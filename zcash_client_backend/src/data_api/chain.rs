use std::fmt::Debug;

use zcash_primitives::{
    block::BlockHash,
    consensus::{self, BlockHeight, NetworkUpgrade},
    merkle_tree::CommitmentTree,
};

use crate::{
    data_api::{
        error::{ChainInvalid, Error},
        BlockSource, WalletWrite,
    },
    proto::compact_formats::CompactBlock,
    wallet::WalletTx,
    welding_rig::scan_block,
};

/// Checks that the scanned blocks in the data database, when combined with the recent
/// `CompactBlock`s in the cache database, form a valid chain.
///
/// This function is built on the core assumption that the information provided in the
/// cache database is more likely to be accurate than the previously-scanned information.
/// This follows from the design (and trust) assumption that the `lightwalletd` server
/// provides accurate block information as of the time it was requested.
///
/// Arguments:
/// - `parameters` Network parameters
/// - `cache` Source of compact blocks
/// - `from_tip` Height & hash of last validated block; if no validation has previously
///    been performed, this will begin scanning from `sapling_activation_height - 1`
///
/// Returns:
/// - `Ok(())` if the combined chain is valid.
/// - `Err(ErrorKind::InvalidChain(upper_bound, cause))` if the combined chain is invalid.
///   `upper_bound` is the height of the highest invalid block (on the assumption that the
///   highest block in the cache database is correct).
/// - `Err(e)` if there was an error during validation unrelated to chain validity.
///
/// This function does not mutate either of the databases.
pub fn validate_chain<N, E, P, C>(
    parameters: &P,
    cache: &C,
    validate_from: Option<(BlockHeight, BlockHash)>,
    chain_network: constants::ChainNetwork
) -> Result<(), E>
where
    E: From<Error<N>>,
    P: consensus::Parameters,
    C: BlockSource<Error = E>,
{
    let sapling_activation_height = parameters
        .activation_height(NetworkUpgrade::Sapling, chain_network)
        .ok_or(Error::SaplingNotActive)?;

    // The cache will contain blocks above the `validate_from` height.  Validate from that maximum
    // height up to the chain tip, returning the hash of the block found in the cache at the
    // `validate_from` height, which can then be used to verify chain integrity by comparing
    // against the `validate_from` hash.
    let from_height = validate_from
        .map(|(height, _)| height)
        .unwrap_or(sapling_activation_height - 1);

    let mut prev_height = from_height;
    let mut prev_hash: Option<BlockHash> = validate_from.map(|(_, hash)| hash);

    cache.with_blocks(from_height, None, move |block| {
        let current_height = block.height();
        let result = if current_height != prev_height + 1 {
            Err(ChainInvalid::block_height_discontinuity(
                prev_height + 1,
                current_height,
            ))
        } else {
            match prev_hash {
                None => Ok(()),
                Some(h) if h == block.prev_hash() => Ok(()),
                Some(_) => Err(ChainInvalid::prev_hash_mismatch(current_height)),
            }
        };

        prev_height = current_height;
        prev_hash = Some(block.hash());
        result.map_err(E::from)
    })
}

pub fn scan_cached_blocks<E, N, P, C, D>(
    params: &P,
    cache: &C,
    data: &mut D,
    limit: Option<u32>,
    chain_network: constants::ChainNetwork
) -> Result<(), E>
where
    P: consensus::Parameters,
    C: BlockSource<Error = E>,
    D: WalletWrite<Error = E, NoteRef = N>,
    N: Copy + Debug,
    E: From<Error<N>>,
{
    let sapling_activation_height = params
        .activation_height(NetworkUpgrade::Sapling, chain_network)
        .ok_or(Error::SaplingNotActive)?;

    // Recall where we synced up to previously.
    // If we have never synced, use sapling activation height to select all cached CompactBlocks.
    let mut last_height = data.block_height_extrema().map(|opt| {
        opt.map(|(_, max)| max)
            .unwrap_or(sapling_activation_height - 1)
    })?;

    // Fetch the ExtendedFullViewingKeys we are tracking
    let extfvks = data.get_extended_full_viewing_keys()?;
    let ivks: Vec<_> = extfvks
        .iter()
        .map(|(a, extfvk)| (*a, extfvk.fvk.vk.ivk()))
        .collect();

    // Get the most recent CommitmentTree
    let mut tree = data
        .get_commitment_tree(last_height)
        .map(|t| t.unwrap_or(CommitmentTree::new()))?;

    // Get most recent incremental witnesses for the notes we are tracking
    let mut witnesses = data.get_witnesses(last_height)?;

    // Get the nullifiers for the notes we are tracking
    let mut nullifiers = data.get_nullifiers()?;

    cache.with_blocks(last_height, limit, |block: CompactBlock| {
        let current_height = block.height();
        // Scanned blocks MUST be height-sequential.
        if current_height != (last_height + 1) {
            return Err(
                ChainInvalid::block_height_discontinuity(last_height + 1, current_height).into(),
            );
        }
        last_height = current_height;

        let block_hash = BlockHash::from_slice(&block.hash);
        let block_time = block.time;

        let txs: Vec<WalletTx> = {
            let mut witness_refs: Vec<_> = witnesses.iter_mut().map(|w| &mut w.1).collect();
            scan_block(
                params,
                block,
                &ivks,
                &nullifiers,
                &mut tree,
                &mut witness_refs[..],
                chain_network
            )
        };

        // Enforce that all roots match. This is slow, so only include in debug builds.
        #[cfg(debug_assertions)]
        {
            let cur_root = tree.root();
            for row in &witnesses {
                if row.1.root() != cur_root {
                    return Err(Error::InvalidWitnessAnchor(row.0, last_height).into());
                }
            }
            for tx in &txs {
                for output in tx.shielded_outputs.iter() {
                    if output.witness.root() != cur_root {
                        return Err(Error::InvalidNewWitnessAnchor(
                            output.index,
                            tx.txid,
                            last_height,
                            output.witness.root(),
                        )
                        .into());
                    }
                }
            }
        }

        // database updates for each block are transactional
        data.transactionally(|up| {
            // Insert the block into the database.
            up.insert_block(current_height, block_hash, block_time, &tree)?;

            for tx in txs {
                let tx_row = up.put_tx_meta(&tx, current_height)?;

                // Mark notes as spent and remove them from the scanning cache
                for spend in &tx.shielded_spends {
                    up.mark_spent(tx_row, &spend.nf)?;
                }

                // remove spent nullifiers from the nullifier set
                nullifiers
                    .retain(|(_, nf)| !tx.shielded_spends.iter().any(|spend| &spend.nf == nf));

                for output in tx.shielded_outputs {
                    if let Some(extfvk) = &extfvks.get(&output.account) {
                        let nf = output
                            .note
                            .nf(&extfvk.fvk.vk, output.witness.position() as u64);

                        let note_id = up.put_received_note(&output, &Some(nf), tx_row)?;

                        // Save witness for note.
                        witnesses.push((note_id, output.witness));

                        // Cache nullifier for note (to detect subsequent spends in this scan).
                        nullifiers.push((output.account, nf));
                    }
                }
            }

            // Insert current witnesses into the database.
            for (note_id, witness) in witnesses.iter() {
                up.insert_witness(*note_id, witness, last_height)?;
            }

            // Prune the stored witnesses (we only expect rollbacks of at most 100 blocks).
            up.prune_witnesses(last_height - 100)?;

            // Update now-expired transactions that didn't get mined.
            up.update_expired_notes(last_height)?;

            Ok(())
        })
    })?;

    Ok(())
}

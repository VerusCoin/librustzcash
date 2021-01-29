//! Consensus logic and parameters.

use std::cmp::{Ord, Ordering};
use std::convert::TryFrom;
use std::fmt;
use std::ops::{Add, Sub};

use crate::constants;

/// A wrapper type representing blockchain heights. Safe conversion from
/// various integer types, as well as addition and subtraction, are provided.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockHeight(u32);

pub const H0: BlockHeight = BlockHeight(0);

impl BlockHeight {
    pub const fn from_u32(v: u32) -> BlockHeight {
        BlockHeight(v)
    }
}

impl fmt::Display for BlockHeight {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl Ord for BlockHeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for BlockHeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<u32> for BlockHeight {
    fn from(value: u32) -> Self {
        BlockHeight(value)
    }
}

impl From<u64> for BlockHeight {
    fn from(value: u64) -> Self {
        BlockHeight(value as u32)
    }
}

impl TryFrom<i32> for BlockHeight {
    type Error = std::num::TryFromIntError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        u32::try_from(value).map(BlockHeight)
    }
}

impl TryFrom<i64> for BlockHeight {
    type Error = std::num::TryFromIntError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        u32::try_from(value).map(BlockHeight)
    }
}

impl From<BlockHeight> for u32 {
    fn from(value: BlockHeight) -> u32 {
        value.0
    }
}

impl From<BlockHeight> for u64 {
    fn from(value: BlockHeight) -> u64 {
        value.0 as u64
    }
}

impl From<BlockHeight> for i64 {
    fn from(value: BlockHeight) -> i64 {
        value.0 as i64
    }
}

impl Add<u32> for BlockHeight {
    type Output = Self;

    fn add(self, other: u32) -> Self {
        BlockHeight(self.0 + other)
    }
}

impl Add for BlockHeight {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self + other.0
    }
}

impl Sub<u32> for BlockHeight {
    type Output = Self;

    fn sub(self, other: u32) -> Self {
        if other > self.0 {
            panic!("Subtraction resulted in negative block height.");
        }

        BlockHeight(self.0 - other)
    }
}

impl Sub for BlockHeight {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self - other.0
    }
}

/// Zcash consensus parameters.
pub trait Parameters: Clone {
    /// Returns the activation height for the overwinter network upgrade on a specified chain
    fn activation_height_overwinter(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for the sapling network upgrade on a specified chain
    fn activation_height_sapling(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for the blossom network upgrade on a specified chain
    fn activation_height_blossom(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for the heartwood network upgrade on a specified chain
    fn activation_height_heartwood(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for the canopy network upgrade on a specified chain
    fn activation_height_canopy(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for the zfuture network upgrade on a specified chain
    fn activation_height_zfuture(&self, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the activation height for a particular network upgrade,
    /// if an activation height has been set.
    fn activation_height(&self, nu: NetworkUpgrade, chain: constants::ChainNetwork) -> Option<BlockHeight>;

    /// Returns the human-readable prefix for Sapling extended full
    /// viewing keys for the network to which this Parameters value applies.
    fn hrp_sapling_extended_full_viewing_key(&self) -> &str;

    /// Returns the human-readable prefix for Sapling payment addresses
    /// viewing keys for the network to which this Parameters value applies.
    fn hrp_sapling_payment_address(&self) -> &str;

    /// Returns the human-readable prefix for transparent pay-to-public-key-hash
    /// payment addresses for the network to which this Parameters value applies.
    fn b58_pubkey_address_prefix(&self) -> [u8; 2];

    /// Returns the human-readable prefix for transparent pay-to-script-hash
    /// payment addresses for the network to which this Parameters value applies.
    fn b58_script_address_prefix(&self) -> [u8; 2];

    /// Determines whether the specified network upgrade is active as of the
    /// provided block height on the network to which this Parameters value applies.
    fn is_nu_active(&self, nu: NetworkUpgrade, height: BlockHeight, chain: constants::ChainNetwork) -> bool {
        self.activation_height(nu, chain).map_or(false, |h| h <= height)
    }
}

/// Marker struct for the production network.
#[derive(PartialEq, Copy, Clone, Debug)]
pub struct MainNetwork;

pub const MAIN_NETWORK: MainNetwork = MainNetwork;

impl Parameters for MainNetwork {
    /// Returns the activation height for the overwinter network upgrade on a specified chain
    fn activation_height_overwinter(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(0)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(347_500))
        }
    }

    /// Returns the activation height for the sapling network upgrade on a specified chain
    fn activation_height_sapling(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(227_520)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(419_200))
        }
    }

    /// Returns the activation height for the blossom network upgrade on a specified chain
    fn activation_height_blossom(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(653_600))
        }
    }

    /// Returns the activation height for the heartwood network upgrade on a specified chain
    fn activation_height_heartwood(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(903_000))
        }
    }

    /// Returns the activation height for the canopy network upgrade on a specified chain
    fn activation_height_canopy(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(1_046_400))
        }
    }

    /// Returns the activation height for the zfuture network upgrade on a specified chain
    fn activation_height_zfuture(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => None
        }
    }

    fn activation_height(&self, nu: NetworkUpgrade, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match nu {
            NetworkUpgrade::Overwinter => self.activation_height_overwinter(chain),
            NetworkUpgrade::Sapling => self.activation_height_sapling(chain),
            NetworkUpgrade::Blossom => self.activation_height_blossom(chain),
            NetworkUpgrade::Heartwood => self.activation_height_heartwood(chain),
            NetworkUpgrade::Canopy => self.activation_height_canopy(chain),
            #[cfg(feature = "zfuture")]
            NetworkUpgrade::ZFuture => self.activation_height_zfuture(chain),
        }
    }

    fn hrp_sapling_extended_full_viewing_key(&self) -> &str {
        constants::mainnet::HRP_SAPLING_EXTENDED_FULL_VIEWING_KEY
    }

    fn hrp_sapling_payment_address(&self) -> &str {
        constants::mainnet::HRP_SAPLING_PAYMENT_ADDRESS
    }

    fn b58_pubkey_address_prefix(&self) -> [u8; 2] {
        constants::mainnet::B58_PUBKEY_ADDRESS_PREFIX
    }

    fn b58_script_address_prefix(&self) -> [u8; 2] {
        constants::mainnet::B58_SCRIPT_ADDRESS_PREFIX
    }
}

/// Marker struct for the test network.
#[derive(PartialEq, Copy, Clone, Debug)]
pub struct TestNetwork;

pub const TEST_NETWORK: TestNetwork = TestNetwork;

impl Parameters for TestNetwork {
    /// Returns the activation height for the overwinter network upgrade on a specified chain
    fn activation_height_overwinter(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(0)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(207_500))
        }
    }

    /// Returns the activation height for the sapling network upgrade on a specified chain
    fn activation_height_sapling(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(227_520)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(280_000))
        }
    }

    /// Returns the activation height for the blossom network upgrade on a specified chain
    fn activation_height_blossom(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(584_000))
        }
    }

    /// Returns the activation height for the heartwood network upgrade on a specified chain
    fn activation_height_heartwood(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(903_800))
        }
    }

    /// Returns the activation height for the canopy network upgrade on a specified chain
    fn activation_height_canopy(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => Some(BlockHeight(1_028_500))
        }
    }

    /// Returns the activation height for the zfuture network upgrade on a specified chain
    fn activation_height_zfuture(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match chain {
            constants::ChainNetwork::VRSC => Some(BlockHeight(u32::MAX)),
            constants::ChainNetwork::ZEC => None
        }
    }
    
    fn activation_height(&self, nu: NetworkUpgrade, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match nu {
            NetworkUpgrade::Overwinter => self.activation_height_overwinter(chain),
            NetworkUpgrade::Sapling => self.activation_height_sapling(chain),
            NetworkUpgrade::Blossom => self.activation_height_blossom(chain),
            NetworkUpgrade::Heartwood => self.activation_height_heartwood(chain),
            NetworkUpgrade::Canopy => self.activation_height_canopy(chain),
            #[cfg(feature = "zfuture")]
            NetworkUpgrade::ZFuture => self.activation_height_zfuture(chain),
        }
    }

    fn hrp_sapling_extended_full_viewing_key(&self) -> &str {
        constants::testnet::HRP_SAPLING_EXTENDED_FULL_VIEWING_KEY
    }

    fn hrp_sapling_payment_address(&self) -> &str {
        constants::testnet::HRP_SAPLING_PAYMENT_ADDRESS
    }

    fn b58_pubkey_address_prefix(&self) -> [u8; 2] {
        constants::testnet::B58_PUBKEY_ADDRESS_PREFIX
    }

    fn b58_script_address_prefix(&self) -> [u8; 2] {
        constants::testnet::B58_SCRIPT_ADDRESS_PREFIX
    }
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Network {
    MainNetwork,
    TestNetwork,
}

impl Parameters for Network {
    fn activation_height_overwinter(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_overwinter(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_overwinter(chain),
        }
    }

    fn activation_height_sapling(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_sapling(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_sapling(chain),
        }
    }

    fn activation_height_blossom(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_blossom(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_blossom(chain),
        }
    }

    fn activation_height_heartwood(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_heartwood(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_heartwood(chain),
        }
    }

    fn activation_height_canopy(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_canopy(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_canopy(chain),
        }
    }

    fn activation_height_zfuture(&self, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height_zfuture(chain),
            Network::TestNetwork => TEST_NETWORK.activation_height_zfuture(chain),
        }
    }

    fn activation_height(&self, nu: NetworkUpgrade, chain: constants::ChainNetwork) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height(nu, chain),
            Network::TestNetwork => TEST_NETWORK.activation_height(nu, chain),
        }
    }

    fn hrp_sapling_extended_full_viewing_key(&self) -> &str {
        match self {
            Network::MainNetwork => MAIN_NETWORK.hrp_sapling_extended_full_viewing_key(),
            Network::TestNetwork => TEST_NETWORK.hrp_sapling_extended_full_viewing_key(),
        }
    }

    fn hrp_sapling_payment_address(&self) -> &str {
        match self {
            Network::MainNetwork => MAIN_NETWORK.hrp_sapling_payment_address(),
            Network::TestNetwork => TEST_NETWORK.hrp_sapling_payment_address(),
        }
    }

    fn b58_pubkey_address_prefix(&self) -> [u8; 2] {
        match self {
            Network::MainNetwork => MAIN_NETWORK.b58_pubkey_address_prefix(),
            Network::TestNetwork => TEST_NETWORK.b58_pubkey_address_prefix(),
        }
    }

    fn b58_script_address_prefix(&self) -> [u8; 2] {
        match self {
            Network::MainNetwork => MAIN_NETWORK.b58_script_address_prefix(),
            Network::TestNetwork => TEST_NETWORK.b58_script_address_prefix(),
        }
    }
}

/// An event that occurs at a specified height on the Zcash chain, at which point the
/// consensus rules enforced by the network are altered.
///
/// See [ZIP 200](https://zips.z.cash/zip-0200) for more details.
#[derive(Clone, Copy, Debug)]
pub enum NetworkUpgrade {
    /// The [Overwinter] network upgrade.
    ///
    /// [Overwinter]: https://z.cash/upgrade/overwinter/
    Overwinter,
    /// The [Sapling] network upgrade.
    ///
    /// [Sapling]: https://z.cash/upgrade/sapling/
    Sapling,
    /// The [Blossom] network upgrade.
    ///
    /// [Blossom]: https://z.cash/upgrade/blossom/
    Blossom,
    /// The [Heartwood] network upgrade.
    ///
    /// [Heartwood]: https://z.cash/upgrade/heartwood/
    Heartwood,
    /// The [Canopy] network upgrade.
    ///
    /// [Canopy]: https://z.cash/upgrade/canopy/
    Canopy,
    /// The [ZFUTURE] network upgrade.
    ///
    /// This upgrade is expected never to activate on mainnet;
    /// it is intended for use in integration testing of functionality
    /// that is a candidate for integration in a future network upgrade.
    #[cfg(feature = "zfuture")]
    ZFuture,
}

impl fmt::Display for NetworkUpgrade {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NetworkUpgrade::Overwinter => write!(f, "Overwinter"),
            NetworkUpgrade::Sapling => write!(f, "Sapling"),
            NetworkUpgrade::Blossom => write!(f, "Blossom"),
            NetworkUpgrade::Heartwood => write!(f, "Heartwood"),
            NetworkUpgrade::Canopy => write!(f, "Canopy"),
            #[cfg(feature = "zfuture")]
            NetworkUpgrade::ZFuture => write!(f, "ZFUTURE"),
        }
    }
}

impl NetworkUpgrade {
    fn branch_id(self) -> BranchId {
        match self {
            NetworkUpgrade::Overwinter => BranchId::Overwinter,
            NetworkUpgrade::Sapling => BranchId::Sapling,
            NetworkUpgrade::Blossom => BranchId::Blossom,
            NetworkUpgrade::Heartwood => BranchId::Heartwood,
            NetworkUpgrade::Canopy => BranchId::Canopy,
            #[cfg(feature = "zfuture")]
            NetworkUpgrade::ZFuture => BranchId::ZFuture,
        }
    }
}

/// The network upgrades on the Zcash chain in order of activation.
///
/// This order corresponds to the activation heights, but because Rust enums are
/// full-fledged algebraic data types, we need to define it manually.
const UPGRADES_IN_ORDER: &[NetworkUpgrade] = &[
    NetworkUpgrade::Overwinter,
    NetworkUpgrade::Sapling,
    NetworkUpgrade::Blossom,
    NetworkUpgrade::Heartwood,
    NetworkUpgrade::Canopy,
];

pub const ZIP212_GRACE_PERIOD: u32 = 32256;

/// A globally-unique identifier for a set of consensus rules within the Zcash chain.
///
/// Each branch ID in this enum corresponds to one of the epochs between a pair of Zcash
/// network upgrades. For example, `BranchId::Overwinter` corresponds to the blocks
/// starting at Overwinter activation, and ending the block before Sapling activation.
///
/// The main use of the branch ID is in signature generation: transactions commit to a
/// specific branch ID by including it as part of [`signature_hash`]. This ensures
/// two-way replay protection for transactions across network upgrades.
///
/// See [ZIP 200](https://zips.z.cash/zip-0200) for more details.
///
/// [`signature_hash`]: crate::transaction::signature_hash
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BranchId {
    /// The consensus rules at the launch of Zcash.
    Sprout,
    /// The consensus rules deployed by [`NetworkUpgrade::Overwinter`].
    Overwinter,
    /// The consensus rules deployed by [`NetworkUpgrade::Sapling`].
    Sapling,
    /// The consensus rules deployed by [`NetworkUpgrade::Blossom`].
    Blossom,
    /// The consensus rules deployed by [`NetworkUpgrade::Heartwood`].
    Heartwood,
    /// The consensus rules deployed by [`NetworkUpgrade::Canopy`].
    Canopy,
    /// Candidates for future consensus rules; this branch will never
    /// activate on mainnet.
    #[cfg(feature = "zfuture")]
    ZFuture,
}

impl TryFrom<u32> for BranchId {
    type Error = &'static str;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(BranchId::Sprout),
            0x5ba8_1b19 => Ok(BranchId::Overwinter),
            0x76b8_09bb => Ok(BranchId::Sapling),
            0x2bb4_0e60 => Ok(BranchId::Blossom),
            0xf5b9_230b => Ok(BranchId::Heartwood),
            0xe9ff_75a6 => Ok(BranchId::Canopy),
            #[cfg(feature = "zfuture")]
            0xffff_ffff => Ok(BranchId::ZFuture),
            _ => Err("Unknown consensus branch ID"),
        }
    }
}

impl From<BranchId> for u32 {
    fn from(consensus_branch_id: BranchId) -> u32 {
        match consensus_branch_id {
            BranchId::Sprout => 0,
            BranchId::Overwinter => 0x5ba8_1b19,
            BranchId::Sapling => 0x76b8_09bb,
            BranchId::Blossom => 0x2bb4_0e60,
            BranchId::Heartwood => 0xf5b9_230b,
            BranchId::Canopy => 0xe9ff_75a6,
            #[cfg(feature = "zfuture")]
            BranchId::ZFuture => 0xffff_ffff,
        }
    }
}

impl BranchId {
    /// Returns the branch ID corresponding to the consensus rule set that is active at
    /// the given height.
    ///
    /// This is the branch ID that should be used when creating transactions.
    pub fn for_height<P: Parameters>(parameters: &P, height: BlockHeight, chain: constants::ChainNetwork) -> Self {
        for nu in UPGRADES_IN_ORDER.iter().rev() {
            if parameters.is_nu_active(*nu, height, chain) {
                return nu.branch_id();
            }
        }

        // Sprout rules apply before any network upgrade
        BranchId::Sprout
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use super::{
        BlockHeight, BranchId, NetworkUpgrade, Parameters, MAIN_NETWORK, UPGRADES_IN_ORDER, constants
    };

    #[test]
    fn nu_ordering() {
        for i in 1..UPGRADES_IN_ORDER.len() {
            let nu_a = UPGRADES_IN_ORDER[i - 1];
            let nu_b = UPGRADES_IN_ORDER[i];
            match (
                MAIN_NETWORK.activation_height(nu_a, constants::ChainNetwork::ZEC),
                MAIN_NETWORK.activation_height(nu_b, constants::ChainNetwork::ZEC),
            ) {
                (a, b) if a < b => (),
                _ => panic!(
                    "{} should not be before {} in UPGRADES_IN_ORDER",
                    nu_a, nu_b
                ),
            }
        }
    }

    #[test]
    fn nu_is_active() {
        assert!(!MAIN_NETWORK.is_nu_active(NetworkUpgrade::Overwinter, BlockHeight(0), constants::ChainNetwork::ZEC));
        assert!(!MAIN_NETWORK.is_nu_active(NetworkUpgrade::Overwinter, BlockHeight(347_499), constants::ChainNetwork::ZEC));
        assert!(MAIN_NETWORK.is_nu_active(NetworkUpgrade::Overwinter, BlockHeight(347_500), constants::ChainNetwork::ZEC));
    }

    #[test]
    fn branch_id_from_u32() {
        assert_eq!(BranchId::try_from(0), Ok(BranchId::Sprout));
        assert!(BranchId::try_from(1).is_err());
    }

    #[test]
    fn branch_id_for_height() {
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(0), constants::ChainNetwork::ZEC),
            BranchId::Sprout,
        );
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(419_199), constants::ChainNetwork::ZEC),
            BranchId::Overwinter,
        );
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(419_200), constants::ChainNetwork::ZEC),
            BranchId::Sapling,
        );
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(903_000), constants::ChainNetwork::ZEC),
            BranchId::Heartwood,
        );
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(1_046_400), constants::ChainNetwork::ZEC),
            BranchId::Canopy,
        );
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(5_000_000), constants::ChainNetwork::ZEC),
            BranchId::Canopy,
        );
    }
}

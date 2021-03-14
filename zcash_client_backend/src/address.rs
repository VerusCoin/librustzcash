//! Structs for handling supported address types.

use zcash_primitives::{consensus, legacy::TransparentAddress, primitives::PaymentAddress, constants::{ChainNetwork}};

use crate::encoding::{
    decode_payment_address, decode_transparent_address, encode_payment_address,
    encode_transparent_address,
};

/// An address that funds can be sent to.
#[derive(Debug, PartialEq, Clone)]
pub enum RecipientAddress {
    Shielded(PaymentAddress),
    Transparent(TransparentAddress),
}

impl From<PaymentAddress> for RecipientAddress {
    fn from(addr: PaymentAddress) -> Self {
        RecipientAddress::Shielded(addr)
    }
}

impl From<TransparentAddress> for RecipientAddress {
    fn from(addr: TransparentAddress) -> Self {
        RecipientAddress::Transparent(addr)
    }
}

impl RecipientAddress {
    pub fn decode<P: consensus::Parameters>(params: &P, s: &str, chain_network: ChainNetwork) -> Option<Self> {
        if let Ok(Some(pa)) = decode_payment_address(params.hrp_sapling_payment_address(chain_network), s) {
            Some(pa.into())
        } else if let Ok(Some(addr)) = decode_transparent_address(
            params.b58_pubkey_address_prefix(chain_network),
            params.b58_script_address_prefix(chain_network),
            s,
        ) {
            Some(addr.into())
        } else {
            None
        }
    }

    pub fn encode<P: consensus::Parameters>(&self, params: &P, chain_network: ChainNetwork) -> String {
        match self {
            RecipientAddress::Shielded(pa) => {
                encode_payment_address(params.hrp_sapling_payment_address(chain_network), pa)
            }
            RecipientAddress::Transparent(addr) => encode_transparent_address(
                params.b58_pubkey_address_prefix(chain_network),
                params.b58_script_address_prefix(chain_network),
                addr,
            ),
        }
    }
}

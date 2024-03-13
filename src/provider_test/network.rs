use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
// #[cfg_attr(feature = "clap", circuit_derive(clap::ValueEnum))]
pub enum Network {
    EthereumMainnet = 1,
    EthereumSepolia = 11155111,
}

use crate::provider_test::network::Network;
use ethers::providers::{Http, Provider, RetryClient};

pub fn get_provider(network: &Network) -> Provider<RetryClient<Http>> {
    let provider_url = match network {
        Network::EthereumMainnet => {
            "https://eth-mainnet.g.alchemy.com/v2/d44QMqZOM_4Wh1nKjfEyakdE6tDjBo1k"
        }
        Network::EthereumSepolia => {
            "https://eth-sepolia.g.alchemy.com/v2/6sHdA14duhUT9RA9LjWRH7CHJNjsZkS8"
        }
    };
    let provider =
        Provider::new_client(provider_url, 10, 1).expect("could not instantiate HTTP Provider");
    provider
}

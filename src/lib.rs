use log::LevelFilter;

extern crate alloc;
extern crate core;
extern crate proc_macro;

pub mod ecdsa;
pub mod hash;
pub mod mpt;
pub mod nonnative;
pub mod poseidon;
pub mod smt;
pub mod types;
pub mod u32;
pub mod zkaa;
pub mod zkdsa;

// eth
mod storage;

pub fn profiling_enable() {
    let mut builder = env_logger::Builder::from_default_env();
    builder.format_timestamp(None);
    builder.filter_level(LevelFilter::Trace);
    builder.try_init().unwrap();
}

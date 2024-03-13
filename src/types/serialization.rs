use crate::types::bytes::{ByteTarget, Bytes32Target};
use itertools::Itertools;
use plonky2::iop::target::BoolTarget;
use plonky2::util::serialization::{Buffer, IoResult, Read};

pub trait ReadBytes {
    fn read_byte_target(&mut self) -> IoResult<ByteTarget>;
    fn read_byte32_target(&mut self) -> IoResult<Bytes32Target>;
}

impl ReadBytes for Buffer<'_> {
    #[inline]
    fn read_byte_target(&mut self) -> IoResult<ByteTarget> {
        let targets = self.read_target_vec()?;
        let bools = targets
            .into_iter()
            .map(|t| BoolTarget::new_unsafe(t))
            .collect_vec();
        Ok(ByteTarget::from_elements(bools))
    }
    #[inline]
    fn read_byte32_target(&mut self) -> IoResult<Bytes32Target> {
        let targets = self.read_target_vec()?;
        let bools = targets
            .into_iter()
            .map(|t| BoolTarget::new_unsafe(t))
            .collect_vec();
        Ok(Bytes32Target::from_elements(bools))
    }
}

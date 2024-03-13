use crate::types::bytes::{ByteTarget, Bytes32Target};
use plonky2::util::serialization::{Buffer, IoResult, Read};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use plonky2_u32::serialization::ReadU32;

pub trait ReadBytes {
    fn read_byte_target(&mut self) -> IoResult<ByteTarget>;
    fn read_byte32_target(&mut self) -> IoResult<Bytes32Target>;
}

impl ReadBytes for Buffer<'_> {
    #[inline]
    fn read_byte_target(&mut self) -> IoResult<ByteTarget> {
        let targets = self.read_target_vec()?;
        //ByteTarget::from_target(targets);
        todo!()
    }
    #[inline]
    fn read_byte32_target(&mut self) -> IoResult<Bytes32Target> {
        todo!()
    }
    // #[inline]
    // fn read_target_u32(&mut self) -> IoResult<U32Target> {
    //     Ok(U32Target(self.read_target()?))
    // }
}

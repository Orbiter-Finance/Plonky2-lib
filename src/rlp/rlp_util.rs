use std::ops::Range;

#[derive(Clone, Debug)]
pub struct RlpFieldParser {
    data: Vec<u8>,
}

pub const RLP_LITERRAL_MAX_VALUE: usize = 127;
pub const RLP_FIELD_SHORT_TYPE_PREFIX_MAX: usize = 183; // len <= 55 bytes
pub const RLP_FIELD_SHORT_TYPE_MAX_LEN: usize = 55;

impl RlpFieldParser {
    pub fn new(data: Vec<u8>) -> Self {
        RlpFieldParser { data }
    }

    pub fn is_not_literal(&self) -> bool {
        self.data.len() > 0 && self.data[0] > RLP_LITERRAL_MAX_VALUE as u8
    }

    pub fn is_long_field(&self) -> bool {
        self.data.len() > 1 && self.data[0] > RLP_FIELD_SHORT_TYPE_PREFIX_MAX as u8
    }

    pub fn is_short_field(&self) -> bool {
        self.is_not_literal() && self.data.len() > 1 && self.data[0] <= RLP_FIELD_SHORT_TYPE_PREFIX_MAX as u8
    }

    pub fn parse_rlp_long_field_len_cells_len(&mut self) -> usize {
        assert!(!self.is_not_literal());
        let len = self.data.len() - 1;
        if len > RLP_FIELD_SHORT_TYPE_MAX_LEN {
            (self.data[0] - RLP_FIELD_SHORT_TYPE_PREFIX_MAX as u8) as usize
        } else {
            0
        }
    }

    pub fn parse_rlp_long_field_len_len(&mut self) -> usize {
        assert!(!self.is_not_literal());
        let mut len_len = 0;
        let len = self.data.len() - 1;
        if len > RLP_FIELD_SHORT_TYPE_MAX_LEN {
            let len_cells_len = self.parse_rlp_long_field_len_cells_len();
            let len_ceslls = &self.data[1..1 + len_cells_len];
            for i in 0..len_cells_len {
                len_len = len_len << 8 | len_ceslls[i] as usize;
            }
        }
        len_len
    }

    pub fn parse_rlp_long_field_index_range(&mut self) -> Range<usize> {
        assert!(!self.is_not_literal());
        let len_cells_len = self.parse_rlp_long_field_len_cells_len();
        let len_len = self.parse_rlp_long_field_len_len();
        assert!(len_cells_len + len_len + 1 <= self.data.len());
        Range {
            start: 1 + len_cells_len,
            end: 1 + len_cells_len + len_len,
        }
    }
}

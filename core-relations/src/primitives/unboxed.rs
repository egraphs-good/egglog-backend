//! Special handling for small integer types to avoid lookups in an [`InternTable`].
//!
//!
//! [`InternTable`]: crate::common::InternTable

use numeric_id::NumericId;

use crate::{common::InternTable, Value};

use super::Primitive;

trait UnboxedPrimitive: Primitive {
    fn try_unbox(val: Value) -> Option<Self>
    where
        Self: Sized;
}

macro_rules! impl_small_primitive {
    ($ty:ty) => {
        impl UnboxedPrimitive for $ty {
            fn try_unbox(val: Value) -> Option<Self> {
                Some(val.rep() as $ty)
            }
        }
    };
    ($ty:ty, $($rest:ty),+) => {
        impl_small_primitive!($ty);
        impl_small_primitive!($($rest),+);
    };
}

impl_small_primitive!(u8, u16, u32, i8, i16, i32);

impl UnboxedPrimitive for bool {
    fn try_unbox(val: Value) -> Option<Self> {
        Some(val.rep() != 0)
    }
}

const VAL_BITS: u32 = std::mem::size_of::<Value>() as u32 * 8;
const VAL_MASK: u32 = 1 << (VAL_BITS - 1);

macro_rules! impl_medium_primitive {
    ($ty:ty) => {
        impl UnboxedPrimitive for $ty {
            fn try_unbox(val: Value) -> Option<Self> {
                let top_bit_clear = val.rep() & VAL_MASK == 0;
                if top_bit_clear {
                    Some(val.rep() as $ty)
                } else {
                    // If the top bit is set, look this up in an intern table.
                    None
                }
            }
        }
    };

    ($ty:ty, $($rest:ty),+) => {
        impl_medium_primitive!($ty);
        impl_medium_primitive!($($rest),+);
    };
}

impl_medium_primitive!(u64, i64);

pub(super) struct UnboxedInternTable<K, V> {
    pub(crate) table: InternTable<K, V>,
}

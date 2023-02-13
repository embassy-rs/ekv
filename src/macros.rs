#![macro_use]

macro_rules! impl_bytes {
    ($t:ident) => {
        impl $t {
            #[allow(unused)]
            pub(crate) const SIZE: usize = core::mem::size_of::<Self>();

            #[allow(unused)]
            #[inline(always)]
            pub(crate) fn to_bytes(self) -> [u8; Self::SIZE] {
                unsafe { core::mem::transmute(self) }
            }

            #[allow(unused)]
            #[inline(always)]
            pub(crate) fn from_bytes(bytes: [u8; Self::SIZE]) -> Self {
                unsafe { core::mem::transmute(bytes) }
            }
        }
    };
}

#[cfg(not(feature = "_panic-on-corrupted"))]
macro_rules! corrupted {
    () => {
        return Err(crate::errors::CorruptedError.into())
    };
}

#[cfg(feature = "_panic-on-corrupted")]
macro_rules! corrupted {
    () => {
        panic!("corrupted")
    };
}

macro_rules! check_corrupted {
    ($e:expr) => {
        match $e {
            Ok(x) => x,
            Err(_) => {
                corrupted!();
            }
        }
    };
}

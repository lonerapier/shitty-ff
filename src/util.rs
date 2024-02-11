use crate::goldilocks::{Goldilocks, P};
pub const fn reduce_64(mut x: u64) -> u64 {
    if x >= P {
        x -= P;
    }
    x
}

/// Reduce a 128 bit value to 64 bit value.
/// copied from [Plonky3](https://github.com/Plonky3/Plonky3/blob/main/goldilocks/src/lib.rs#L365)'s Goldilocks impl.
pub fn reduce_128(x: u128) -> Goldilocks {
    let (n0n1, n2n3) = (x as u64, (x >> 64) as u64);
    let n3 = n2n3 >> 32;

    let n2 = n2n3 as u32;

    let n0n1 = if n0n1 >= n3 {
        n0n1.wrapping_sub(n3)
    } else {
        n0n1.wrapping_sub(n3).wrapping_add(P)
    };

    let med_shift: u64 = ((n2 as u64) << 32).wrapping_sub(n2 as u64);

    let ret = n0n1.wrapping_add(med_shift);
    if ret >= P || ret < med_shift {
        Goldilocks {
            value: ret.wrapping_sub(P),
        }
    } else {
        Goldilocks { value: ret }
    }
}

use super::{D, Q};

/// Decomposes r into (r1, r0) such that r = r1*2^d + r0 (mod Q)
pub const fn power2round(mut r: i32) -> (i32, i32) {
    r += (r >> 31) & Q;

    let q = (1 << (D - 1)) - 1;

    let r1 = (r + q) >> D;
    let r0 = r - (r1 << D);

    (r1, r0)
}

/// Convert 3 bytes into an element of Z_Q.
pub const fn from_three_bytes(b0: u8, b1: u8, b2: u8) -> Option<i32> {
    let mut z = b0 as u32;
    z |= (b1 as u32) << 8;
    z |= (b2 as u32) << 16;
    z &= 0x7FFFFF;

    if z < Q as u32 {
        return Some(z as i32);
    }

    None
}

const fn mod5(a: u32) -> i32 {
    const DIV_SHIFT: usize = 10;
    const M: u32 = ((1 << DIV_SHIFT) + 3) / 5;
    (a - ((a * M) >> DIV_SHIFT) * 5) as i32
}

/// Convert two half-bytes into two elements of Z_Q.
pub const fn from_halfbytes<const ETA: usize>(b: u8) -> (Option<i32>, Option<i32>) {
    let b0 = (b & 0xF) as u32;
    let b1 = (b >> 4) as u32;

    match ETA {
        2 => (
            if b0 < 15 { Some(2 - mod5(b0)) } else { None },
            if b1 < 15 { Some(2 - mod5(b1)) } else { None },
        ),
        4 => (
            if b0 < 9 { Some(4 - b0 as i32) } else { None },
            if b1 < 9 { Some(4 - b1 as i32) } else { None },
        ),
        _ => unreachable!(),
    }
}

pub const fn decompose_32(mut r: i32) -> (i32, i32) {
    const GAMMA2: i32 = (Q - 1) / 32;
    const M: i32 = ((1 << 28) / (GAMMA2 as i64)) as i32;
    const R1_MAX: i32 = (Q - 1) / (2 * GAMMA2);

    r += (r >> 31) & Q;

    let mut r1 = (r + 255) >> 8;
    r1 = (r1 * M + (1 << 20)) >> 21;
    r1 &= R1_MAX - 1;

    let mut r0 = r - r1 * 2 * GAMMA2;
    r0 -= (((Q - 1) / 2 - r0) >> 31) & Q;

    (r1, r0)
}

pub const fn decompose_88(mut r: i32) -> (i32, i32) {
    const GAMMA2: i32 = (Q - 1) / 88;
    const M: i32 = ((1 << 30) / (GAMMA2 as i64)) as i32;
    const R1_MAX: i32 = (Q - 1) / (2 * GAMMA2);

    r += (r >> 31) & Q;

    let mut r1 = (r + 255) >> 8;
    r1 = (r1 * M + (1 << 22)) >> 23;
    r1 ^= ((R1_MAX - 1 - r1) >> 31) & r1;

    let mut r0 = r - r1 * 2 * GAMMA2;
    r0 -= (((Q - 1) / 2 - r0) >> 31) & Q;

    (r1, r0)
}

pub const fn use_hint_88(h: usize, r: i32) -> i32 {
    let (mut r1, r0) = decompose_88(r);

    if h == 0 {
        return r1;
    }

    r1 += 1 - (((r0 >> 31) & 1) << 1);
    r1 -= ((r1 + (1 << 5)) >> 6) * 44;
    r1 + ((r1 >> 31) & 44)
}

pub const fn use_hint_32(h: usize, r: i32) -> i32 {
    let (r1, r0) = decompose_32(r);

    if h == 0 {
        return r1;
    }

    if r0 > 0 {
        (r1 + 1) & 15
    } else {
        (r1 - 1) & 15
    }
}

pub const fn make_hint<const G2: i32>(z: i32, r: i32) -> i32 {
    (z > G2 || z < -G2 || (z == -G2 && r != 0)) as i32
}

pub const fn norm(w: i32) -> usize {
    (w - ((w >> 31) & (w << 1))) as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decomp32() {
        for i in 0..Q {
            let mut r0_prime = i % (261888 * 2);
            if r0_prime > 261888 {
                r0_prime -= 261888 * 2;
            }
            let (r1, r0) = decompose_32(i);

            if i - r0_prime == Q - 1 {
                r0_prime -= 1;
                assert_eq!(r0, r0_prime);
                assert_eq!(r1, 0);
            } else {
                assert_eq!(r0, r0_prime);
                assert_eq!(r1, (i - r0_prime) / (2 * 261888));
            }
        }
    }

    #[test]
    fn test_decomp88() {
        for i in 0..Q {
            let mut r0_prime = i % (95232 * 2);
            if r0_prime > 95232 {
                r0_prime -= 95232 * 2;
            }
            let (r1, r0) = decompose_88(i);

            if i - r0_prime == Q - 1 {
                r0_prime -= 1;
                assert_eq!(r0, r0_prime);
                assert_eq!(r1, 0);
            } else {
                assert_eq!(r0, r0_prime);
                assert_eq!(r1, (i - r0_prime) / (2 * 95232));
            }
        }
    }
}

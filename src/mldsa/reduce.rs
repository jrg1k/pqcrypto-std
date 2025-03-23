//! Reductions mod [`Q`]

use super::Q;

// R = 2^32
pub const R_MOD_Q: i32 = -4186625; // 2^32 mod Q
const R2_MOD_Q: i32 = 2365951; // (2^32)^2 mod Q
const QINV: i32 = 58728449; // Q^-1 mod 2^32

/// a -> aR^-1 (mod Q)
pub const fn redc(a: i64) -> i32 {
    let m = (a as i32).wrapping_mul(QINV) as i64;

    let mq = m * (Q as i64);

    // t = (a - mQ) / R
    let t = (a - mq) >> 32;

    t as i32
}

/// ab -> abR^-1 (mod Q)
pub const fn mont_mul(a: i32, b: i32) -> i32 {
    redc(a as i64 * b as i64)
}

/// a -> aR (mod Q)
pub const fn to_mont(a: i32) -> i32 {
    mont_mul(R2_MOD_Q, a)
}

/// a -> a (mod Q)
pub const fn barrett_reduce(a: i32) -> i32 {
    // M = 2^23 / Q = 1
    let q = (a + (1 << (22))) >> 23;

    a - (q * Q)
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;
    #[test]
    fn test_barret_reduce() {
        for _ in 0..10000 {
            let n: i32 = rand::rng().random();
            let n = n % (1 << 24);
            let n_modq = n.wrapping_rem(Q);
            let n_breduced = barrett_reduce(n);
            assert!(n_breduced < (Q) && n_breduced > -(Q));
            assert!(
                n_modq == n_breduced
                    || n_modq - Q == n_breduced
                    || n_modq + Q == n_breduced
            );
        }
    }

    #[test]
    fn test_montgomery_reduce() {
        let a = to_mont(15);
        let b = to_mont(17);
        let c = to_mont(-25);
        let d = to_mont(-634);

        let x = mont_mul(a, b);
        let x = mont_mul(x, c);
        let x = mont_mul(x, d);
        assert_eq!(4041750, redc(x as i64));

        let x = to_mont(8) + to_mont(8);
        assert_eq!(16, redc(x as i64));
    }
}

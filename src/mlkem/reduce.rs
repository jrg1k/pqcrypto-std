use crate::mlkem::Q;

pub const R_MOD_Q: i32 = -1044; // 2^16 mod Q
pub const R2_MOD_Q: i32 = 1353; // (2^16)^2 mod Q
pub const QINV: i32 = -3327; // Q^-1 mod 2^16

/// map a -> aR^{-1} (mod Q)
pub const fn redc(a: i32) -> i16 {
    // m = (a (mod 2^16))Q^{-1} (mod 2^16)
    let m = (a as i16).wrapping_mul(QINV as i16) as i32;

    let mq = m * (Q as i32);

    // t = (a - mQ) / R
    let t = (a - mq) >> 16;

    t as i16
}

/// map ab -> abR^{-1} (mod Q)
pub const fn mont_mul(a: i16, b: i16) -> i16 {
    redc(a as i32 * b as i32)
}

/// map a -> aR (mod Q)
pub const fn to_mont(a: i16) -> i16 {
    redc(R2_MOD_Q * a as i32)
}

/// map a -> a (mod Q)
pub const fn barrett_reduce(a: i16) -> i16 {
    const M: i32 = (1 << 26) / Q as i32;

    let a = a as i32;
    let q = (a * M + (1 << 25)) >> 26;

    (a - (q * Q as i32)) as i16
}

#[test]
fn test_barret_reduce() {
    for n in i16::MIN..i16::MAX {
        let n_modq = n.wrapping_rem(Q);
        let n_breduced = barrett_reduce(n);
        assert!(n_breduced < 3329 && n_breduced > -3329);
        assert!(n_modq == n_breduced || n_modq - Q == n_breduced || n_modq + Q == n_breduced);
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
    assert_eq!(344, redc(x as i32));

    let x = to_mont(8) + to_mont(8);
    assert_eq!(16, redc(x as i32));
}

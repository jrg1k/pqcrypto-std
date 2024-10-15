use crate::kyber::Q;

const Q_HALF: i32 = (Q as i32 + 1) / 2;

/// round(2^n / Q)
const fn power_div_q(n: usize) -> i64 {
    ((1 << n) + Q_HALF as i64) / Q as i64
}

/// x -> round((2^4 / Q) * x) (mod 2^4)
pub const fn compr_4bit(x: i16) -> u8 {
    const M: i32 = power_div_q(16 + 4) as i32;

    let a = M * x as i32;
    let div = (a + (1 << 15)) >> 16;

    (div & 0xF) as u8
}

/// y -> round((q/2^4) * y)
pub const fn decompr_4bit(y: u8) -> i16 {
    let y = y as i32 * Q as i32;

    ((y + (1 << 3)) >> 4) as i16
}

/// x -> round((2^10 / Q) * x) (mod 2^10)
pub const fn compr_10bit(x: i16) -> u16 {
    const M: i64 = power_div_q(10 + 24);

    let a = M * x as i64;
    let div = (a + (1 << 23)) >> 24;

    (div & 0x3FF) as u16
}

/// y -> round((q/2^10) * y)
pub const fn decompr_10bit(y: u16) -> i16 {
    let y = y as i32 * Q as i32;

    ((y + (1 << 9)) >> 10) as i16
}

/// y -> round((q/2) * y)
pub const fn decompr_1bit(y: u8) -> i16 {
    let y = -((y & 1) as i16);
    y & Q_HALF as i16
}

#[test]
fn test_compress() {
    for i in -Q..Q {
        let compressed_4bit = i.rem_euclid(Q) as f64 * (2f64.powi(4)) / Q as f64;
        assert_eq!(compr_4bit(i), compressed_4bit.round() as u8 % 16);

        let compressed_10bit = i.rem_euclid(Q) as f64 * (2f64.powi(10)) / Q as f64;
        assert_eq!(compr_10bit(i), compressed_10bit.round() as u16 % 1024);
    }

    for i in 0..16 {
        assert_eq!(compr_4bit(decompr_4bit(i)), i);
    }

    for i in 0..1024 {
        assert_eq!(compr_10bit(decompr_10bit(i)), i);
    }
}

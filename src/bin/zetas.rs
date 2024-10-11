use pqcrypto_std::{
    kyber::{self, Q},
    reduce::{mont_mul, to_mont, R_MOD_Q},
};

const ZETA1: i16 = to_mont(17);

fn main() {
    let zetas = (0..128i16).fold(vec![R_MOD_Q as i16], |mut acc, _| {
        let prev = acc.last().unwrap();
        acc.push(mont_mul(*prev, ZETA1));
        acc
    });

    let zetas: Vec<i16> = (0..128u8)
        .map(|i| {
            let i = i.reverse_bits() >> 1;
            match zetas[i as usize] {
                z if z > Q / 2 => z - Q,
                z if z < -Q / 2 => z + Q,
                z => z,
            }
        })
        .collect();

    assert_eq!(zetas, kyber::ZETAS);
    println!("const ZETAS: [i16; 128] = {:?};", zetas);
}

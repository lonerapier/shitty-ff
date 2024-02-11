// structure adapted from https://github.com/lambdaclass/lambdaworks/blob/main/math/src/unsigned_integer/montgomery.rs
use ark_ff::{BigInt, BigInteger};

pub struct MontgomeryAlgorithms;
impl MontgomeryAlgorithms {
    /// Compute CIOS multiplication of `a` * `b`
    pub fn cios<const N: usize>(
        a: &BigInt<N>,
        b: &BigInt<N>,
        p: &BigInt<N>,
        mu: &u64,
    ) -> BigInt<N> {
        let mut t = [0u64; N];
        let mut t_extra = [0u64; 2];

        for i in 0..N {
            let mut c = 0u128;

            for (j, item) in t.iter_mut().enumerate().take(N) {
                // (c, t[i]) = t[i] + a[j] * b[i] + c
                let sum = *item as u128 + (a.0[j] as u128 * b.0[i] as u128) + c;
                c = sum >> 64;
                *item = sum as u64;
            }
            // (t[n+1], t[n]) = t[n] + c
            let cs: u128 = t_extra[0] as u128 + c;
            t_extra[1] = (cs >> 64) as u64;
            t_extra[0] = cs as u64;

            // m = t[0] * mu[0] mod b;
            let m = ((t[0] as u128 * (*mu as u128)) << 64) >> 64;
            // (c, _) = t[0] + m * q[0];
            let mut c = ((t[0] as u128) + m * (p.0[0] as u128)) >> 64;
            for j in 1..N {
                // (c, t[j-1]) = t[j] + m*q[j] + c
                let sum = t[j] as u128 + m * (p.0[j] as u128) + c;
                c = sum >> 64;
                t[j - 1] = sum as u64;
            }

            // (c,t[n-1]) = t[n] + c
            let sum = t_extra[0] as u128 + c;
            c = sum >> 64;
            t[N - 1] = ((sum << 64) >> 64) as u64;
            // t[n+1] = t[n] + c
            t_extra[1] = t_extra[0] + c as u64;
        }

        let mut result = BigInt(t);
        if t_extra[0] > 0 || p.le(&result) {
            result.sub_with_borrow(p);
        }

        result
    }
    fn cios_for_one_spare_bit_modulus<const N: usize>(
        a: &BigInt<N>,
        b: &BigInt<N>,
        p: &BigInt<N>,
        mu: &u64,
    ) -> BigInt<N> {
        let mut t = [0u64; N];
        let mut t_extra = 0;

        for i in 0..N {
            let mut c = 0u128;

            for (j, item) in t.iter_mut().enumerate().take(N) {
                // (c, t[i]) = t[i] + a[j] * b[i] + c
                c += *item as u128 + (a.0[j] as u128 * b.0[i] as u128);
                *item = c as u64;
                c >>= 64;
            }
            // (t[n+1], t[n]) = t[n] + c
            t_extra = c as u64;

            // m = t[0] * mu[0] mod b;
            let m = ((t[0] as u128 * (*mu as u128)) << 64) >> 64;
            // (c, _) = t[0] + m * q[0];
            let mut c = ((t[0] as u128) + m * (p.0[0] as u128)) >> 64;
            for j in 1..N {
                // (c, t[j-1]) = t[j] + m*q[j] + c
                c += t[j] as u128 + m * (p.0[j] as u128);
                t[j - 1] = c as u64;
                c >>= 64;
            }

            // (c,t[n-1]) = t[n] + c
            c += t_extra as u128;
            t[N - 1] = ((c << 64) >> 64) as u64;
        }

        let mut result = BigInt(t);
        if t_extra > 0 || p.le(&result) {
            result.sub_with_borrow(p);
        }

        result
    }

    /// taken from https://hackmd.io/@gnark/modular_multiplication
    fn cios_with_no_carry_opt<const N: usize>(
        a: &BigInt<N>,
        b: &BigInt<N>,
        p: &BigInt<N>,
        mu: &u64,
    ) -> BigInt<N> {
        let mut t = [0u64; N];
        for i in 0..N {
            // (A, t[0]) = t[0] + a[0] * b[i]
            let mut ad = t[0] as u128 + (a.0[0] as u128 * b.0[i] as u128);
            t[0] = ad as u64;
            ad >>= 64;

            // m = t[0] * mu[0] mod b
            let m = ((t[0] as u128 * (*mu as u128)) << 64) >> 64;
            // (c, _) = t[0] + m * q[0]
            let mut c = ((t[0] as u128) + m * (p.0[0] as u128)) >> 64;
            for j in 1..N {
                // (A, t[j]) = t[j] + a[j]*b[i] + A
                ad += t[j] as u128 + (a.0[j] as u128 * b.0[i] as u128);
                t[j] = ad as u64;
                ad >>= 64;

                // (C, t[j-1]) = t[j] + m*p[j] + C
                c += t[j] as u128 + m * (p.0[j] as u128);
                t[j - 1] = c as u64;
                c >>= 64;
            }
            // t[N-1] = C + A
            t[N - 1] = (c + ad) as u64;
        }

        let mut result = BigInt(t);
        if p.le(&result) {
            result.sub_with_borrow(p);
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::{BigInt, BigInteger384};

    use crate::montgomery::MontgomeryAlgorithms;

    #[test]
    fn cios_works() {
        let a = BigInteger384::from(10u64);
        let b = BigInteger384::from(11u64);
        let p = BigInteger384::from(23u64);
        // let mu = -1 * (p.divn) % (2 ^ 64);
        // TODO: find how to calculate inverse of modulus from arkworks
        // also learn how to use montconfig trait
        let mu: u64 = 3208129404123400281;
        let c = BigInteger384::from(13_u64); // x * y * (r^{-1}) % m, where r = 2^{64 * 6} and r^{-1} mod m = 2.
        assert_eq!(MontgomeryAlgorithms::cios(&a, &b, &p, &mu), c);
    }

    #[test]
    fn cios_works_without_modulo_set() {
        let x = BigInteger384::from(1000000000000u64);
        let y = BigInteger384::from(100000000111111u64);
        let m: BigInt<6> = BigInt!("1174276539873794166777825651584630259791601769697"); // this is prime
        let mu: u64 = 16085280245840369887; // negative of the inverse of `m` modulo 2^{64}
        assert_eq!(
            MontgomeryAlgorithms::cios(&x, &y, &m, &mu),
            MontgomeryAlgorithms::cios_for_one_spare_bit_modulus(&x, &y, &m, &mu)
        );
    }

    #[test]
    fn cios_works_with_no_carry_opt() {
        let x = BigInteger384::from(1000000000000u64);
        let y = BigInteger384::from(100000000111111u64);
        let m: BigInt<6> = BigInt!("1174276539873794166777825651584630259791601769697"); // this is prime
        let mu: u64 = 16085280245840369887; // negative of the inverse of `m` modulo 2^{64}
        assert_eq!(
            MontgomeryAlgorithms::cios(&x, &y, &m, &mu),
            MontgomeryAlgorithms::cios_with_no_carry_opt(&x, &y, &m, &mu)
        );
    }
}

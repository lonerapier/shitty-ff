use crate::util::{reduce_128, reduce_64};
use ark_ff::{BigInt, FftField, Field, One, PrimeField, Zero};
use ark_serialize::Flags;
use num_bigint::BigUint;
use std::convert::From;
use std::fmt::Display;
use std::ops::Neg;
use std::{
    iter,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};
use zeroize::Zeroize;

pub const P: u64 = (0xffffffff_ffffffff << 32) + 1;

// pub const NEG_P: u64 = P.wrapping_neg();

pub const P_MINUS_ONE_DIV_TWO: u64 = (0xffffffff_ffffffff << 32) >> 1;

#[derive(Eq, PartialEq, Debug, Default, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Goldilocks {
    pub value: u64,
}

impl Goldilocks {
    fn new(num: u64) -> Self {
        Self {
            value: reduce_64(num),
        }
    }

    #[inline]
    pub fn is_geq_modulus(&self) -> bool {
        self.value >= P
    }
}

impl Field for Goldilocks {
    const ZERO: Self = Self { value: 0 };
    const ONE: Self = Self { value: 1 };
    const SQRT_PRECOMP: Option<ark_ff::SqrtPrecomputation<Self>> = None;
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    fn characteristic() -> &'static [u64] {
        todo!()
    }

    fn extension_degree() -> u64 {
        1
    }

    fn from_base_prime_field(elem: Self::BasePrimeField) -> Self {
        elem
    }

    fn from_base_prime_field_elems(elems: &[Self::BasePrimeField]) -> Option<Self> {
        if elems.len() != (Self::extension_degree() as usize) {
            return None;
        }
        Some(elems[0])
    }

    fn double(&self) -> Self {
        *self + *self
    }

    fn double_in_place(&mut self) -> &mut Self {
        *self = self.double();
        self
    }

    fn frobenius_map_in_place(&mut self, power: usize) {
        todo!()
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        todo!()
    }

    fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        todo!()
    }

    /// copied from plonky3's [inverse](https://github.com/Plonky3/Plonky3/blob/main/goldilocks/src/lib.rs#L167) and [recmo's](https://github.com/recmo/goldilocks/blob/main/ntt/src/field/algo/generic.rs#L277).
    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // a^-1 = a^(p-2) mod p
        // p - 2 = 2(2^31 - 1)(2^32 + 1) + 1
        // 2^31 - 1 = 2(2^15 - 1)(2^15 + 1) + 1  (optimal)

        let t2 = self.square() * self; // 3
        let t3 = t2.square() * self; // 7

        let t6 = t3.pow([1 << 3]) * t3; // 63
        let t60 = t6.square(); // 126
        let t7 = t60 * self; // 2^7-1
        let t12 = t60.pow([1 << 5]) * t6; // 2^12-1

        let t24 = t12.pow([1 << 12]) * t12; // 2^24-1

        let t31 = t24.pow([1 << 7]) * t7;

        // compute base^111111111111111111111111111111101111111111111111111111111111111
        let t63 = t31.pow([1 << 32]) * t31;

        // compute base^1111111111111111111111111111111011111111111111111111111111111111
        let res = t63.square() * self;

        debug_assert_eq!(res * *self, Self::ONE);

        Some(res)
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        if let Some(inverse) = self.inverse() {
            *self = inverse;
            Some(self)
        } else {
            None
        }
    }

    fn legendre(&self) -> ark_ff::LegendreSymbol {
        todo!()
    }

    fn neg_in_place(&mut self) -> &mut Self {
        *self = self.neg();
        self
    }

    fn sqrt(&self) -> Option<Self> {
        todo!()
    }

    fn square(&self) -> Self {
        *self * self
    }

    fn square_in_place(&mut self) -> &mut Self {
        *self = self.square();
        self
    }

    fn to_base_prime_field_elements(&self) -> Self::BasePrimeFieldIter {
        todo!()
    }
}

impl ark_serialize::CanonicalSerializeWithFlags for Goldilocks {
    fn serialize_with_flags<W: ark_serialize::Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), ark_serialize::SerializationError> {
        todo!()
    }

    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        todo!()
    }
}

impl ark_serialize::CanonicalSerialize for Goldilocks {
    fn serialize_with_mode<W: ark_serialize::Write>(
        &self,
        writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        todo!()
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        todo!()
    }
}

impl ark_serialize::CanonicalDeserializeWithFlags for Goldilocks {
    fn deserialize_with_flags<R: ark_serialize::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), ark_serialize::SerializationError> {
        todo!()
    }
}

impl ark_serialize::CanonicalDeserialize for Goldilocks {
    fn deserialize_with_mode<R: ark_serialize::Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        todo!()
    }
}

impl ark_serialize::Valid for Goldilocks {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        todo!()
    }
}

impl Zeroize for Goldilocks {
    fn zeroize(&mut self) {
        self.value.zeroize()
    }
}

impl ark_std::rand::distributions::Distribution<Goldilocks>
    for ark_std::rand::distributions::Standard
{
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Goldilocks {
        loop {
            let tmp = Goldilocks::new(rng.sample(ark_std::rand::distributions::Standard));
            if !tmp.is_geq_modulus() {
                return tmp;
            }
        }
    }
}

impl std::iter::Product for Goldilocks {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        todo!()
    }
}

impl<'a> std::iter::Product<&'a Self> for Goldilocks {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        todo!()
    }
}

impl std::iter::Sum for Goldilocks {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        todo!()
    }
}

impl<'a> std::iter::Sum<&'a Self> for Goldilocks {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        todo!()
    }
}

impl Display for Goldilocks {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl One for Goldilocks {
    fn one() -> Self {
        Self::ONE
    }

    fn is_one(&self) -> bool
    where
        Self: PartialEq,
    {
        self.value == 1
    }
}

impl Zero for Goldilocks {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl Sub for Goldilocks {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let (mut a, c) = self.value.overflowing_sub(rhs.value);
        let adj = 0u32.wrapping_sub(c as u32);
        a = a.wrapping_sub(adj as u64);

        Self::Output { value: a }
    }
}

impl Sub<&Self> for Goldilocks {
    type Output = Self;
    fn sub(self, rhs: &Self) -> Self::Output {
        self.sub(*rhs)
    }
}

impl Sub<&mut Self> for Goldilocks {
    type Output = Self;
    fn sub(self, rhs: &mut Self) -> Self::Output {
        self.sub(*rhs)
    }
}

impl SubAssign for Goldilocks {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl SubAssign<&Self> for Goldilocks {
    fn sub_assign(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
}

impl SubAssign<&mut Self> for Goldilocks {
    fn sub_assign(&mut self, rhs: &mut Self) {
        *self -= *rhs;
    }
}

impl Mul for Goldilocks {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        reduce_128((self.value as u128) * (rhs.value as u128))
    }
}

impl Mul<&Self> for Goldilocks {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self::Output {
        self.mul(*rhs)
    }
}

impl Mul<&mut Self> for Goldilocks {
    type Output = Self;

    fn mul(self, rhs: &mut Self) -> Self::Output {
        self.mul(*rhs)
    }
}

impl MulAssign for Goldilocks {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl MulAssign<&Self> for Goldilocks {
    fn mul_assign(&mut self, rhs: &Self) {
        *self *= *rhs;
    }
}

impl MulAssign<&mut Self> for Goldilocks {
    fn mul_assign(&mut self, rhs: &mut Self) {
        *self *= *rhs;
    }
}

impl Add for Goldilocks {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let b = P.wrapping_sub(rhs.value);
        let (mut a, c) = self.value.overflowing_sub(b);
        let adj = 0u32.wrapping_sub(c as u32);
        a = a.wrapping_sub(adj as u64);

        Self::Output { value: a }
    }
}

impl Add<&Self> for Goldilocks {
    type Output = Self;
    fn add(self, rhs: &Self) -> Self::Output {
        self.add(*rhs)
    }
}

impl Add<&mut Self> for Goldilocks {
    type Output = Self;
    fn add(self, rhs: &mut Self) -> Self::Output {
        self.add(*rhs)
    }
}

impl AddAssign for Goldilocks {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl AddAssign<&Self> for Goldilocks {
    fn add_assign(&mut self, rhs: &Self) {
        *self += *rhs;
    }
}

impl AddAssign<&mut Self> for Goldilocks {
    fn add_assign(&mut self, rhs: &mut Self) {
        *self += *rhs;
    }
}

impl Div for Goldilocks {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let rhs_inv = rhs.inverse().expect("zero not invertible");
        self * rhs_inv
    }
}

impl Div<&mut Self> for Goldilocks {
    type Output = Self;

    #[inline(always)]
    fn div(self, other: &mut Self) -> Self::Output {
        self.div(&*other)
    }
}

impl Div<&Self> for Goldilocks {
    type Output = Self;

    #[inline(always)]
    fn div(self, other: &Self) -> Self::Output {
        self.div(*other)
    }
}

// intersting: use dec macros to make implmentation easier for other fields https://github.com/Plonky3/Plonky3/pull/49
impl DivAssign for Goldilocks {
    fn div_assign(&mut self, rhs: Self) {
        let rhs_inv = rhs.inverse().expect("zero not invertible");
        *self *= rhs_inv;
    }
}

/// Computes `self *= other.inverse()` if `other.inverse()` is `Some`, and
/// panics otherwise.
impl DivAssign<&Self> for Goldilocks {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl DivAssign<&mut Self> for Goldilocks {
    #[inline(always)]
    fn div_assign(&mut self, other: &mut Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl Neg for Goldilocks {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self {
            value: P - self.value,
        }
    }
}

impl From<num_bigint::BigUint> for Goldilocks {
    fn from(value: num_bigint::BigUint) -> Self {
        todo!()
    }
}

impl From<Goldilocks> for BigUint {
    fn from(value: Goldilocks) -> Self {
        todo!()
    }
}

impl From<bool> for Goldilocks {
    fn from(value: bool) -> Self {
        Self::new(value as u64)
    }
}

impl From<u8> for Goldilocks {
    fn from(value: u8) -> Self {
        Self::new(value as u64)
    }
}

impl From<i8> for Goldilocks {
    fn from(value: i8) -> Self {
        let val = Self::new(value as u64);
        if value < 0 {
            -val
        } else {
            val
        }
    }
}

impl From<u16> for Goldilocks {
    fn from(value: u16) -> Self {
        Self::new(value as u64)
    }
}

impl From<i16> for Goldilocks {
    fn from(value: i16) -> Self {
        let val = Self::new(value as u64);
        if value < 0 {
            -val
        } else {
            val
        }
    }
}

impl From<u32> for Goldilocks {
    fn from(value: u32) -> Self {
        Self::new(value as u64)
    }
}

impl From<i32> for Goldilocks {
    fn from(value: i32) -> Self {
        let val = Self::new(value as u64);
        if value < 0 {
            -val
        } else {
            val
        }
    }
}

impl From<u64> for Goldilocks {
    fn from(value: u64) -> Self {
        Self::new(value as u64)
    }
}

impl From<i64> for Goldilocks {
    fn from(value: i64) -> Self {
        let val = Self::new(value as u64);
        if value < 0 {
            -val
        } else {
            val
        }
    }
}

impl From<u128> for Goldilocks {
    fn from(value: u128) -> Self {
        reduce_128(value)
    }
}

impl std::str::FromStr for Goldilocks {
    type Err = ();
    // TODO: revisit
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let modulus = num_bigint::BigInt::from(P);
        let mut res = num_bigint::BigInt::from_str(s).map_err(|_| ())? % &modulus;
        if res < num_bigint::BigInt::zero() {
            res += modulus;
        }
        // todo: check if this is right??
        BigUint::try_from(res)
            .map_err(|_| ())
            .and_then(TryFrom::try_from)
            .ok()
            .and_then(Self::from_bigint)
            .ok_or(())
    }
}

impl From<BigInt<1>> for Goldilocks {
    fn from(value: BigInt<1>) -> Self {
        Self::new(value.0[0])
    }
}

impl From<Goldilocks> for BigInt<1> {
    fn from(value: Goldilocks) -> Self {
        BigInt::from(value.value)
    }
}

impl PrimeField for Goldilocks {
    type BigInt = BigInt<1>;
    const MODULUS: Self::BigInt = BigInt([P]);
    const MODULUS_BIT_SIZE: u32 = 64;
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([P_MINUS_ONE_DIV_TWO]);
    const TRACE: Self::BigInt = Self::MODULUS.two_adic_coefficient();
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = Self::TRACE.divide_by_2_round_down();

    fn from_bigint(repr: Self::BigInt) -> Option<Self> {
        Some(Self::new(repr.0[0]))
    }

    fn into_bigint(self) -> Self::BigInt {
        BigInt::from(self)
    }
}

impl From<Goldilocks> for u64 {
    fn from(value: Goldilocks) -> Self {
        value.value
    }
}

// TODO: revisit
impl FftField for Goldilocks {
    const GENERATOR: Self = Self { value: 7 };
    const TWO_ADICITY: u32 = 0;
    const TWO_ADIC_ROOT_OF_UNITY: Self = Self { value: 9 };
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::tests::field_tests;
    use ark_std::rand::thread_rng;

    #[test]
    fn test_goldilocks() {
        let test_elem = Goldilocks::new(P - 1);
        let lhs: u64 = test_elem.into();
        assert_eq!(lhs, P - 1);

        let test_elem = Goldilocks::new(0);
        let lhs: u64 = test_elem.into();
        assert_eq!(lhs, 0);

        let test_elem = Goldilocks::new(1);
        let lhs: u64 = test_elem.into();
        assert_eq!(lhs, 1);

        let test_elem = Goldilocks::new(P);
        let lhs: u64 = test_elem.into();
        assert_eq!(lhs, 0);

        let a = Goldilocks::from(10_u8);
        let b = Goldilocks::from(10_u16);
        assert_eq!(a, b);

        let a = Goldilocks::from(-10_i8);
        let b = Goldilocks::from(-10_i16);
        assert_eq!(a, b);

        let a = Goldilocks::from(10_u32);
        let b = Goldilocks::from(10_u128);
        assert_eq!(a, b);

        let a: Goldilocks = Goldilocks::MODULUS.into();
        let b = Goldilocks::ONE;
        assert_eq!(a + b, Goldilocks::ONE);

        let a = Goldilocks::new(P - 1);
        assert_eq!(a.square(), Goldilocks::ONE);

        let a = Goldilocks::ZERO;
        assert_eq!(a.inverse(), None);

        let a = Goldilocks::new(2).inverse().unwrap();
        assert_eq!(a.value, 9223372034707292161_u64);
    }

    #[test]
    fn test_ops() {
        let mut rng = thread_rng();
        field_tests::<Goldilocks, _>(&mut rng);
    }
}

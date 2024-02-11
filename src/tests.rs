use std::ops::MulAssign;

// adapted from https://github.com/zhenfeizhang/Goldilocks/blob/master/src/tests.rs
use ark_ff::Field;
use rand::Rng;

// TODO: use dec macros instead of funcs

pub fn field_tests<F: Field, R: Rng>(mut rng: R) {
    for _ in 0..100000 {
        let a = F::rand(&mut rng);
        let b = F::rand(&mut rng);
        let c = F::rand(&mut rng);

        addition_tests(a, b, c);
        subtraction_tests(a, b, c);
        multiplication_tests(a, b, c);
        squaring_tests(a, b, c);
        pow_tests(a, b, c);
        inversion_tests(a, b, c);
        division_tests(a, b, c);
        doubling_tests(a, b, c);
    }
}

fn addition_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a;
    t0.add_assign(b);
    t0.add_assign(&c);

    let mut t1 = b;
    t1.add_assign(c);
    t1.add_assign(&a);

    let mut t2 = c;
    t2.add_assign(a);
    t2.add_assign(&b);

    assert_eq!(t0, t1);
    assert_eq!(t1, t2);
}

fn subtraction_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a;
    t0.sub_assign(b);
    t0.sub_assign(&c);

    let mut t1 = a;
    t1.sub_assign(b);
    t1.sub_assign(&c);

    let mut t2 = c;
    t2.sub_assign(a);
    t2.sub_assign(&b);

    let mut t3 = c;
    t3.sub_assign(b);
    t3.sub_assign(&a);

    assert_eq!(t0, t1);
    assert_eq!(t2, t3);
}

fn multiplication_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a;
    t0.mul_assign(b);
    t0.mul_assign(&c);

    let mut t1 = b;
    t1.mul_assign(c);
    t1.mul_assign(&a);

    let mut t2 = c;
    t2.mul_assign(a);
    t2.mul_assign(&b);

    assert_eq!(t0, t1);
    assert_eq!(t1, t2);
}

fn division_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a;
    t0.div_assign(a);

    assert_eq!(t0, F::ONE);

    let mut t1 = b;
    t1.div_assign(b);
    assert_eq!(t1, F::ONE);

    let mut t2 = c;
    t2.div_assign(c);

    assert_eq!(t2, F::ONE);
}

fn doubling_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a.double();
    t0.sub_assign(a);

    let mut t1 = b.double();
    t1.sub_assign(b);

    let mut t2 = c.double();
    t2.sub_assign(c);

    assert_eq!(t0, a);
    assert_eq!(t1, b);
    assert_eq!(t2, c);
}

fn inversion_tests<F: Field>(a: F, b: F, c: F) {
    let mut t0 = a.inverse().unwrap_or(F::ONE);
    t0.mul_assign(&a);

    let mut t1 = b.inverse().unwrap_or(F::ONE);
    t1.mul_assign(&b);

    let mut t2 = c.inverse().unwrap_or(F::ONE);
    t2.mul_assign(&c);

    assert_eq!(t0, F::ONE);
    assert_eq!(t1, F::ONE);
    assert_eq!(t2, F::ONE);
}

fn squaring_tests<F: Field>(a: F, b: F, c: F) {
    assert_eq!(a.square(), a * a);
    assert_eq!(b.square(), b * b);
    assert_eq!(c.square(), c * c);
}

fn pow_tests<F: Field>(a: F, b: F, c: F) {
    let t0 = a.pow([2_u64.pow(5)]);
    let t1 = a.square().square().square().square().square();

    assert_eq!(t0, t1);
}

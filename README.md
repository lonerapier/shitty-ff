# Shitty FF

Experimental implmenetation of finite fields.

## Implementations

- [x] Goldilocks: $2^{64}-2^{32}+1$
  - [ ] quadratic extension field
  - [ ] cubic extension field
  - [ ] aarch64 backend
  - [ ] montgomery backend
- [ ] Mersenne Prime: $2^{32}-1$
- [ ] Baby Bear

## Acknowledgements

This repo wouldn't have been possible without these awesome references. Most of the code is copied and modified from these.

- [arkworks]()
- [plonky3's goldilocks](https://github.com/Plonky3/Plonky3/blob/main/goldilock) implementation
- [risc0's](https://github.com/risc0/risc0/blob/main/risc0/core/src/field/goldilocks.rs) field impls
- [winterfell's](https://github.com/facebook/winterfell/tree/main/math/src/field) fields
- recmo's [goldilocks](https://github.com/recmo/goldilocks)
-
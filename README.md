
Staged compilation proof-of-concept in Agda
-------------------------------------------

We try to use the ideas from the paper 
["Closure-Free Functional Programming in a Two-Level Type Theory"](https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf)
by András Kovács to build a libary of algebra operations useful in the context
cryptography (in particular zero knowledge proofs).

Note: This is very much a work-in-progress experimental prototype, intended primarily
as a proof-of-concept and a learning device.

### Algebra libary

- [ ] fixed-size big integers (eg. 256-bit ones)
  - [x] bit operations
  - [x] comparison
  - [x] addition, subtraction 
  - [x] multiplication, squaring, scaling
  - [ ] long division
- [ ] finite fields
  - [ ] generic small prime fields
  - [ ] large prime fields
    - [x] addition, subtraction, negation
    - [ ] standard representation
        - [ ] Barrett reduction, multiplication
        - [x] inversion, division
    - [ ] Montgomery representation
        - [x] Montgomery multiplication, squaring
        - [x] conversion to/from Montgomery representation
        - [x] inversion, division
    - [ ] exponentiation
    - [ ] batch inversion
  - [ ] specific small fields (higher performance than the generic ones)
     - [ ] Goldilocks 
     - [ ] Mersenne-31
     - [ ] Babybear
  - [ ] generic field extensions
- [ ] elliptic curves
- [ ] polynomials
- [ ] number theoretical transform

### Organization

- the user application is written in Agda (as a metaprogram)
- building on the top of the "frontend", which is also written in Agda
- the backend is written in Haskell

### Compilation pipeline

1. You write your application as a metaprogram in Agda, using HOAS representation and whatever convenience the library can offer
2. This gets translated into a very standard well-typed first-order representation of simply typed lambda calculus
3. In theory you could have a well-typed interpreter at this level, but I haven't implement the primops yet
4. The first order representation gets downgraded to an untyped "raw" representation
5. That raw AST is then exported as a text file (using a hand-written `Show` instance)
6. The resulting text file can be read by Haskell with the standard derived `Read` instance
7. This can be interpreted at this point too
8. Lambda lifting transformation is applied
9. ANF conversion is applied
10. Code generation (as C source code)
11. Finally the resulting C code is compiled by a standard C compiler 

TODO: make a script automating this


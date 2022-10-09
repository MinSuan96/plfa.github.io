---
title     : "Assignment1: TSPL Assignment 1"
permalink : /TSPL/2022/Assignment1/
---

```
module Assignment1 where
```

## YOUR NAME AND EMAIL GOES HERE
Minsuan Teh
s1817967@ed.ac.uk

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## Naturals

```
module Naturals where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```agda
  seven : ℕ
  seven = suc (suc (suc (suc (suc (suc (suc zero))))))
```

You will need to give both a type signature and definition for the
variable `seven`. Type `C-c C-l` in Emacs to instruct Agda to re-load.


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations, using the equations for `+`.

```agda
  _ : 3 + 4 ≡ 7
  _ =
    begin
      3 + 4
    ≡⟨⟩
      (suc (suc (suc zero))) + (suc (suc (suc (suc (zero)))))
    ≡⟨⟩
      suc ((suc (suc (zero))) + (suc (suc (suc (suc (zero))))))
    ≡⟨⟩
      suc (suc (suc zero) + (suc (suc (suc (suc zero)))))
    ≡⟨⟩
      suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
    ≡⟨⟩
      suc (suc (suc (suc (suc (suc (suc zero))))))
    ≡⟨⟩
      7
    ∎
```


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
(You do not need to step through the evaluation of `+`.)

```agda
  _ : 3 * 4 ≡ 12
  _ =
    begin
      3 * 4
    ≡⟨⟩
      suc (suc (suc zero)) * suc (suc (suc (suc zero)))
    ≡⟨⟩
      4 + (suc (suc zero) * suc (suc (suc (suc zero))))
    ≡⟨⟩
      4 + (4 + (suc zero * suc (suc (suc (suc zero)))))
    ≡⟨⟩
      4 + 4 + 4 + (0 * 3)
    ≡⟨⟩
      12
    ∎
```


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

Check that `3 ^ 4` is `81`.

```agda
  _^_ : ℕ → ℕ → ℕ
  m ^ zero = 1
  m ^ (suc n) = m * (m ^ n)

  _ : 3 ^ 4 ≡ 81
  _ =
    begin
      3 ^ 4
    ≡⟨⟩
      3 * (3 ^ 3)
    ≡⟨⟩
      3 * (3 * (3 ^ 2))
    ≡⟨⟩
      3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
      3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
      3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
      3 * (3 * (3 * 3))
    ≡⟨⟩
      3 * (3 * 9)
    ≡⟨⟩
      3 * 27
    ≡⟨⟩
      81
    ∎
```



#### Exercise `∸-example₁` and `∸-example₂` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```agda
  _ = 
    begin
      5 ∸ 3
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎

  _ = 
    begin
      3 ∸ 5
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      0 ∸ 2
    ≡⟨⟩
      0
    ∎
```


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
```agda
  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded as

    ⟨⟩ I O I I

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as:

    ⟨⟩ O O I O I I

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `⟨⟩ O`.
Confirm that these both give the correct answer for zero through four.

```agda
  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (x O) = x I
  inc (x I) = (inc x) O

  _ =
    begin
      ⟨⟩ I
    ≡⟨⟩
      inc (⟨⟩ O)
    ∎

  _ = 
    begin
      ⟨⟩ I O
    ≡⟨⟩
      inc (⟨⟩ I)
    ≡⟨⟩
      inc (inc (⟨⟩ O))
    ∎

  _ = 
    begin
      ⟨⟩ I I
    ≡⟨⟩
      inc (⟨⟩ I O)
    ≡⟨⟩
      inc (inc (⟨⟩ I))
    ≡⟨⟩
      inc (inc (inc (⟨⟩ O)))
    ∎

  _ = 
    begin
      ⟨⟩ I O O
    ≡⟨⟩
      inc (⟨⟩ I I)
    ≡⟨⟩
      inc (inc (⟨⟩ I O))
    ≡⟨⟩
      inc (inc (inc (⟨⟩ I)))
    ≡⟨⟩
      inc (inc (inc (inc (⟨⟩ O))))
    ∎
```

```agda
  to : ℕ → Bin
  to 0 = ⟨⟩ O
  to (suc x) = inc (to x)

  _ =
    begin
      to 0
    ≡⟨⟩
      ⟨⟩ O
    ∎

  _ =
    begin
      to 1
    ≡⟨⟩
      inc (to 0)
    ≡⟨⟩
      inc (⟨⟩ O)
    ≡⟨⟩
      ⟨⟩ I
    ∎

  _ =
    begin
      to 2
    ≡⟨⟩
      inc (to 1)
    ≡⟨⟩
      inc (inc (to 0))
    ≡⟨⟩
      inc (inc (⟨⟩ O))
    ≡⟨⟩
      inc (⟨⟩ I)
    ≡⟨⟩
      ⟨⟩ I O
    ∎

  _ =
    begin
      to 3
    ≡⟨⟩
      inc (to 2)
    ≡⟨⟩
      inc (inc (to 1))
    ≡⟨⟩
      inc (inc (inc ((to 0))))
    ≡⟨⟩
      inc (inc (inc (⟨⟩ O)))
    ≡⟨⟩
      inc (inc (⟨⟩ I))
    ≡⟨⟩
      inc (⟨⟩ I O)
    ≡⟨⟩
      ⟨⟩ I I
    ∎

  _ =
    begin
      to 4
    ≡⟨⟩
      inc (to 3)
    ≡⟨⟩
      inc (inc (to 2))
    ≡⟨⟩
      inc (inc (inc ((to 1))))
    ≡⟨⟩
      inc (inc (inc (inc ((to 0)))))
    ≡⟨⟩
      inc (inc (inc (inc (⟨⟩ O))))
    ≡⟨⟩
      inc (inc (inc (⟨⟩ I)))
    ≡⟨⟩
      inc (inc (⟨⟩ I O))
    ≡⟨⟩
      inc (⟨⟩ I I)
    ≡⟨⟩
      ⟨⟩ I O O
    ∎
```

```agda
  from : Bin → ℕ
  from ⟨⟩ = 0
  from (x O) = 2 * from x
  from (x I) = 2 * from x + 1

  _ =
    begin
      from (⟨⟩ O)
    ≡⟨⟩
      (from ⟨⟩) + (from ⟨⟩)
    ≡⟨⟩
      0 + 0
    ≡⟨⟩
      0
    ∎

  _ =
    begin
      from (⟨⟩ I)
    ≡⟨⟩
      suc ((from ⟨⟩) + (from ⟨⟩))
    ≡⟨⟩
      suc (0 + 0)
    ≡⟨⟩
      suc 0
    ≡⟨⟩
      1
    ∎

  _ =
    begin
      from (⟨⟩ I O)
    ≡⟨⟩
      (from (⟨⟩ I)) + (from (⟨⟩ I))
    ≡⟨⟩
      (suc ((from ⟨⟩) + (from ⟨⟩))) + (suc ((from ⟨⟩) + (from ⟨⟩)))
    ≡⟨⟩
      (suc (0 + 0)) + (suc (0 + 0))
    ≡⟨⟩
      (suc 0) + (suc 0)
    ≡⟨⟩
      1 + 1
    ≡⟨⟩
      2
    ∎

  _ =
    begin
      from (⟨⟩ I I)
    ≡⟨⟩
      suc ((from (⟨⟩ I)) + (from (⟨⟩ I)))
    ≡⟨⟩
      suc ((suc ((from ⟨⟩) + (from ⟨⟩))) + (suc ((from ⟨⟩) + (from ⟨⟩))))
    ≡⟨⟩
      suc ((suc (0 + 0)) + (suc (0 + 0)))
    ≡⟨⟩
      suc ((suc 0) + (suc 0))
    ≡⟨⟩
      suc (1 + 1)
    ≡⟨⟩
      suc 2
    ≡⟨⟩
      3
    ∎

  _ =
    begin
      from (⟨⟩ I O O)
    ≡⟨⟩
      (from (⟨⟩ I O)) + (from (⟨⟩ I O))
    ≡⟨⟩
      ((from (⟨⟩ I)) + (from (⟨⟩ I))) + ((from (⟨⟩ I)) + (from (⟨⟩ I)))
    ≡⟨⟩
      ((suc ((from ⟨⟩) + (from ⟨⟩))) + (suc ((from ⟨⟩) + (from ⟨⟩)))) + ((suc ((from ⟨⟩) + (from ⟨⟩))) + (suc ((from ⟨⟩) + (from ⟨⟩))))
    ≡⟨⟩
      ((suc (0 + 0)) + (suc (0 + 0))) + ((suc (0 + 0)) + (suc (0 + 0)))
    ≡⟨⟩
      ((suc 0) + (suc 0)) + ((suc 0) + (suc 0))
    ≡⟨⟩
      (1 + 1) + (1 + 1)
    ≡⟨⟩
      2 + 2
    ≡⟨⟩
      4
    ∎
```



## Induction

```
module Induction where
  import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
```

## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also require a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```
(Importing `step-≡` defines `_≡⟨_⟩_`.)


```
  open import plfa.part1.Induction
    hiding ()
```

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
(You do not have to prove these properties.)

Give an example of an operator that has an identity and is
associative but is not commutative.
(You do not have to prove these properties.)


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier](/Naturals/#finite-creation).

```agda
  -- Day 0

  -- Day 1
  -- 0 : ℕ

  -- Day 2
  -- 1 : ℕ
  -- (0 + 0) + 0 ≡ 0 + (0 + 0)

  -- Day 3
  -- 2 : ℕ
  -- (0 + 0) + 1 ≡ 0 + (0 + 1)
  -- (0 + 1) + 0 ≡ 0 + (1 + 0)
  -- (0 + 1) + 1 ≡ 0 + (1 + 1)
  -- (1 + 0) + 0 ≡ 1 + (0 + 0)
  -- (1 + 0) + 1 ≡ 1 + (0 + 1)
  -- (1 + 1) + 0 ≡ 1 + (1 + 0)
  -- (1 + 1) + 1 ≡ 1 + (1 + 1)

  -- Day 4
  -- 3 : ℕ
  -- (0 + 0) + 2 ≡ 0 + (0 + 2)
  -- (0 + 1) + 2 ≡ 0 + (1 + 2)
  -- (0 + 2) + 0 ≡ 0 + (2 + 0)
  -- (0 + 2) + 1 ≡ 0 + (2 + 1)
  -- (0 + 2) + 2 ≡ 0 + (2 + 2)
  -- (1 + 0) + 2 ≡ 1 + (0 + 2)
  -- (1 + 1) + 2 ≡ 1 + (1 + 2)
  -- (1 + 2) + 0 ≡ 1 + (2 + 0)
  -- (1 + 2) + 1 ≡ 1 + (2 + 1)
  -- (1 + 2) + 2 ≡ 1 + (2 + 2)
  -- (2 + 0) + 0 ≡ 2 + (0 + 0)
  -- (2 + 0) + 1 ≡ 2 + (0 + 1)
  -- (2 + 0) + 2 ≡ 2 + (0 + 2)
  -- (2 + 1) + 0 ≡ 2 + (1 + 0)
  -- (2 + 1) + 1 ≡ 2 + (1 + 1)
  -- (2 + 1) + 2 ≡ 2 + (1 + 2)
  -- (2 + 2) + 0 ≡ 2 + (2 + 0)
  -- (2 + 2) + 1 ≡ 2 + (2 + 1)
  -- (2 + 2) + 2 ≡ 2 + (2 + 2)
```

#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

```agda
  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap m n p =
    begin
      m + (n + p)
    ≡⟨ sym (+-assoc m n p) ⟩
      (m + n) + p
    ≡⟨ cong (_+ p) (+-comm m n) ⟩
      (n + m) + p
    ≡⟨ +-assoc n m p ⟩
      n + (m + p)
    ∎
```


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```agda
  *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ 0 n p = refl
  *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p = sym (+-assoc p (m * p) (n * p))
```


#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```agda
  *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
  *-assoc 0 n p = refl
  *-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
```


#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```agda
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  *-comm 0 0 =
    begin
      0 * 0
    ≡⟨⟩
      0
    ≡⟨⟩
      0 * 0
    ∎
  *-comm (suc m) 0 =
    begin
      suc m * 0
    ≡⟨⟩
      0 + m * 0
    ≡⟨⟩
      m * 0
    ≡⟨ *-comm m 0 ⟩
      0 * m
    ≡⟨⟩
      0 * m + 0
    ≡⟨⟩
      0 * suc m
    ∎
  *-comm 0 (suc n) =
    begin
      0 * suc n
    ≡⟨⟩
      0 * n + 0
    ≡⟨⟩
      0 * n
    ≡⟨ *-comm 0 n ⟩
      n * 0
    ≡⟨⟩
      0 + (n * 0)
    ≡⟨⟩
      suc n * 0
    ∎
  *-comm (suc m) (suc n) =
    begin
      (suc m) * (suc n)
    ≡⟨⟩
      (suc n) + (m * (suc n))
    ≡⟨ cong ((suc n) +_) (*-comm m (suc n)) ⟩
      (suc n) + ((suc n) * m)
    ≡⟨⟩
      (suc n) + (m + (n * m))
    ≡⟨ +-swap (suc n) m (n * m) ⟩
      m + ((suc n) + (n * m))
    ≡⟨ sym (+-assoc m (suc n) (n * m)) ⟩
      (m + (suc n)) + (n * m)
    ≡⟨ cong (_+ (n * m)) (+-suc m n) ⟩
      suc (m + n) + (n * m)
    ≡⟨ cong suc (+-assoc m n (n * m)) ⟩
      (suc m) + (n + (n * m))
    ≡⟨ cong (λ n*m → (suc m) + (n + n*m)) (*-comm n m) ⟩
      (suc m) + (n + (m * n))
    ≡⟨⟩
      (suc m) + ((suc m) * n)
    ≡⟨ cong ((suc m) +_) (*-comm ((suc m)) n) ⟩
      (suc m) + (n * (suc m))
    ≡⟨⟩
      (suc n) * (suc m)
    ∎
```


#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```agda
  -- Your code goes here
```


#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

```agda
  -- Your code goes here
```


#### Exercise `+*^` (stretch)

Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.

```agda
  open Naturals

  ^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^-distribˡ-+-* m zero p = sym (+-identityʳ (m ^ p))
  ^-distribˡ-+-* m (suc n) p = 
    begin
      m ^ (suc n + p)
    ≡⟨⟩
      m * m ^ (n + p)
    ≡⟨ cong (_*_ m) (^-distribˡ-+-* m n p) ⟩
      m * ((m ^ n) * (m ^ p))
    ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
      m * m ^ n * m ^ p
    ≡⟨⟩
      m ^ (suc n) * m ^ p
    ∎

  ^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  ^-distribʳ-* m n 0 =
    begin
      (m * n) ^ 0
    ≡⟨⟩
      1
    ≡⟨⟩
      (m ^ 0) * (n ^ 0)
    ∎
  ^-distribʳ-* m n (suc p) =
    begin
      (m * n) ^ suc p
    ≡⟨⟩
      (m * n) * (m * n) ^ p
    ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
      (m * n) * ((m ^ p) * (n ^ p))
    ≡⟨ *-assoc m n (m ^ p * n ^ p) ⟩
      m * (n * ((m ^ p) * (n ^ p)))
    ≡⟨ cong (m *_) (*-comm n ((m ^ p) * (n ^ p))) ⟩
      m * (((m ^ p) * (n ^ p)) * n)
    ≡⟨ sym (*-assoc m ((m ^ p) * (n ^ p)) n) ⟩
      (m * ((m ^ p) * (n ^ p))) * n  
    ≡⟨ cong (_* n) (sym (*-assoc m (m ^ p) (n ^ p))) ⟩
      ((m * (m ^ p)) * (n ^ p)) * n
    ≡⟨⟩
      ((m ^ suc p) * (n ^ p)) * n
    ≡⟨ *-assoc (m ^ suc p) (n ^ p) n ⟩
      (m ^ suc p) * ((n ^ p) * n)
    ≡⟨ cong (m ^ suc p *_) (*-comm (n ^ p) n) ⟩
      (m ^ suc p) * (n * (n ^ p))
    ≡⟨⟩
      (m ^ suc p) * (n ^ suc p)
    ∎

  ^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
  ^-*-assoc m n 0 =
    begin
      (m ^ n) ^ 0
    ≡⟨⟩
      1
    ≡⟨⟩
      m ^ 0
    ≡⟨⟩
      m ^ (0 * n)
    ≡⟨ cong (m ^_) (*-comm 0 n) ⟩
      m ^ (n * 0)
    ∎
  ^-*-assoc m n (suc p) =
    begin
      (m ^ n) ^ suc p
    ≡⟨⟩
      (m ^ n) * ((m ^ n) ^ p)
    ≡⟨ cong (m ^ n *_) (^-*-assoc m n p) ⟩
      (m ^ n) * (m ^ (n * p))
    ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
      m ^ (n + n * p)
    ≡⟨ cong (λ n*p → m ^ (n + n*p)) (*-comm n p) ⟩
      m ^ (n + p * n)
    ≡⟨⟩
      m ^ (suc p * n)
    ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
      m ^ (n * suc p)
    ∎
```


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

```agda

  from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
  from-inc ⟨⟩ =
    begin
      from (inc ⟨⟩)
    ≡⟨⟩
      from (⟨⟩ I)
    ≡⟨⟩
      1
    ≡⟨⟩
      suc 0
    ≡⟨⟩
      suc (from (⟨⟩))
    ∎
  from-inc (b O) =
    begin
      from (inc (b O))
    ≡⟨⟩
      from (b I)
    ≡⟨⟩
      2 * from b + 1
    ≡⟨⟩
      from (b O) + 1
    ≡⟨ +-suc (from (b O)) zero ⟩
      suc (from (b O) + zero)
    ≡⟨ cong suc (+-identityʳ (from (b O))) ⟩
      suc (from (b O))
    ∎
  from-inc (b I) =
    begin
      from (inc (b I))
    ≡⟨⟩
      from ((inc b) O)
    ≡⟨⟩
      2 * from (inc b)
    ≡⟨ cong (2 *_) (from-inc b) ⟩
      2 * suc (from b)
    ≡⟨⟩
      suc 1 * suc (from b)
    ≡⟨⟩
      suc (suc 0) * suc (from b)
    ≡⟨⟩
      suc (from b) + (suc 0 * suc (from b))
    ≡⟨⟩
      suc (from b) + (suc (from b) + (0 * suc (from b)))
    ≡⟨⟩
      suc (from b) + (suc (from b) + 0)
    ≡⟨ cong (suc (from b) +_) (+-identityʳ (suc (from b))) ⟩
      suc (from b) + suc (from b)
    ≡⟨ +-suc (suc (from b)) (from b) ⟩
      suc (suc (from b) + from b)
    ≡⟨ cong suc (sym (+-assoc 1 (from b) (from b))) ⟩
      suc (suc (from b + from b))
    ≡⟨ cong ((λ n → suc (suc (from b + n)))) (sym (+-identityʳ (from b))) ⟩
      suc (suc (from b + (from b + 0)))
    ≡⟨⟩
      suc (suc (from b + (from b + (0 * from b))))
    ≡⟨⟩
      suc (suc (from b + (1 * from b)))
    ≡⟨⟩
      suc (suc (2 * from b))
    ≡⟨⟩
      suc (1 + 2 * from b)
    ≡⟨ cong (suc) (+-comm 1 (2 * from b)) ⟩
      suc (2 * from b + 1)
    ≡⟨⟩
      suc (from (b I))
    ∎

  -- to (from (⟨⟩ O I)) = ⟨⟩ I which isn't ⟨⟩ O I
  _ =
    begin
      to (from (⟨⟩ O I))
    ≡⟨⟩
      to 1
    ≡⟨⟩
      ⟨⟩ I -- not ⟨⟩ O I
    ∎

  from-to : ∀ (n : ℕ) → from (to n) ≡ n
  from-to 0 =
    begin
      from (to 0)
    ≡⟨⟩
      from (⟨⟩ O)
    ≡⟨⟩
      2 * from (⟨⟩)
    ≡⟨⟩
      2 * 0
    ≡⟨⟩
      0
    ∎
  from-to (suc n) =
    begin
      from (to (suc n))
    ≡⟨⟩
      from (inc (to n))
    ≡⟨ from-inc (to n) ⟩
      suc (from (to n))
    ≡⟨ cong suc (from-to n) ⟩
      suc n
    ∎
```



## Relations

```
module Relations where
  import Data.Nat using (_≤_; z≤n; s≤s)
  import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                    +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)
  open import plfa.part1.Relations
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

```agda
  -- Your code goes here
```

Give an example of a partial order that is not a total order.

```agda
  -- Your code goes here
```

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```agda
  -- Your code goes here
```


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

```agda
  *-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    → n * p ≤ n * q
  *-monoʳ-≤ zero p q p≤q = z≤n
  *-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

  *-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    → m * p ≤ n * p
  *-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

  *-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    → m * p ≤ n * q
  *-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)
```


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive. Use a direct proof. (A later
exercise exploits the relation between < and ≤.)

```agda
  <-trans : ∀ {m n p} → m < n → n < p → m < p
  <-trans z<s (s<s n<p) = z<s
  <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)

```agda
  -- Your code goes here
```

#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```agda
  +-monoʳ-< : ∀ (n p q : ℕ)
    → p < q
      -------------
    → n + p < n + q
  +-monoʳ-< zero    p q p<q  =  p<q
  +-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

  +-monoˡ-< : ∀ (m n p : ℕ)
    → m < n
      -------------
    → m + p < n + p
  +-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

  +-mono-< : ∀ (m n p q : ℕ)
    → m < n
    → p < q
      -------------
    → m + p < n + q
  +-mono-< m n p q m<n p<q  =  <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)
```

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```agda
  ≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
  ≤-iff-< 0 n (s≤s 1≤n) = z<s
  ≤-iff-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-< m n m≤n)
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

```agda
  -- Your code goes here
```


#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```agda
  o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
  o+o≡e (suc zero) om = suc om
  o+o≡e (suc (suc om)) on = suc (suc (o+o≡e om on))
```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

```agda
  open Naturals
  open Induction

  data One : Bin → Set where
    ⟨⟩I : One (⟨⟩ I)
    _O : ∀ {b : Bin} → One b → One (b O)
    _I : ∀ {b : Bin} → One b → One (b I)

  data Can : Bin → Set where
    ⟨⟩O : Can (⟨⟩ O)
    can : ∀ {b : Bin} → One b → Can b

  -- Can b
  --------------
  -- Can (inc b)

  one-inc : ∀ {b : Bin} → One b → One (inc b)
  one-inc ⟨⟩I = ⟨⟩I O
  one-inc (x O) = x I
  one-inc (x I) = (one-inc x) O

  can-inc : ∀ {b : Bin} → Can b → Can (inc b)
  can-inc ⟨⟩O = can ⟨⟩I
  can-inc (can ⟨⟩I) = can (⟨⟩I O)
  can-inc (can (x O)) = can (x I)
  can-inc (can (x I)) = can (one-inc (x I))

  -------------
  -- Can (to n)

  can-to : ∀ (n : ℕ) → Can (to n)
  can-to zero = ⟨⟩O
  can-to (suc n) = can-inc (can-to n)

  -- Can b
  ------------------
  -- to (from b) ≡ b

{-
  one-atleast1 : ∀ {b : Bin} → One b → (suc zero) ≤ (from b)
  one-atleast1 ⟨⟩I = s≤s z≤n
  one-atleast1 (x O) = <-trans (one-atleast1 ⟨⟩I) (⟨⟩I ≤ (x O))
  one-atleast1 (x I) = <-trans (one-atleast1 (x O)) (⟨⟩I ≤ (x I))

  one-to-from : ∀ {b : Bin} → One b → to (from b) ≡ b
  one-to-from ⟨⟩I = refl
  one-to-from (x O)

  can-to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b
  can-to-from ⟨⟩O = refl
  can-to-from (can ⟨⟩I) = refl
  can-to-from (can (x O)) =
  can-to-from (can (x I)) =
  -}
```
               
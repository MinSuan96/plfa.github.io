---
title     : "Assignment2: TSPL Assignment 2"
permalink : /TSPL/2020/Assignment2/
---

```
module Assignment2 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under
[Learn](https://www.learn.ed.ac.uk/ultra/courses/_98006_1/cl/outline).
Select `Assessment` from the left hand menu, then select `Assignment Submission`.

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


## Equality

```
module Equality where
```

## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


```
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; cong-app)
  open Eq.≡-Reasoning
```

#### Exercise `trans` and `≡-Reasoning` (practice)

Sadly, we cannot use the definition of trans' using ≡-Reasoning as the definition
for trans. Can you see why? (Hint: look at the definition of `_≡⟨_⟩_`)

```agda
  -- Your code goes here
```

#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations](/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

```agda
  open import Data.Nat using (_≤_; z≤n; s≤s; ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (≤-refl; ≤-trans; +-comm)

  module ≤-Reasoning where
    infix  1 begin-≤_
    infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩-≤_ 
    infix  3 _∎-≤

    begin-≤_ : ∀ {m n : ℕ}
      → m ≤ n
        -----
      → m ≤ n
    begin-≤ m≤n = m≤n

    _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ}
      → m ≤ n
        -----
      → m ≤ n
    m ≤⟨⟩ m≤n = m≤n

    _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
      → m ≤ n
      → n ≤ p
        -----
      → m ≤ p
    m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

    _≡⟨_⟩-≤_ : ∀ (m : ℕ) {n p : ℕ}
      → m ≡ n
      → n ≤ p
        -----
      → m ≤ p
    m ≡⟨ refl ⟩-≤ n≤p = n≤p

    _∎-≤ : ∀ (n : ℕ)
        -----
      → n ≤ n
    n ∎-≤ = ≤-refl

  open ≤-Reasoning

  +-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
      -------------
    → n + p ≤ n + q
  +-monoʳ-≤ zero p q p≤q =
    begin-≤
      zero + p
    ≤⟨ p≤q ⟩
      zero + q
    ∎-≤
  +-monoʳ-≤ (suc n) p q p≤q =
    begin-≤
      (suc n) + p
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
      (suc n) + q
    ∎-≤

  +-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
      -------------
    → m + p ≤ n + p
  +-monoˡ-≤ m n p m≤n =
    begin-≤
      m + p
    ≡⟨ +-comm m p ⟩-≤
      p + m
    ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
      p + n
    ≡⟨ +-comm p n ⟩-≤
      n + p
    ∎-≤

  +-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
      -------------
    → m + p ≤ n + q
  +-mono-≤ m n p q m≤n p≤q =
    begin-≤
      m + p
    ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
      n + p
    ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
      n + q
    ∎-≤
```




## Isomorphism

```
module Isomorphism where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; cong-app; sym)
  open Eq.≡-Reasoning
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc; +-assoc)
```


```
  open import plfa.part1.Isomorphism
    hiding (≃-implies-≲; _⇔_)
```

#### Exercise `≃-implies-≲` (practice)

Show that every isomorphism implies an embedding.
```agda
  postulate
    ≃-implies-≲ : ∀ {A B : Set}
      → A ≃ B
        -----
      → A ≲ B
```

```agda
  -- Your code goes here
```

#### Exercise `_⇔_` (practice) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows:
```agda
  record _⇔_ (A B : Set) : Set where
    field
      to   : A → B
      from : B → A
```
Show that equivalence is reflexive, symmetric, and transitive.

```agda
  -- Your code goes here
```

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin](/Naturals/#Bin) and
[Bin-laws](/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
```agda
  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (x O) = x I
  inc (x I) = (inc x) O

  to : ℕ → Bin
  to 0 = ⟨⟩ O
  to (suc x) = inc (to x)

  from : Bin → ℕ
  from ⟨⟩ = 0
  from (x O) = 2 * from x
  from (x I) = 2 * from x + 1

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

  ℕ≲Bin : ℕ ≲ Bin
  ℕ≲Bin =
    record
      { to = to
      ; from = from
      ; from∘to = from-to
      }
```

Why do `to` and `from` not form an isomorphism?


## Connectives

```
module Connectives where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning
  open import Data.Nat using (ℕ)
  open import Function using (_∘_)
  open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
  open plfa.part1.Isomorphism.≃-Reasoning
```


```
  open import plfa.part1.Connectives
    hiding (⊎-weak-×; ⊎×-implies-×⊎)
```

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

```agda
  record _⇔_ (A B : Set) : Set where
    field
      to   : A → B
      from : B → A
  open _⇔_

  ⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
  ⇔≃× =
    record
      { to = λ{ a⇔b → ⟨ to a⇔b , from a⇔b ⟩ }
      ; from = λ{ abxba → record { to   = proj₁ abxba
                                 ; from = proj₂ abxba 
                                 } }
      ; from∘to = λ{ a⇔b → refl }                       
      ; to∘from = λ{ abxba → 
          begin
            ⟨ proj₁ abxba , proj₂ abxba ⟩
          ≡⟨ η-× abxba ⟩
            abxba
          ∎ }
      }
```


#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
```agda
  postulate
    ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
```
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

```agda
  -- Your code goes here
```


#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
```agda
  postulate
    ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
```
Does the converse hold? If so, prove; if not, give a counterexample.

```agda
  -- Your code goes here
```



## Negation

```
module Negation where
```

## Imports

```agda
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_)
  open import plfa.part1.Isomorphism using (_≃_; extensionality)
```


```
  open import plfa.part1.Negation
    hiding (Stable)
```

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality](/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

```agda
  -- Your code goes here
```


#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy](/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

```agda
  -- Your code goes here
```

#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

```agda
  -- Your code goes here
```


Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

```agda
  -- Your code goes here
```


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
```agda
  Stable : Set → Set
  Stable A = ¬ ¬ A → A
```
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

```agda
  -- Your code goes here
```


## Quantifiers

```
module Quantifiers where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Relation.Nullary using (¬_)
  open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import plfa.part1.Isomorphism using (_≃_; extensionality)
```


```
  open import plfa.part1.Quantifiers
    hiding (∀-distrib-×; ⊎∀-implies-∀⊎; ∃-distrib-⊎; ∃×-implies-×∃; ∃¬-implies-¬∀; Tri)
```

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```agda
  postulate
    ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
      (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```agda
  postulate
    ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
      (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
```agda
  data Tri : Set where
    aa : Tri
    bb : Tri
    cc : Tri
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.


#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```agda
  postulate
    ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
      ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```agda
  postulate
    ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
      ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```agda
  -- Your code goes here
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```agda
  -- Your code goes here
```


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```agda
  postulate
    ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
      → ∃[ x ] (¬ B x)
        --------------
      → ¬ (∀ x → B x)
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ] Can b`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

```agda
  -- Your code goes here
```


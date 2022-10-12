
```agda
module test where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; cong-app)
  open Eq.≡-Reasoning

  open import plfa.part1.Induction
  open import Data.Nat using (_≤_; z≤n; s≤s; ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (≤-refl; ≤-trans; +-comm; +-identity)

  +-comm′' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm′' zero    n  rewrite +-identity n             =  refl
  +-comm′' (suc m) n  rewrite +-suc n m | +-comm′' m n  =  refl

```

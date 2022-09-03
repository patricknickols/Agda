{-# OPTIONS --exact-split #-}

module plfa.part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

seven : ℕ

{-# BUILTIN NATURAL ℕ #-}

seven = 7

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

{-# BUILTIN NATTIMES _*_ #-}

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

infixl 6 _+_ _∸_
infixl 7 _*_

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O 
inc (x O) = x I
inc (x I I) = (inc x) O O
inc (x O I) = x I O


to : ℕ → Bin
to zero = (⟨⟩ O)
to (suc m) = inc (to m) 

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

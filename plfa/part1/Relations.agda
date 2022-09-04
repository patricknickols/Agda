module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      -----------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
      -------------
    → m ≤ n
      -------------
    → suc m ≤ suc n

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
    -----------------
  → suc m ≤ suc n
    --------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
    ------------------
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    -----------------
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
    -------------------
  → m ≤ n → n ≤ p
    -------------
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
    -------------------
  → m ≤ n → n ≤ m
    -------------
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
    m ≤ n → Total m n

  flipped :
    n ≤ m → Total m n
  
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
    ------
  → p ≤ q
    ----------
  → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
    -------
  → m ≤ n
    ------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n → p ≤ q
    --------------
  → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (m n p : ℕ)
    -----
  → m ≤ n
    -------------
  → m * p ≤ n * p

*-monoʳ-≤ m n p z≤n = z≤n
*-monoʳ-≤ (suc m) (suc n) p (s≤s m≤n) = +-monoʳ-≤ p (m * p) (n * p) (*-monoʳ-≤ m n p m≤n)

*-monoˡ-≤ : ∀ (m n p : ℕ)
    --------
  → m ≤ n
    --------
  → p * m ≤ p * n
*-monoˡ-≤ m n p m≤n rewrite *-comm p m | *-comm p n = *-monoʳ-≤ m n p m≤n
  
*-mono-≤ : ∀ (m n p q : ℕ)
    ----------
  → m ≤ n → p ≤ q
    ----------
  → m * p ≤ n * q

*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoʳ-≤ m n p m≤n) (*-monoˡ-≤ p q n p≤q)


infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
       -------------------
     → zero < suc n

  s<s : ∀ {m n : ℕ}
      ---------------------
    → m < n
      ---------------------
    → suc m < suc n

<-suc : ∀ (n : ℕ) → n < suc n
<-suc zero = z<s
<-suc (suc n) = s<s (<-suc n)

inv-s<s : ∀ {m n : ℕ}
    -------------
  → suc m < suc n
    -------------
  → m < n

inv-s<s (s<s m<n) = m<n


<-trans : ∀ {m n p : ℕ}
    -------------
  → m < n → n < p
    -------------
  → m < p

<-trans {p = suc a} z<s _ = z<s
<-trans {suc m} {suc n} {suc p} (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Related (m n : ℕ) : Set where

  less-than :
    m < n → Related m n

  equal :
    m ≡ n → Related m n

  more-than :
    n < m → Related m n

suc-related : ∀ (m n : ℕ)
    -----------
  → Related m n
    -----------------------
  → Related (suc m) (suc n)

suc-related m n (equal m≡n) = equal (cong suc m≡n)
suc-related m n (less-than m<n) = less-than (s<s m<n) 
suc-related m n (more-than m>n) = more-than (s<s m>n)

trichotomy : ∀ (m n : ℕ) → Related m n
trichotomy zero zero = equal refl
trichotomy zero (suc n) = less-than (z<s)
trichotomy (suc m) zero = more-than (z<s)
trichotomy (suc m) (suc n) = suc-related m n (trichotomy m n)

+-monoʳ-< : ∀ (m n p : ℕ)
    -------
  → m < n
    --------------
  → p + m < p + n

+-monoʳ-< m n zero m<n = m<n
+-monoʳ-< m n (suc p) m<n = s<s (+-monoʳ-< m n p m<n)

+-monoˡ-< : ∀ (m n p : ℕ)
    ----------
  → m < n
    --------------
  → m + p < n + p

+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< m n p m<n

+-mono-< : ∀ (m n p q : ℕ)
    ---------------
  → m < n → p < q
    ---------------
  → m + p < n + q

+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< p q n p<q)

≤-only-if-< : ∀ (m n : ℕ)
    ---------
  → suc m ≤ n
    ---------
  → m < n

≤-only-if-< zero (suc n) _ = z<s
≤-only-if-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-only-if-< m n m≤n)

≤-if-< : ∀ (m n : ℕ)
    ----------
  → m < n
    ----------
  → suc m ≤ n

≤-if-< zero (suc n) m<n = s≤s z≤n
≤-if-< (suc m) (suc n) (s<s m<n) = s≤s (≤-if-< m n m<n)

data even : ℕ → Set
data odd : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc : ∀ {n : ℕ}
      -----
    → odd n
      -----------
    → even (suc n)

data odd where

  suc : ∀ {n : ℕ}
      ------
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
    ---------------
  → even m → even n
    ---------------
  → even (m + n)

o+e≡e : ∀ {m n : ℕ}
    -----
  → odd m → even n
    --------------
  → odd (m + n)

e+e≡e zero n-even = n-even
e+e≡e (suc m-odd) n-even = suc (o+e≡e m-odd n-even)
o+e≡e (suc m-even) n-even = suc (e+e≡e m-even n-even)

o+o≡e : ∀ {m n : ℕ}
    -------------
  → odd m → odd n
    -------------
  → even (m + n)

o+o≡e {suc m} {suc n} (suc m-even) (suc n-even) rewrite +-comm m (suc n) = suc (suc (e+e≡e n-even m-even))


module misc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s; _<_)
open import Data.Bool using (Bool; true; false)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)


refl-≤ : ∀ {n : ℕ} → n ≤ n
antisym-≤ : ∀ {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
trans-≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

refl-≤ {zero} = z≤n
refl-≤ {suc n} = s≤s (refl-≤ {n})

antisym-≤ z≤n z≤n = Eq.refl
antisym-≤ (s≤s n≤m) (s≤s m≤n) = cong suc (antisym-≤ n≤m m≤n)

trans-≤ z≤n z≤n = z≤n
trans-≤ z≤n (s≤s n≤p) = z≤n
trans-≤ (s≤s m≤n) (s≤s n≤p) = s≤s (trans-≤ m≤n n≤p)

n≤sucn : ∀ (n : ℕ) → n ≤ suc n
n≤sucn zero = _≤_.z≤n
n≤sucn (suc n) = _≤_.s≤s (n≤sucn n)

n≤k+n : ∀ (n k : ℕ) → n ≤ k + n
n≤k+n zero _ = _≤_.z≤n
n≤k+n (suc n) zero = _≤_.s≤s (n≤k+n n zero)
n≤k+n (suc n) (suc k) = _≤_.s≤s (trans-≤ (n≤sucn n) (n≤k+n (suc n) k))

max : ℕ → ℕ → ℕ
max zero b = b
max a zero = a
max (suc a) (suc b) = suc (max a b) 

max-sym : (a b : ℕ) → max a b ≡ max b a
max-sym zero zero = Eq.refl
max-sym zero (suc b) = Eq.refl
max-sym (suc a) zero = Eq.refl
max-sym (suc a) (suc b) = Eq.cong suc (max-sym a b)

a≤max-a-b : {b : ℕ} (a : ℕ) → a ≤ (max a b)
a≤max-a-b zero = z≤n
a≤max-a-b {zero} (suc a) = refl-≤
a≤max-a-b {suc b} (suc a) = s≤s (a≤max-a-b {b} a)

b≤max-a-b : {a : ℕ} (b : ℕ) → b ≤ (max a b)
b≤max-a-b zero = z≤n
b≤max-a-b {zero} (suc b) = refl-≤
b≤max-a-b {suc a} (suc b) = s≤s (b≤max-a-b {a} b)

a≤b≡c→a≤c : {a b c : ℕ} → a ≤ b → b ≡ c → a ≤ c
a≤b≡c→a≤c a≤b Eq.refl = a≤b

a≤b≡c→a≤c′ : {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ⊑ b → b ≡ c → a ⊑ c
a≤b≡c→a≤c′ a≤b Eq.refl = a≤b

a≡b≤c→a≤c : {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ≡ b → b ⊑ c → a ⊑ c
a≡b≤c→a≤c Eq.refl b≤c = b≤c

≤-dichotomy : {m n : ℕ} → (m ≤ n) ⊎ (n ≤ m)
≤-dichotomy {zero} {n} = inj₁ z≤n
≤-dichotomy {suc m} {zero} = inj₂ z≤n
≤-dichotomy {suc m} {suc n} with ≤-dichotomy {m} {n}
...                         | inj₁ m≤n  = inj₁ (s≤s m≤n)
...                         | inj₂ n≤m = inj₂ (s≤s n≤m)

≤-dichotomy′ : {m n : ℕ} → (m < n) ⊎ (n ≤ m)
≤-dichotomy′ {m} {zero} = inj₂ z≤n
≤-dichotomy′ {zero} {suc n} = inj₁ (s≤s z≤n)
≤-dichotomy′ {suc m} {suc n} with ≤-dichotomy′ {m} {n}
...                         | inj₁ x = inj₁ (s≤s x)
...                         | inj₂ y = inj₂ (s≤s y)

sa<sb→a<b : {m n : ℕ} → suc m < suc n → m < n
sa<sb→a<b (s≤s x) = x


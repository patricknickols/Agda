module debruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import posets2 using (domain; flat-domain; chain; monotone-fun; inj; x≼x; z≼n; function-domain; cont-fun; ⊥₁; tarski-fix; least-pre-fixed; domain-product; poset; chain-map; chain-complete-flat-domain-pos-B; tarski-continuous; product-equality)
open import useful-functions using (ℕ⊥; 𝔹⊥; _∘_; constant-fun-is-cont; pair-f; extend-function; ev-cont; if-cont; cur-cont; domain-dependent-projection)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) 

infix 4 _⊢_
infix 4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix 5 ƛ_
infix 5 μ_
infixl 7 _·_
infix 8 `suc_
infix 9 `_
infix 9 S_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
  `bool : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A


data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

  `zero : ∀ {Γ}
    → Γ ⊢ `ℕ

  `is-zero_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `bool

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ

  `pred_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ

  `true : ∀ {Γ}
    → Γ ⊢ `bool

  `false : ∀ {Γ}
    → Γ ⊢ `bool

  if_then_else_ : ∀ {Γ A}
    → Γ ⊢ `bool
    → Γ ⊢ A
    → Γ ⊢ A
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ ⊢ A ⇒ A
    → Γ ⊢ A

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsucc : {n : ℕ} → Fin n → Fin (suc n)

conv : {n : ℕ} → Fin n → ℕ
conv fzero = 0
conv (fsucc x) = suc (conv x)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero} (s≤s z≤n) = A
lookup {(Γ , _)} {suc n} (s≤s p) = lookup p

lookup₂ : {Γ : Context} → {n : Fin (length Γ)} → Type
lookup₂ {(_ , A)} {fzero} = A
lookup₂ {(Γ , _)} {fsucc x} = lookup₂ {Γ} {x}

count : ∀ {Γ} → {n : Fin (length Γ)} → Γ ∋ lookup₂ {Γ} {n}
count {Γ , x} {fzero} = Z
count {Γ , x} {fsucc n} = S (count {Γ} {n})

ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S ρ x

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ N) = ƛ rename (ext ρ) N
rename ρ (L · M) = (rename ρ L) · (rename ρ M)
rename ρ `zero = `zero
rename ρ (`suc M) = `suc (rename ρ M)
rename ρ (μ N) = μ (rename ρ N)
rename ρ `true = `true
rename ρ `false = `false
rename ρ (`is-zero y) = `is-zero (rename ρ y)
rename ρ (`pred y) = `pred rename ρ y
rename ρ (if b then x else y) = if (rename ρ b) then (rename ρ x) else (rename ρ y)


exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z     = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ L) = ƛ subst (exts σ) L
subst σ (L · M) = (subst σ L) · (subst σ M) 
subst σ `zero = `zero
subst σ (`suc x) = `suc (subst σ x)
subst σ (μ L) = μ subst σ L
subst σ `true = `true
subst σ `false = `false
subst σ (`is-zero x) = `is-zero (subst σ x)
subst σ (`pred x) = `pred (subst σ x)
subst σ (if b then x else y) = if (subst σ b) then (subst σ x) else (subst σ y)

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z     = M
  σ (S x) = ` x


data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)

  V-zero : ∀ {Γ}
    → Value (`zero {Γ})

  V-true : ∀ {Γ}
    → Value (`true {Γ})

  V-false : ∀ {Γ}
    → Value (`false {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
    → Value (`suc V)

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A} 
    → Value V
    → M —→ M′
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
    → `suc M —→ `suc M′

  ξ-pred : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
    → `pred M —→ `pred M′

  β-pred₁ : ∀ {Γ : Context}
    → `pred (`zero) —→ `zero {Γ}

  β-pred₂ : ∀ {Γ : Context} {M : Γ ⊢ `ℕ}
    → Value M
    → `pred (`suc M) —→ M

  ξ-if : ∀ {Γ A} {B B′ : Γ ⊢ `bool} {x y : Γ ⊢ A}
    → B —→ B′
    → if B then x else y —→ if B′ then x else y
  
  β-if₁ : ∀ {Γ A} {x y : Γ ⊢ A}
    → if `true then x else y —→ x

  β-if₂ : ∀ {Γ A} {x y : Γ ⊢ A}
    → if `false then x else y —→ y

  β-μ : ∀ {Γ A} {N : Γ ⊢ A ⇒ A}
    → μ N —→ N · (μ N)

  ξ-is-zero : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
    → `is-zero M —→ `is-zero M′

  β-is-zero₁ : ∀ {Γ}
    → `is-zero `zero —→ `true {Γ}

  β-is-zero₂ : ∀ {Γ} {M : Γ ⊢ `ℕ}
    → Value M
    → `is-zero (`suc M) —→ `false 

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
    → Progress M

  done :
      Value M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (ƛ M) = done V-ƛ

progress (L · M)  with progress L
...    | step L—→L′               = step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M 
...        | step M—→M′           = step (ξ-·₂ V-ƛ M—→M′)
...        | done VM              = step (β-ƛ VM)

progress `zero = done V-zero

progress (`is-zero M) with progress M
...    | step M—→M′      = step (ξ-is-zero M—→M′)
...    | done (V-zero)   = step β-is-zero₁
...    | done (V-suc VM) = step (β-is-zero₂ VM)

progress (`suc M) with progress M
...    | step M—→M′ = step (ξ-suc M—→M′)
...    | done VM    = done (V-suc VM)

progress (`pred M) with progress M
...    | step M—→M′ = step (ξ-pred M—→M′)
...    | done V-zero = step β-pred₁
...    | done (V-suc VM) = step (β-pred₂ VM)


progress `true = done V-true
progress `false = done V-false

progress (if B then M else N) with progress B
...    | step L—→L′   = step (ξ-if L—→L′)
...    | done V-true  = step β-if₁
...    | done V-false = step β-if₂
progress (μ M) = step β-μ


infix 3 _⊢_↓_

data _⊢_↓_ : ∀{Γ A} → Γ ⊢ A → Set where

⟦_⟧ : Type → domain
⟦ `ℕ ⟧ = ℕ⊥
⟦ `bool ⟧ = 𝔹⊥
⟦ τ ⇒ τ′ ⟧ = function-domain ⟦ τ ⟧ ⟦ τ′ ⟧


data ⊥-set : Set where
  ⊥₂ : ⊥-set

data _⊥≼_ : ⊥-set → ⊥-set → Set where
  ⊥≼⊥ : ⊥₂ ⊥≼ ⊥₂ 

⊥≼-refl : {a : ⊥-set} → a ⊥≼ a
⊥≼-refl {⊥₂} = ⊥≼⊥

⊥≼-antisym : {a b : ⊥-set} → a ⊥≼ b → b ⊥≼ a → a ≡ b
⊥≼-antisym ⊥≼⊥ ⊥≼⊥ = refl

⊥≼-trans : {a b c : ⊥-set} → a ⊥≼ b → b ⊥≼ c → a ⊥≼ c
⊥≼-trans ⊥≼⊥ ⊥≼⊥ = ⊥≼⊥

⊥-is-top : ∀ {a : ⊥-set} → a ⊥≼ ⊥₂
⊥-is-top {⊥₂} = ⊥≼⊥

context-⟦_⟧ : Context → domain
context-⟦ ∅ ⟧ = record { pos = record
                         { A = ⊥-set
                         ; R = _⊥≼_
                         ; reflexive = ⊥≼-refl
                         ; antisymmetric = ⊥≼-antisym
                         ; transitive = ⊥≼-trans
                         }
                       ; chain-complete = λ c → record
                         { ⊔ = ⊥₂
                         ; lub1 = λ {n} → ⊥-is-top
                         ; lub2 = λ { {⊥₂} → λ x → ⊥≼⊥}
                         }
                       ; bottom = record
                         { ⊥ = ⊥₂
                         ; ⊥-is-bottom = λ { {⊥₂} → ⊥≼⊥ }
                         }
                       }

context-⟦ Γ , x ⟧ = domain-product context-⟦ Γ ⟧ ⟦ x ⟧

context₂-⟦_⟧ : Context → domain
context₂-⟦ Γ ⟧ = posets2.domain-dependent-product (Fin (length Γ)) (λ x → ⟦ lookup₂ {Γ} {x} ⟧)

s⊥ : cont-fun ℕ⊥ ℕ⊥
s : ℕ → poset.A (domain.pos ℕ⊥)
s x = inj (suc x)
s⊥ = extend-function s

z⊥ : cont-fun ℕ⊥ 𝔹⊥
z : ℕ → poset.A (domain.pos 𝔹⊥)
z zero = inj true
z (suc n) = inj false
z⊥ = extend-function z

p⊥ : cont-fun ℕ⊥ ℕ⊥
p : ℕ → poset.A (domain.pos ℕ⊥)
p zero = ⊥₁
p (suc n) = inj n
p⊥ = extend-function p


constant-fun : ∀ {Γ} → (B : Set) → B → cont-fun context-⟦ Γ ⟧ (flat-domain B)
constant-fun B b = constant-fun-is-cont b


⟦_⊢′_⟧ : ∀ {A} → (Γ : Context) → (M : Γ ⊢ A) → cont-fun context-⟦ Γ ⟧ ⟦ A ⟧
⟦ Γ ⊢′ `zero ⟧ = constant-fun {Γ} ℕ 0
⟦ Γ ⊢′ `true ⟧ = constant-fun {Γ} Bool true
⟦ Γ ⊢′ `false ⟧ = constant-fun {Γ} Bool false
⟦ Γ ⊢′ M₁ · M₂ ⟧ = ev-cont ∘ (pair-f ⟦ Γ ⊢′ M₁ ⟧ ⟦ Γ ⊢′ M₂ ⟧) 
⟦ Γ ⊢′ `is-zero N ⟧ = z⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ `suc N ⟧ = s⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ `pred N ⟧ = p⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ if M₁ then M₂ else M₃ ⟧ = if-cont ∘ (pair-f ⟦ Γ ⊢′ M₁ ⟧ (pair-f ⟦ Γ ⊢′ M₂ ⟧ ⟦ Γ ⊢′ M₃ ⟧))
⟦ Γ ⊢′ ` x ⟧ = {!!}
⟦ Γ ⊢′ ƛ_ {A = A} M ⟧ = cur-cont ⟦ Γ , A ⊢′ M ⟧
⟦ Γ ⊢′ μ M ⟧ = tarski-continuous ∘ ⟦ Γ ⊢′ M ⟧ 

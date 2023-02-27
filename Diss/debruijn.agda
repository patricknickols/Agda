module debruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import posets2 using (domain; flat-domain; chain; monotone-fun; inj; x≼x; function-domain; cont-fun; ⊥₁; tarski-fix; least-pre-fixed)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

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
infix 9 #_

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

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero} (s≤s z≤n) = A
lookup {(Γ , _)} {suc n} (s≤s p) = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = Z
count {Γ , _} {(suc n)} (s≤s p) = S (count p)

#_ : ∀ {Γ} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ ⊢ lookup (toWitness n∈Γ)

#_ n {n∈Γ} = ` count (toWitness n∈Γ)

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

ℕ⊥ : domain
𝔹⊥ : domain

ℕ⊥ = flat-domain ℕ
𝔹⊥ = flat-domain Bool

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

context-⟦_⟧ : Context → domain
context-⟦ ∅ ⟧ = record { pos = record
                                 { A = ⊥-set
                                 ; R = _⊥≼_
                                 ; reflexive = ⊥≼-refl
                                 ; antisymmetric = ⊥≼-antisym
                                 ; transitive = ⊥≼-trans
                                 }
                       ; chain-complete = {!!}
                       ; bottom = {!!}
                       }
context-⟦ x , x₁ ⟧ = record { pos = {!!} ; chain-complete = {!!} ; bottom = {!!} }


constant-fun-is-cont : ∀ {B : Set} → {D : domain} → B → cont-fun D (flat-domain B)
constant-fun-is-cont b = record { mon = record { g = λ x → inj b
                                               ; mon = λ x → x≼x }
                                ; lub-preserve = λ c → {!!}
                                }


constant-fun : ∀ {Γ} → (B : Set) → B → cont-fun context-⟦ Γ ⟧ (flat-domain B)
constant-fun B b = constant-fun-is-cont b

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


⟦_⊢′_⟧ : ∀ {A} → (Γ : Context) → (M : Γ ⊢ A) → cont-fun context-⟦ Γ ⟧ ⟦ A ⟧
⟦ Γ ⊢′ `zero ⟧ = constant-fun {Γ} ℕ 0
⟦ Γ ⊢′ `true ⟧ = constant-fun {Γ} Bool true
⟦ Γ ⊢′ `false ⟧ = constant-fun {Γ} Bool false
⟦ Γ ⊢′ ` x ⟧ = record { mon = record { g = λ ρ → {!ρ!}
                                     ; mon = {!!}
                                     }
                      ; lub-preserve = {!!}
                      }
⟦ Γ ⊢′ ƛ M ⟧ = record { mon = record { g = λ ρ → record
                                                 { mon = record { g = λ d → {!!}
                                                                ; mon = {!!}
                                                                }
                                                 ; lub-preserve = {!!}
                                                 }
                                     ; mon = {!!} }
                      ; lub-preserve = {!!} }
⟦ Γ ⊢′ M₁ · M₂ ⟧ = record { mon = record { g = λ ρ → monotone-fun.g
                                                       (cont-fun.mon
                                                         (monotone-fun.g
                                                           (cont-fun.mon ⟦ Γ ⊢′ M₁ ⟧)
                                                        ρ)
                                                       ) (monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ M₂ ⟧)ρ)
                                         ; mon = {!!}
                                         }
                          ; lub-preserve = {!!}
                          }
⟦ Γ ⊢′ `is-zero N ⟧ = record { mon =
                        record {
                               g = λ ρ → case ((monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ N ⟧))ρ) of
                               λ { ⊥₁ → ⊥₁
                               ; (inj 0) → inj true
                               ; (inj (suc n)) → inj false }
                               ; mon = {!!}
                               }
                         ; lub-preserve = {!!}
                         }
⟦ Γ ⊢′ `suc N ⟧ = record { mon =
                    record {
                           g = λ ρ → case ((monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ N ⟧))ρ) of
                           λ { (inj n) → inj (suc n)
                             ; ⊥₁ → ⊥₁
                             }
                           ; mon = {!!}
                           }
                         ; lub-preserve = {!!}
                         }
⟦ Γ ⊢′ `pred N ⟧ = record { mon =
                    record {
                           g = λ ρ → case ((monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ N ⟧))ρ) of
                           λ { (inj 0) → ⊥₁
                             ; (inj (suc n)) → inj n
                             ; ⊥₁ → ⊥₁
                             }
                           ; mon = {!!}
                           }
                         ; lub-preserve = {!!}
                         }
⟦_⊢′_⟧ {A} Γ (if M₁ then M₂ else M₃) = record { mon =
                    record {
                           g = λ ρ → case ((monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ M₁ ⟧))ρ) of
                           λ { (inj true) → (monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ M₂ ⟧))ρ
                             ; (inj false) → (monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ M₃ ⟧))ρ
                             ; ⊥₁ → posets2.least-element.⊥ (domain.bottom ⟦ A ⟧)
                             }
                           ; mon = {!!}
                           }
                         ; lub-preserve = {!!}
                         }
⟦_⊢′_⟧ {A} Γ (μ M) = record
                     { mon = record
                       { g = λ ρ → posets2.pre-fixed.d (least-pre-fixed.lfp1 (tarski-fix ⟦ A ⟧ (monotone-fun.g (cont-fun.mon ⟦ Γ ⊢′ M ⟧)ρ)))
                       ; mon = {!!}
                       }
                     ; lub-preserve = {!!}
                     } 

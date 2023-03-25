module debruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import posets2
open import ev-cont using (ev-cont)
open import if-cont using (if-cont)
open import cur-cont using (cur-cont)
open import useful-functions using (ℕ⊥; 𝔹⊥; _∘_; constant-fun-is-cont; pair-f; extend-function; domain-dependent-projection)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) 

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain

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

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero} (s≤s z≤n) = A
lookup {(Γ , _)} {suc n} (s≤s p) = lookup p

lookup₂ : {Γ : Context} → (n : Fin (length Γ)) → Type
lookup₂ {(_ , A)} (fzero) = A
lookup₂ {(Γ , _)} (fsucc x) = lookup₂ {Γ} x

count : ∀ {Γ} → {n : Fin (length Γ)} → Γ ∋ lookup₂ {Γ} n
count {Γ , x} {fzero} = Z
count {Γ , x} {fsucc n} = S (count {Γ} {n})

conv : ∀ {x} → {Γ : Context} → (Γ ∋ x) → Fin (length Γ)
conv Z = fzero
conv (S Γ∋x) = fsucc (conv Γ∋x)

conv₂ : {y : ℕ} (x : ℕ) → x < y → Fin y
conv₂ zero (s≤s x<y) = fzero
conv₂ (suc x) (s≤s x<y) = fsucc (conv₂ x x<y) 

#_ : ∀ {Γ} → (n : Fin (length Γ)) → Γ ⊢ lookup₂ n
#_ n = ` (count {n = n}) 

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


⟦_⟧ : Type → domain
⟦ `ℕ ⟧ = ℕ⊥
⟦ `bool ⟧ = 𝔹⊥
⟦ τ ⇒ τ′ ⟧ = function-domain ⟦ τ ⟧ ⟦ τ′ ⟧

context-⟦_⟧ : Context → domain
context-⟦ Γ ⟧ = domain-dependent-product (Fin (length Γ)) (λ x → ⟦ lookup₂ {Γ} x ⟧)

helpful-lemma-chain : {Γ : Context} {A : Type} → chain (pos (domain-product context-⟦ Γ ⟧ ⟦ A ⟧)) → chain (pos (context-⟦ Γ , A ⟧))
g (monotone (helpful-lemma-chain c)) = λ x → λ {fzero → g (monotone c) x (fsucc fzero); (fsucc n) → g (monotone c) x fzero n}
mon (monotone (helpful-lemma-chain c)) a≤a′ fzero = mon (monotone c) a≤a′ (fsucc fzero)
mon (monotone (helpful-lemma-chain c)) a≤a′ (fsucc i) = mon (monotone c) a≤a′ (fzero) i 

helpful-lemma-blah : {Γ : Context} {A B : Type} → cont-fun (context-⟦ Γ , A ⟧) ⟦ B ⟧ → cont-fun (domain-product context-⟦ Γ ⟧ ⟦ A ⟧) ⟦ B ⟧
mon (helpful-lemma-blah f) = record { g = λ x → g (mon f) λ {fzero → x (fsucc fzero); (fsucc n) → x fzero n}
                                    ; mon = λ a≤a′ → mon (mon f) λ {fzero → a≤a′ (fsucc fzero); (fsucc n) → a≤a′ fzero n}
                                    }
lub-preserve (helpful-lemma-blah {Γ} {A} {B} f) c =
  begin
    g (mon (helpful-lemma-blah {Γ} {A} {B} f)) (⊔ (chain-complete (domain-product context-⟦ Γ ⟧ ⟦ A ⟧) c))
  ≡⟨ cong (g (mon f)) (dependent-function-extensionality (λ {fzero → refl; (fsucc n) → refl})) ⟩
    g (mon f) (⊔ (chain-complete context-⟦ Γ , A ⟧ (helpful-lemma-chain {Γ} {A} c)))
  ≡⟨ lub-preserve f (helpful-lemma-chain c) ⟩
    ⊔ (chain-complete ⟦ B ⟧ (chain-map (helpful-lemma-chain c) (mon f)))
  ≡⟨ same-f-same-lub {⟦ B ⟧}
       {chain-map (helpful-lemma-chain c) (mon f)}
       {chain-map c (mon (helpful-lemma-blah {Γ} {A} {B} f))}
       (function-extensionality
         (λ x → cong (g (mon f))
           (dependent-function-extensionality
             (λ {fzero → refl; (fsucc n) → refl}))))
   ⟩
    ⊔ (chain-complete ⟦ B ⟧ (chain-map c (mon (helpful-lemma-blah {Γ} {A} {B} f))))
  ∎


s⊥ : cont-fun ℕ⊥ ℕ⊥
s : ℕ → A (pos ℕ⊥)
s x = inj (suc x)
s⊥ = extend-function s

z⊥ : cont-fun ℕ⊥ 𝔹⊥
z : ℕ → A (pos 𝔹⊥)
z zero = inj true
z (suc n) = inj false
z⊥ = extend-function z

p⊥ : cont-fun ℕ⊥ ℕ⊥
p : ℕ → A (pos ℕ⊥)
p zero = inj zero
p (suc n) = inj n
p⊥ = extend-function p

p⊥-inv-s⊥ : {x : B⊥ ℕ} → g (mon p⊥) ((g (mon s⊥)) x) ≡ x
p⊥-inv-s⊥ {⊥₁} = refl
p⊥-inv-s⊥ {inj zero} = refl
p⊥-inv-s⊥ {inj (suc x)} = refl

constant-fun : ∀ {Γ} → (B : Set) → B → cont-fun context-⟦ Γ ⟧ (flat-domain B)
constant-fun B b = constant-fun-is-cont b

project-x′ : ∀ {x} → (Γ : Context) → (Γ∋x : Γ ∋ x) → cont-fun
                                                (domain-dependent-product (Fin (length Γ))
                                                  (λ x → ⟦ lookup₂ {Γ} x ⟧))
                                                ⟦ lookup₂ (conv Γ∋x) ⟧
project-x′ {x} Γ Γ∋x =  domain-dependent-projection (Fin (length Γ)) (λ x → ⟦ lookup₂ x ⟧) (conv Γ∋x)

project-x-lemma : ∀ {x} → {Γ : Context} → (Γ∋x : Γ ∋ x) → lookup₂ (conv Γ∋x) ≡ x
project-x-lemma Z = refl
project-x-lemma (S Γ∋x) = project-x-lemma Γ∋x

project-x : ∀ {x} → (Γ : Context) → (Γ∋x : Γ ∋ x) → cont-fun
                                                (domain-dependent-product (Fin (length Γ))
                                                  (λ x → ⟦ lookup₂ {Γ} x ⟧))
                                                ⟦ x ⟧
project-x Γ Γ∋x rewrite Eq.sym (project-x-lemma Γ∋x) = project-x′ Γ Γ∋x


⟦_⊢′_⟧ : ∀ {A} → (Γ : Context) → (M : Γ ⊢ A) → cont-fun context-⟦ Γ ⟧ ⟦ A ⟧
⟦ Γ ⊢′ `zero ⟧ = constant-fun {Γ} ℕ 0
⟦ Γ ⊢′ `true ⟧ = constant-fun {Γ} Bool true
⟦ Γ ⊢′ `false ⟧ = constant-fun {Γ} Bool false
⟦ Γ ⊢′ M₁ · M₂ ⟧ = ev-cont ∘ (pair-f ⟦ Γ ⊢′ M₁ ⟧ ⟦ Γ ⊢′ M₂ ⟧) 
⟦ Γ ⊢′ `is-zero N ⟧ = z⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ `suc N ⟧ = s⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ `pred N ⟧ = p⊥ ∘ ⟦ Γ ⊢′ N ⟧
⟦ Γ ⊢′ if M₁ then M₂ else M₃ ⟧ = if-cont ∘ (pair-f ⟦ Γ ⊢′ M₁ ⟧ (pair-f ⟦ Γ ⊢′ M₂ ⟧ ⟦ Γ ⊢′ M₃ ⟧))
⟦ Γ ⊢′ ` x ⟧ = project-x Γ x
⟦ Γ ⊢′ ƛ_ {A = A} {B} M ⟧ = cur-cont (helpful-lemma-blah {Γ} {A} {B} ⟦ Γ , A ⊢′ M ⟧)
⟦ Γ ⊢′ μ M ⟧ = tarski-continuous ∘ ⟦ Γ ⊢′ M ⟧ 

⟦_⟧-program : ∀ {T} → (M : ∅ ⊢ T) → A (pos ⟦ T ⟧)
⟦_⟧-program M = g (mon ⟦ ∅ ⊢′ M ⟧) λ() 

zero-right : ⟦ `zero ⟧-program ≡ (inj zero)
zero-right = refl


--⟦ μ (ƛ (`suc (# fzero))) ⟧-program ≡ ⊥₁
--⟦ μ (ƛ (`pred (# fzero))) ⟧-program ≡ inj zero
--g (mon (⟦ μ (ƛ_ {A = `ℕ ⇒ `ℕ } (ƛ_  {A = `ℕ} (if (`is-zero (# fzero)) then (`suc `zero) else (# (fsucc fzero) · (`pred (# fzero)))))) ⟧-program))

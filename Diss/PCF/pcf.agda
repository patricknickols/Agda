module PCF.pcf where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) 

open import DomainTheory.BasicObjects.posets-etc
open import DomainTheory.BasicObjects.theorems
open import DomainTheory.ContinuousFunctions.ev-cont using (ev-cont)
open import DomainTheory.ContinuousFunctions.if-cont using (if-cont)
open import DomainTheory.ContinuousFunctions.cur-cont using (cur-cont)
open import DomainTheory.ContinuousFunctions.fix-cont using (tarski-continuous)

open import misc


open poset
open domain
open monotone-fun
open cont-fun
open lub

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

lookup : {Γ : Context} → (n : Fin (length Γ)) → Type
lookup {(_ , A)} (fzero) = A
lookup {(Γ , _)} (fsucc x) = lookup {Γ} x

count : ∀ {Γ} → {n : Fin (length Γ)} → Γ ∋ lookup {Γ} n
count {Γ , x} {fzero} = Z
count {Γ , x} {fsucc n} = S (count {Γ} {n})

conv : ∀ {x} → {Γ : Context} → (Γ ∋ x) → Fin (length Γ)
conv Z = fzero
conv (S Γ∋x) = fsucc (conv Γ∋x)

#_ : ∀ {Γ} → (n : Fin (length Γ)) → Γ ⊢ lookup n
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


σ : ∀ {Γ B} {M : Γ ⊢ B} → ({A₁ : Type} → Γ , B ∋ A₁ → Γ ⊢ A₁)
σ {M = M} Z = M
σ (S x)     = ` x

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} (σ {Γ} {B} {M}) N


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

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
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
...    | step L—→L′  = step (ξ-·₁ L—→L′)
...    | done V-ƛ    = step β-ƛ

progress `zero = done V-zero

progress (`is-zero M) with progress M
...    | step M—→M′      = step (ξ-is-zero M—→M′)
...    | done (V-zero)   = step β-is-zero₁
...    | done (V-suc VM) = step (β-is-zero₂ VM)

progress (`suc M) with progress M
...    | step M—→M′ = step (ξ-suc M—→M′)
...    | done VM    = done (V-suc VM)

progress (`pred M) with progress M
...    | step M—→M′      = step (ξ-pred M—→M′)
...    | done V-zero     = step β-pred₁
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
context-⟦ Γ ⟧ = domain-dependent-product (Fin (length Γ)) (λ x → ⟦ lookup {Γ} x ⟧)

unconcat : {Γ : Context} {τ : Type} → cont-fun context-⟦ Γ , τ ⟧ (domain-product context-⟦ Γ ⟧ ⟦ τ ⟧)
g (mon unconcat) x (fzero) i = x (fsucc i)
g (mon unconcat) x (fsucc fzero) = x fzero
mon (mon unconcat) x fzero i = x (fsucc i)
mon (mon unconcat) x (fsucc fzero) = x fzero
lub-preserve unconcat c = dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl})


concat : {Γ : Context} {τ : Type} → cont-fun (domain-product context-⟦ Γ ⟧ ⟦ τ ⟧) context-⟦ Γ , τ ⟧
g (mon concat) x fzero = x (fsucc fzero)
g (mon concat) x (fsucc n) = x fzero n
mon (mon concat) x fzero = x (fsucc fzero)
mon (mon concat) x (fsucc i) = x (fzero) i
lub-preserve concat c = dependent-function-extensionality (λ {fzero → refl; (fsucc n) → refl}) 

{-
helpful-lemma-chain : {Γ : Context} {A : Type} → chain (pos (domain-product context-⟦ Γ ⟧ ⟦ A ⟧)) → chain (pos (context-⟦ Γ , A ⟧))
g (helpful-lemma-chain c) x = λ {fzero → g c x (fsucc fzero); (fsucc n) → g c x fzero n}
mon (helpful-lemma-chain c) a≤a′ fzero = mon c a≤a′ (fsucc fzero)
mon (helpful-lemma-chain c) a≤a′ (fsucc i) = mon c a≤a′ (fzero) i 
-}
helpful-lemma-blah : {Γ : Context} {A B : Type} → cont-fun (context-⟦ Γ , A ⟧) ⟦ B ⟧ → cont-fun (domain-product context-⟦ Γ ⟧ ⟦ A ⟧) ⟦ B ⟧
helpful-lemma-blah f = f ∘ concat
{-
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
-}

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
                                                  (λ x → ⟦ lookup {Γ} x ⟧))
                                                ⟦ lookup (conv Γ∋x) ⟧
project-x′ {x} Γ Γ∋x =  domain-dependent-projection (Fin (length Γ)) (λ x → ⟦ lookup x ⟧) (conv Γ∋x)
{-
project-x-lemma : ∀ {x} → {Γ : Context} → (Γ∋x : Γ ∋ x) → lookup₂ (conv Γ∋x) ≡ x
project-x-lemma Z = refl
project-x-lemma (S Γ∋x) = project-x-lemma Γ∋x
-}
project-x : ∀ {x} → (Γ : Context) → (Γ∋x : Γ ∋ x) → cont-fun
                                                (domain-dependent-product (Fin (length Γ))
                                                  (λ x → ⟦ lookup {Γ} x ⟧))
                                                ⟦ x ⟧
--project-x Γ Γ∋x rewrite Eq.sym (project-x-lemma Γ∋x) = project-x′ Γ Γ∋x

restrict-context-cont : {Γ : Context} {X : Type} → cont-fun context-⟦ Γ , X ⟧ context-⟦ Γ ⟧
restrict-context-cont = π₁ ∘ unconcat

project-x (Γ , τ) Z = project-x′ (Γ , τ) Z
project-x (Γ , τ) (S Γ∋x) = project-x Γ Γ∋x ∘ restrict-context-cont

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


data _-→*_ : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl-→* : ∀ {Γ} {A}
    → {t : Γ ⊢ A}
    → t -→* t
  single : ∀ {Γ} {A}
    → {t  : Γ ⊢ A}
    → {t′ : Γ ⊢ A}
    → t —→ t′
    → t -→* t′
  trans-→* : ∀ {Γ} {A}
    → {t  : Γ ⊢ A}
    → {t′ : Γ ⊢ A}
    → {t″ : Γ ⊢ A}
    → (t -→* t′)
    → (t′ -→* t″)
    → (t -→* t″)

_⇓_ : ∀ {Γ} {A} → (M : Γ ⊢ A) → (V : Γ ⊢ A) → Set
M ⇓ V = M -→* V × Value V 

cong-suc : ∀ {Γ} {M V : Γ ⊢ `ℕ} → M -→* V → (`suc M) -→* (`suc V)
cong-suc refl-→* = refl-→*
cong-suc (single x) = single (ξ-suc x)
cong-suc (trans-→* x y) = trans-→* (cong-suc x) (cong-suc y)

cong-pred : ∀ {Γ} {M V : Γ ⊢ `ℕ} → M -→* V → (`pred M) -→* (`pred V)
cong-pred refl-→* = refl-→*
cong-pred (single x) = single (ξ-pred x)
cong-pred (trans-→* x y) = trans-→* (cong-pred x) (cong-pred y)

cong-zero : ∀ {Γ} {M V : Γ ⊢ `ℕ} → M -→* V → (`is-zero M) -→* (`is-zero V)
cong-zero refl-→* = refl-→*
cong-zero (single x) = single (ξ-is-zero x)
cong-zero (trans-→* x y) = trans-→* (cong-zero x) (cong-zero y)

cong-if : ∀ {Γ} {τ} {M V : Γ ⊢ `bool} {N N′ : Γ ⊢ τ} → M -→* V → (if M then N else N′) -→* (if V then N else N′)
cong-if refl-→* = refl-→*
cong-if (single x) = single (ξ-if x)
cong-if (trans-→* x y) = trans-→* (cong-if x) (cong-if y)

cong-app : ∀ {Γ} {A} {B} {M V : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} → M -→* V → (M · N) -→* (V · N)
cong-app refl-→* = refl-→*
cong-app (single x) = single (ξ-·₁ x)
cong-app (trans-→* x y) = trans-→* (cong-app x) (cong-app y)

fix-inversion : ∀ {Γ} {A} {M : Γ ⊢ A ⇒ A} {V : Γ ⊢ A} → (M · (μ M)) -→* V → (μ M) -→* V
fix-inversion refl-→* = trans-→* (single β-μ) (refl-→*)
fix-inversion (single x) = trans-→* (single β-μ) (single x)
fix-inversion (trans-→* x y) = trans-→* (single β-μ) (trans-→* x y)

suc-val-inversion : ∀ {Γ} {V : Γ ⊢ `ℕ} → Value (`suc V) → Value V
suc-val-inversion (V-suc x) = x

⇓-Val : ∀ {Γ} {A} {V : Γ ⊢ A} → Value V → V ⇓ V
⇓-succ : ∀ {Γ} {M : Γ ⊢ `ℕ} {V : Γ ⊢ `ℕ} → M ⇓ V → (`suc M) ⇓ (`suc V)
⇓-pred : ∀ {Γ} {M : Γ ⊢ `ℕ} {V : Γ ⊢ `ℕ} → M ⇓ (`suc V) → (`pred M) ⇓ V
⇓-zero₁ : ∀ {Γ} {M : Γ ⊢ `ℕ} → M ⇓ `zero → (`is-zero M) ⇓ `true
⇓-zero₂ : ∀ {Γ} {M : Γ ⊢ `ℕ} {V : Γ ⊢ `ℕ} → M ⇓ (`suc V) → (`is-zero M) ⇓ `false
⇓-if₁ : ∀ {Γ} {A} {M₁ : Γ ⊢ `bool} {M₂ M₃ V : Γ ⊢ A} → M₁ ⇓ `true → M₂ ⇓ V → (if M₁ then M₂ else M₃) ⇓ V
⇓-if₂ : ∀ {Γ} {A} {M₁ : Γ ⊢ `bool} {M₂ M₃ V : Γ ⊢ A} → M₁ ⇓ `false → M₃ ⇓ V → (if M₁ then M₂ else M₃) ⇓ V
⇓-cbn : ∀ {Γ} {A} {B} {M₁ : Γ ⊢ A ⇒ B} {M₁′ : Γ , A ⊢ B} {M₂ : Γ ⊢ A} {V : Γ ⊢ B} → M₁ ⇓ (ƛ M₁′) → (M₁′ [ M₂ ]) ⇓ V → (M₁ · M₂) ⇓ V 
⇓-fix : ∀ {Γ} {A} {M : Γ ⊢ A ⇒ A} {V : Γ ⊢ A} → (M · (μ M)) ⇓ V → (μ M) ⇓ V

⇓-Val val-v = ⟨ refl-→* , val-v ⟩
⇓-succ ⟨ M-→*V , val-v ⟩ = ⟨ cong-suc M-→*V , V-suc val-v ⟩
⇓-pred ⟨ M-→*sucV , val-sucV ⟩ = ⟨ trans-→* (cong-pred M-→*sucV) (single (β-pred₂ (suc-val-inversion val-sucV))) , suc-val-inversion val-sucV ⟩
⇓-zero₁ ⟨ M-→*0 , _ ⟩ = ⟨ trans-→* (cong-zero M-→*0) (single β-is-zero₁) , V-true ⟩
⇓-zero₂ ⟨ M-→*sucV , val-sucV ⟩ = ⟨ trans-→* (cong-zero M-→*sucV) (single (β-is-zero₂ (suc-val-inversion val-sucV))) , V-false ⟩
⇓-if₁ ⟨ M₁-→*true , _ ⟩ ⟨ M₂-→*V , val-v ⟩ = ⟨ trans-→* (trans-→* (cong-if M₁-→*true) (single β-if₁)) M₂-→*V , val-v ⟩
⇓-if₂ ⟨ M₁-→*false , _ ⟩ ⟨ M₃-→*V , val-v ⟩ = ⟨ trans-→* (trans-→* (cong-if M₁-→*false) (single β-if₂)) M₃-→*V , val-v ⟩
⇓-cbn ⟨ M₁-→*ƛM₁′ , val-ƛM₁′ ⟩ ⟨ M₁′[M₂]-→*V , val-v ⟩ = ⟨ trans-→* (trans-→* (cong-app M₁-→*ƛM₁′) (single β-ƛ)) M₁′[M₂]-→*V , val-v ⟩
⇓-fix ⟨ MμM-→*V , val-v ⟩ = ⟨ fix-inversion MμM-→*V , val-v ⟩


add : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
add = μ (ƛ (ƛ (ƛ (if `is-zero (` Z) then ` S Z else (` (S S Z) · `suc ` S Z · (`pred (` Z)))))))

times : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
times = μ (ƛ (ƛ (ƛ (if `is-zero (` Z) then `zero else (add · ` S Z · (` S S Z · ` S Z · (`pred (` Z))))))))

factorial : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
factorial = μ (ƛ (ƛ (if `is-zero (` Z) then (`suc `zero) else (times · ` Z · (` S Z · (`pred (` Z)))))))


record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ : Context} {τ : Type} (V : Γ ⊢ τ) : Set where
  done :
      Value V
    → Finished V

  out-of-gas :
    Finished V

data Steps {Γ : Context} {τ : Type} (M : Γ ⊢ τ) : Set where
  steps : ∀ {N}
    → M -→* N
    → Finished N
    → Steps M

eval : ∀ {A} → Gas → (L : ∅ ⊢ A) → Steps L
eval (gas zero) L = steps refl-→* out-of-gas
eval (gas (suc m)) L with progress L
... | done VL = steps refl-→* (done VL)
... | step {N} L-→N with eval (gas m) N
...     | steps N-→*V fin = steps (trans-→* (single L-→N) N-→*V) fin

_ : eval (gas 1000) (factorial · (`suc (`suc (`suc (`zero))))) ≡ {!!}
_ = refl

--fact⇓120 : (∅ ⊢ (μ (ƛ (ƛ (if (`is-zero `Z) then (`suc `zero) else (` (S Z)

--⟦ μ (ƛ (`suc (# fzero))) ⟧-program ≡ ⊥₁
--⟦ μ (ƛ (`pred (# fzero))) ⟧-program ≡ inj zero
--g (mon (⟦ μ (ƛ_ {A = `ℕ ⇒ `ℕ } (ƛ_  {A = `ℕ} (if (`is-zero (# fzero)) then (`suc `zero) else (# (fsucc fzero) · (`pred (# fzero)))))) ⟧-program))

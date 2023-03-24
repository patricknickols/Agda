module useful-functions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import posets2
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain
open eventually-constant

constant-fun-is-cont : {B : Set} → {D : domain} → B → cont-fun D (flat-domain B)
constant-fun-is-cont-mon : {B : Set} → {D : domain} → B → monotone-fun (pos D) (pos (flat-domain B))
constant-fun-is-cont-mon {B} {D} b = record { g = λ x → inj b
                                            ; mon = λ x → x≼x
                                            }
constant-fun-is-cont {B} {D} b = record { mon = constant-fun-is-cont-mon {B} {D} b
                                        ; lub-preserve = λ c → antisymmetric (pos (flat-domain B))
                                            (lub1
                                              {pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete (flat-domain B) (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {0}
                                            )
                                            (lub2
                                              {pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete (flat-domain B) (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {inj b}
                                              (λ {n} → x≼x)
                                            )
                                        }

pair-f : ∀ {D D₁ D₂ : domain} → cont-fun D D₁ → cont-fun D D₂ → cont-fun D (domain-product D₁ D₂)
g (mon (pair-f f₁ f₂)) x fzero = g (mon f₁) x
g (mon (pair-f f₁ f₂)) x (fsucc i) = g (mon f₂) x
mon (mon (pair-f f₁ f₂)) a≦a′ fzero = mon (mon f₁) a≦a′
mon (mon (pair-f f₁ f₂)) a≦a′ (fsucc y) = mon (mon f₂) a≦a′
lub-preserve (pair-f f₁ f₂) c = dependent-function-extensionality (λ { fzero → (lub-preserve f₁) c ; (fsucc x) → (lub-preserve f₂) c })


_∘_ : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → cont-fun D₁ D₃

∘-mon : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → monotone-fun (domain.pos D₁) (domain.pos D₃)
∘-mon f₂ f₁ = record { g = λ x → g (mon f₂) (g (mon f₁) x)
                     ; mon = λ a≤a′ → mon (mon f₂) (mon (mon f₁) a≤a′)
                     }


_∘_ {D₁ = D₁} {D₂ = D₂} {D₃ = D₃} f₂ f₁  =
                     record { mon = ∘-mon f₂ f₁
                            ; lub-preserve = λ c →
                            begin
                              g (mon f₂) (g (mon f₁) (⊔ (chain-complete D₁ c)))
                            ≡⟨ cong (g (mon f₂)) (lub-preserve f₁ c) ⟩
                              g (mon f₂) (⊔ (chain-complete D₂ (chain-map c (mon f₁))))
                            ≡⟨ lub-preserve f₂ (chain-map c (mon f₁)) ⟩
                              ⊔ (chain-complete D₃ (chain-map c (∘-mon f₂ f₁)))
                            ∎ 
                            }

extend-function : ∀ {X Y} → (X → B⊥ Y) → cont-fun (flat-domain X) (flat-domain Y)
extend-function-mon : ∀ {X Y} → (X → B⊥ Y) → monotone-fun (flat-domain-pos X) (flat-domain-pos Y)
extend-function-mon f = record { g = λ { ⊥₁ → ⊥₁
                                       ; (inj x) → f x
                                       }
                               ; mon = λ {z≼n → z≼n; x≼x → x≼x}
                               }

mon (extend-function {X} {Y} f) = extend-function-mon f

lub-preserve (extend-function {X} {Y} f) c = constant-UP-useful
  {flat-domain-pos Y}
  {chain-map c (extend-function-mon f)}
  {flat-domain-chain-eventually-constant (chain-map c (extend-function-mon f))}
  {g (mon (extend-function f)) (⊔ (chain-complete (flat-domain X) c))}
  {index (flat-domain-chain-eventually-constant c)}
  (λ {m} index≤m →
    cong
      (g (mon (extend-function f)))
      (eventually-val (flat-domain-chain-eventually-constant c) index≤m))
           
ℕ⊥ : domain
𝔹⊥ : domain

ℕ⊥ = flat-domain ℕ
𝔹⊥ = flat-domain Bool

domain-dependent-projection : (I : Set) → (f : I → domain) → (i : I) → cont-fun (domain-dependent-product I f) (f i)
domain-dependent-projection-mon : (I : Set) → (f : I → domain) → (i : I) → monotone-fun (pos (domain-dependent-product I f)) (pos (f i))
domain-dependent-projection-mon I f i = record { g = λ p → p i ; mon = λ a≤a′ → a≤a′ i } 


domain-dependent-projection I f i = record { mon = domain-dependent-projection-mon I f i
                                           ; lub-preserve = λ c →
                                               same-f-same-lub
                                                 {f i} {chain-of-functions I f c i} {chain-map c (domain-dependent-projection-mon I f i)}
                                                 refl
                                           }

pair : ∀ {D} {E} → (A (pos D)) → (A (pos E)) → A (pos (domain-product D E))
pair d e fzero = d
pair d e (fsucc fzero) = e

pair-equality : ∀ {D} {E} → {d₁ d₂ : A (pos D)} → {e₁ e₂ : A (pos E)} → (d₁ ≡ d₂) → (e₁ ≡ e₂) → pair {D} {E} d₁ e₁ ≡ pair {D} {E} d₂ e₂
pair-equality refl refl = refl

pair-η : ∀ {D} {E} → {a : poset.A (pos (domain-product D E))} → pair {D} {E} (a fzero) (a (fsucc fzero)) ≡ a
pair-η = dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}


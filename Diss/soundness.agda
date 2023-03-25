module soundness where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import posets2
open import debruijn
open import ev-cont using (ev-cont)
open import if-cont using (if-cont)
open import cur-cont using (cur-cont)
open import useful-functions using (pair-f; _∘_)

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)


open cont-fun
open monotone-fun


term-⟦_⟧ : ∀ {A} → (M : ∅ ⊢ A) → cont-fun context-⟦ ∅ ⟧ ⟦ A ⟧
term-⟦ M ⟧ = ⟦ ∅ ⊢′ M ⟧

if-true : ∀ {x} {A₁} {V : ∅ ⊢ A₁} {y : ∅ ⊢ A₁}
  → (g (mon if-cont) (g (mon (pair-f term-⟦ `true ⟧ (pair-f term-⟦ V ⟧ term-⟦ y ⟧))) x))
     ≡
     g (mon term-⟦ V ⟧) x

if-true {x} {A₁} {V} {y} =
  begin
    g (mon if-cont)
      (g (mon (pair-f term-⟦ `true ⟧ (pair-f term-⟦ V ⟧ term-⟦ y ⟧))) x)
  ≡⟨ refl ⟩
    g (mon if-cont)
      (g (mon (pair-f (constant-fun {∅} Bool true) (pair-f term-⟦ V ⟧ term-⟦ y ⟧)))x)
  ≡⟨ refl ⟩
    g (mon term-⟦ V ⟧) x
  ∎

if-false : ∀ {x} {A₁} {V : ∅ ⊢ A₁} {y : ∅ ⊢ A₁} 
  → (g (mon if-cont) (g (mon (pair-f term-⟦ `false ⟧ (pair-f term-⟦ y ⟧ term-⟦ V ⟧))) x))
     ≡
    (g (mon term-⟦ V ⟧) x)

if-false = refl

soundness : ∀ {A} → {M : ∅ ⊢ A} {V : ∅ ⊢ A} → (step : M —→ V) → term-⟦ M ⟧ ≡ term-⟦ V ⟧
soundness (ξ-·₁ {L = L} {L′} {M} L→L′) =
  begin
    term-⟦ L · M ⟧
  ≡⟨ refl ⟩
    ev-cont ∘ pair-f term-⟦ L ⟧ term-⟦ M ⟧
  ≡⟨ cong (_∘_ ev-cont) (cong (λ x → pair-f x term-⟦ M ⟧) (soundness L→L′)) ⟩
    ev-cont ∘ pair-f term-⟦ L′ ⟧ term-⟦ M ⟧
  ≡⟨ refl ⟩
    term-⟦ L′ · M ⟧
  ∎
soundness (ξ-·₂ {V = V} {M} {M′} v M→M′) =
  begin
    term-⟦ V · M ⟧
  ≡⟨ refl ⟩
    ev-cont ∘ pair-f term-⟦ V ⟧ term-⟦ M ⟧
  ≡⟨ cong (_∘_ ev-cont) (cong (pair-f term-⟦ V ⟧) (soundness M→M′)) ⟩
    ev-cont ∘ pair-f term-⟦ V ⟧ term-⟦ M′ ⟧
  ≡⟨ refl ⟩
    term-⟦ V · M′ ⟧
  ∎

soundness (β-ƛ {A = A} {N = N} {W} v) =
  begin
    term-⟦ (ƛ N) · W ⟧
  ≡⟨ refl ⟩
    ev-cont ∘ pair-f term-⟦ ƛ N ⟧ term-⟦ W ⟧
  ≡⟨ {!!} ⟩ 
    term-⟦ subst σ N ⟧
  ≡⟨ {!!} ⟩
    term-⟦ N [ W ] ⟧
  ∎
  where
  σ : ∀ {A₂} → ∅ , A ∋ A₂ → ∅ ⊢ A₂
  σ Z     = W
  σ (S x) = ` x

soundness (ξ-suc {M = M} {M′} M→M′) =
  begin
    term-⟦ `suc M ⟧
  ≡⟨ refl ⟩
    (s⊥ ∘ term-⟦ M ⟧)
  ≡⟨ cong (_∘_ s⊥) (soundness M→M′) ⟩
    (s⊥ ∘ term-⟦ M′ ⟧)
  ≡⟨ refl ⟩
    term-⟦ `suc M′ ⟧
  ∎
soundness (ξ-pred {M = M} {M′} M→M′) =
  begin
    term-⟦ `pred M ⟧
  ≡⟨ refl ⟩
    p⊥ ∘ term-⟦ M ⟧
  ≡⟨ cong (_∘_ p⊥) (soundness M→M′) ⟩
    p⊥ ∘ term-⟦ M′ ⟧
  ≡⟨ refl ⟩
    term-⟦ `pred M′ ⟧
  ∎
soundness β-pred₁ = cont-fun-extensionality (λ ⊥ → refl)
soundness {V = V} (β-pred₂ v) =
  begin
    term-⟦ `pred (`suc V) ⟧
  ≡⟨ refl ⟩
    p⊥ ∘ (s⊥ ∘ term-⟦ V ⟧)
  ≡⟨ cont-fun-extensionality (λ ⊥ → p⊥-inv-s⊥) ⟩
    term-⟦ V ⟧
  ∎ 
soundness (ξ-if {B = B} {B′} {x} {y} B→B′) =
  begin
    term-⟦ if B then x else y ⟧
  ≡⟨ refl ⟩
    if-cont ∘ (pair-f term-⟦ B ⟧ (pair-f term-⟦ x ⟧ term-⟦ y ⟧))
  ≡⟨ cong (_∘_ if-cont) (cong (λ b → pair-f b (pair-f term-⟦ x ⟧ term-⟦ y ⟧)) (soundness B→B′)) ⟩
    (if-cont ∘ (pair-f term-⟦ B′ ⟧ (pair-f term-⟦ x ⟧ term-⟦ y ⟧)))
  ≡⟨ refl ⟩
    term-⟦ if B′ then x else y ⟧
  ∎
soundness {A} {V = V} (β-if₁ {y = y}) =
  begin
    term-⟦ if `true then V else y ⟧
  ≡⟨ refl ⟩
    (if-cont ∘ (pair-f term-⟦ `true ⟧ (pair-f term-⟦ V ⟧ term-⟦ y ⟧)) )
  ≡⟨ cont-fun-extensionality (λ ⊥ → if-true {⊥} {A} {V} {y}) ⟩
    term-⟦ V ⟧
  ∎
soundness {A} {V = V} (β-if₂ {x = x}) =
  begin
    term-⟦ if `false then x else V ⟧
  ≡⟨ refl ⟩
    if-cont ∘ (pair-f term-⟦ `false ⟧ (pair-f term-⟦ x ⟧ term-⟦ V ⟧))
  ≡⟨ cont-fun-extensionality (λ ⊥ → if-false {⊥} {A} {V} {x}) ⟩
    term-⟦ V ⟧
  ∎
soundness {A} (β-μ {N = N}) =
   begin
     term-⟦ μ N ⟧
   ≡⟨ refl ⟩
     tarski-continuous ∘ term-⟦ N ⟧
   ≡⟨ cont-fun-extensionality
     (λ x → lfp-is-fixed { ⟦ A ⟧ } {g (mon term-⟦ N ⟧) x})
    ⟩
     ev-cont ∘ pair-f term-⟦ N ⟧ (tarski-continuous ∘ term-⟦ N ⟧)
   ≡⟨ refl ⟩
     ev-cont ∘ (pair-f term-⟦ N ⟧ term-⟦ μ N ⟧)
   ≡⟨ refl ⟩
     term-⟦ N · (μ N) ⟧
   ∎
soundness (ξ-is-zero {M = M} {M′} M→M′) =
  begin
    term-⟦ `is-zero M ⟧
  ≡⟨ refl ⟩
    z⊥ ∘ term-⟦ M ⟧
  ≡⟨ cong (_∘_ z⊥) (soundness M→M′) ⟩
    z⊥ ∘ term-⟦ M′ ⟧
  ≡⟨ refl ⟩
    term-⟦ `is-zero M′ ⟧
  ∎
soundness β-is-zero₁ =
  begin
    term-⟦ `is-zero `zero ⟧
  ≡⟨ refl ⟩
    z⊥ ∘ term-⟦ `zero ⟧
  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
    term-⟦ `true ⟧
  ∎
soundness (β-is-zero₂ {M = `zero} x) =
  begin
    term-⟦ `is-zero (`suc `zero) ⟧
  ≡⟨ refl ⟩
    z⊥ ∘ (s⊥ ∘ term-⟦ `zero ⟧)
  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
    term-⟦ `false ⟧
  ∎
soundness (β-is-zero₂ {M = `suc M} x) =
   begin
     term-⟦ `is-zero (`suc (`suc M)) ⟧
   ≡⟨ refl ⟩
     (z⊥ ∘ (s⊥ ∘ (s⊥ ∘ term-⟦ M ⟧)) )
   ≡⟨ cont-fun-extensionality (λ ⊥ → {!!} ) ⟩
     term-⟦ `false ⟧
    ∎

∘-assoc : {D₀ D₁ D₂ D₃ : domain} {f : cont-fun D₂ D₃} {g : cont-fun D₁ D₂} {h : cont-fun D₀ D₁} → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
∘-assoc {f} {g} {h} = cont-fun-extensionality λ ⊥ → refl

lemma-blah-proof : ∀ {M} → Value M → z⊥ ∘ (term-⟦ `suc M ⟧) ≡ term-⟦ `false ⟧


z⊥∘s⊥-inj-n : {n : ℕ} → g (mon (z⊥ ∘ s⊥)) (inj n) ≡ inj false
z⊥∘s⊥-inj-n = refl



lemma-blah-proof {M} V-zero = 
  begin
    z⊥ ∘ term-⟦ `suc M ⟧
  ≡⟨ refl ⟩
    z⊥ ∘ (s⊥ ∘ term-⟦ M ⟧)
  ≡⟨ Eq.sym (∘-assoc {f = z⊥} {g = s⊥} {h = term-⟦ M ⟧}) ⟩
    (z⊥ ∘ s⊥) ∘ term-⟦ M ⟧
  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
    term-⟦ `false ⟧
  ∎
lemma-blah-proof {.(`suc V)} (V-suc {V = V} val-M) =
  begin
    z⊥ ∘ term-⟦ `suc (`suc V) ⟧
  ≡⟨ refl ⟩
    z⊥ ∘ (s⊥ ∘ term-⟦ `suc V ⟧)
  ≡⟨ Eq.sym (∘-assoc { f = z⊥} { s⊥ } { term-⟦ `suc V ⟧ }) ⟩
    (z⊥ ∘ s⊥) ∘ term-⟦ `suc V ⟧
  ≡⟨ cont-fun-extensionality (λ ⊥ →
     begin
       g (mon ((z⊥ ∘ s⊥) ∘ term-⟦ `suc V ⟧)) ⊥
     ≡⟨ {!z⊥∘s⊥-inj-n { g (mon term-⟦ `suc V ⟧) ⊥ }!} ⟩
       inj false
     ≡⟨ refl ⟩
       g (mon term-⟦ `false ⟧) ⊥
     ∎)
   ⟩
    term-⟦ `false ⟧
  ∎

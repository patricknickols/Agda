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

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)

open poset
open domain
open cont-fun
open monotone-fun


term-⟦_⟧ : ∀ {A} → (M : ∅ ⊢ A) → cont-fun context-⟦ ∅ ⟧ ⟦ A ⟧
term-⟦ M ⟧ = ⟦ ∅ ⊢′ M ⟧

z⊥∘s⊥-n≡false : ∀ {n} → g (mon (z⊥ ∘ s⊥)) (inj n) ≡ inj false
z⊥∘s⊥-n≡false {zero} = refl
z⊥∘s⊥-n≡false {suc x} = refl

well-typed-nats-are-not-bot : (M : ∅ ⊢ `ℕ) → (x : Value M) → {⊥ : A (pos context-⟦ ∅ ⟧)} → ∃[ n ] (g (mon term-⟦ M ⟧) ⊥ ≡ (inj n))
well-typed-nats-are-not-bot `zero V-zero = ⟨ 0 , refl ⟩
well-typed-nats-are-not-bot (`suc M) (V-suc x) {⊥} with well-typed-nats-are-not-bot M x {⊥}
...                                 | ⟨ n , proof ⟩ = ⟨ suc n , cong (λ v → g (mon s⊥) v) proof ⟩

z⊥∘s⊥-soundness-lemma : (M : ∅ ⊢ `ℕ) → (x : Value M) → {⊥ : A (pos context-⟦ ∅ ⟧)} → g (mon (z⊥ ∘ (s⊥ ∘ term-⟦ M ⟧))) ⊥ ≡ inj false
z⊥∘s⊥-soundness-lemma M x {⊥} with well-typed-nats-are-not-bot M x {⊥}
...            | ⟨ n , proof ⟩ = 
                 begin
                   g (mon (z⊥ ∘ (s⊥ ∘ term-⟦ M ⟧))) (⊥)
                 ≡⟨ refl ⟩
                   g (mon (z⊥ ∘ s⊥)) (g (mon term-⟦ M ⟧) ⊥)
                 ≡⟨ cong (λ x → (g (mon (z⊥ ∘ s⊥))) x) proof ⟩
                   g (mon (z⊥ ∘ s⊥)) (inj n)
                 ≡⟨ z⊥∘s⊥-n≡false {n} ⟩
                   inj false
                 ∎

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

soundness (β-ƛ {A = A} {N = N} {W}) =
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
  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
    term-⟦ V ⟧
  ∎
soundness {A} {V = V} (β-if₂ {x = x}) =
  begin
    term-⟦ if `false then x else V ⟧
  ≡⟨ refl ⟩
    if-cont ∘ (pair-f term-⟦ `false ⟧ (pair-f term-⟦ x ⟧ term-⟦ V ⟧))
  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
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
soundness (β-is-zero₂ {M = M} x) =
  begin
    term-⟦ `is-zero (`suc M) ⟧
  ≡⟨ cont-fun-extensionality (λ ⊥ → z⊥∘s⊥-soundness-lemma M x {⊥})⟩
    term-⟦ `false ⟧
  ∎

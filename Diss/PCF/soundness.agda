module PCF.soundness where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import DomainTheory.BasicObjects.posets-etc
open import DomainTheory.BasicObjects.theorems
open import DomainTheory.ContinuousFunctions.ev-cont using (ev-cont)
open import DomainTheory.ContinuousFunctions.if-cont using (if-g; if-cont)
open import DomainTheory.ContinuousFunctions.cur-cont using (cur-mon; cur-cont)
open import DomainTheory.ContinuousFunctions.fix-cont
open import misc
open import PCF.pcf
open import PCF.soundness-lemmas

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂)

open poset
open domain
open cont-fun
open monotone-fun

compositional-suc : {M₁ M₂ : ∅ ⊢ `ℕ} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ `suc M₁ ⟧ ≡ term-⟦ `suc M₂ ⟧
compositional-pred : {M₁ M₂ : ∅ ⊢ `ℕ} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ `pred M₁ ⟧ ≡ term-⟦ `pred M₂ ⟧
compositional-zero : {M₁ M₂ : ∅ ⊢ `ℕ} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ `is-zero M₁ ⟧ ≡ term-⟦ `is-zero M₂ ⟧
--compositional-if-arg1 : {A : Type} {M₁ M₂ : ∅ ⊢ `bool} {X Y : ∅ ⊢ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ if M₁ then X else Y ⟧ ≡ term-⟦ if M₂ then X else Y ⟧
--compositional-if-arg2 : {A : Type} {B : ∅ ⊢ `bool} {M₁ M₂ Y : ∅ ⊢ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ if B then M₁ else Y ⟧ ≡ term-⟦ if B then M₂ else Y ⟧
--compositional-if-arg3 : {A : Type} {B : ∅ ⊢ `bool} {M₁ M₂ X : ∅ ⊢ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ if B then X else M₁ ⟧ ≡ term-⟦ if B then X else M₂ ⟧
compositional-app1 : {A B : Type} {M₁ M₂ : ∅ ⊢ A ⇒ B} {X : ∅ ⊢ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ M₁ · X ⟧ ≡ term-⟦ M₂ · X ⟧
compositional-app2 : {A B : Type} {F : ∅ ⊢ A ⇒ B} {M₁ M₂ : ∅ ⊢ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ F · M₁ ⟧ ≡ term-⟦ F · M₂ ⟧
--compositional-fix : {A : Type} {M₁ M₂ : ∅ ⊢ A ⇒ A} → term-⟦ M₁ ⟧ ≡ term-⟦ M₂ ⟧ → term-⟦ μ M₁ ⟧ ≡ term-⟦ μ M₂ ⟧

compositional-suc M₁≡M₂ = cong (λ f → s⊥ ∘ f) M₁≡M₂
compositional-pred M₁≡M₂ = cong (λ f → p⊥ ∘ f) M₁≡M₂
compositional-zero M₁≡M₂ = cong (λ f → z⊥ ∘ f) M₁≡M₂
{-
compositional-if-arg1 {A} {M₁} {M₂} {X} {Y} M₁≡M₂ =
  begin
    term-⟦ if M₁ then X else Y ⟧
  ≡⟨⟩
    if-cont ∘ pair-f term-⟦ M₁ ⟧ (pair-f term-⟦ X ⟧ term-⟦ Y ⟧)
  ≡⟨ cong (λ f → if-cont ∘ pair-f f (pair-f term-⟦ X ⟧ term-⟦ Y ⟧)) M₁≡M₂ ⟩
    if-cont ∘ pair-f term-⟦ M₂ ⟧ (pair-f term-⟦ X ⟧ term-⟦ Y ⟧)
  ≡⟨⟩
    term-⟦ if M₂ then X else Y ⟧
  ∎
compositional-if-arg2 {A} {B} {M₁} {M₂} {Y} M₁≡M₂ =
  begin
    term-⟦ if B then M₁ else Y ⟧
  ≡⟨⟩
    if-cont ∘ pair-f term-⟦ B ⟧ (pair-f term-⟦ M₁ ⟧ term-⟦ Y ⟧)
  ≡⟨ cong (λ f → if-cont ∘ pair-f term-⟦ B ⟧ (pair-f f term-⟦ Y ⟧)) M₁≡M₂ ⟩
    if-cont ∘ pair-f term-⟦ B ⟧ (pair-f term-⟦ M₂ ⟧ term-⟦ Y ⟧)
  ≡⟨⟩
    term-⟦ if B then M₂ else Y ⟧
  ∎
compositional-if-arg3 {A} {B} {M₁} {M₂} {X} M₁≡M₂ =
  begin
    term-⟦ if B then X else M₁ ⟧
  ≡⟨⟩
    if-cont ∘ pair-f term-⟦ B ⟧ (pair-f term-⟦ X ⟧ term-⟦ M₁ ⟧)
  ≡⟨ cong (λ f → if-cont ∘ pair-f term-⟦ B ⟧ (pair-f term-⟦ X ⟧ f)) M₁≡M₂ ⟩
    if-cont ∘ pair-f term-⟦ B ⟧ (pair-f term-⟦ X ⟧ term-⟦ M₂ ⟧)
  ≡⟨⟩
    term-⟦ if B then X else M₂ ⟧
  ∎
-}
compositional-app1 {A} {B} {M₁} {M₂} {X} M₁≡M₂ =
  begin
    term-⟦ M₁ · X ⟧
  ≡⟨⟩
    ev-cont ∘ pair-f term-⟦ M₁ ⟧ term-⟦ X ⟧
  ≡⟨ cong (λ f → ev-cont ∘ pair-f f term-⟦ X ⟧) M₁≡M₂ ⟩
    ev-cont ∘ pair-f term-⟦ M₂ ⟧ term-⟦ X ⟧
  ≡⟨⟩
    term-⟦ M₂ · X ⟧
  ∎
compositional-app2 {A} {B} {F} {M₁} {M₂} M₁≡M₂ =
  begin
    term-⟦ F · M₁ ⟧
  ≡⟨⟩
    ev-cont ∘ pair-f term-⟦ F ⟧ term-⟦ M₁ ⟧
  ≡⟨ cong (λ f → ev-cont ∘ pair-f term-⟦ F ⟧ f) M₁≡M₂ ⟩
    ev-cont ∘ pair-f term-⟦ F ⟧ term-⟦ M₂ ⟧
  ≡⟨⟩
    term-⟦ F · M₂ ⟧
  ∎
--compositional-fix M₁≡M₂ = cong (λ f → tarski-continuous ∘ f) M₁≡M₂


comm-triangle : {Γ Δ : Context} {τ : Type} (t : Γ ⊢ τ) → (σ : {A : Type} → Γ ∋ A → Δ ⊢ A)
  → ⟦ Δ ⊢′ subst σ t ⟧ ≡ ⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ
{-
comm-triangle `true σ = cont-fun-extensionality λ x → refl
comm-triangle `false σ = cont-fun-extensionality λ x → refl
comm-triangle `zero σ = cont-fun-extensionality λ x → refl
comm-triangle {Γ} {Δ} (`suc t) σ =
  begin
    ⟦ Δ ⊢′ subst σ (`suc t) ⟧
  ≡⟨ cong (_∘_ s⊥) (comm-triangle t σ) ⟩
    (s⊥ ∘ (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ))
  ≡⟨ cont-fun-extensionality (λ x → refl) ⟩
    ((s⊥ ∘ ⟦ Γ ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ )
  ∎
comm-triangle {Γ} {Δ} (`is-zero t) σ =
  begin
    (z⊥ ∘ ⟦ Δ ⊢′ subst σ t ⟧)
  ≡⟨ cong (_∘_ z⊥) (comm-triangle t σ) ⟩
    (z⊥ ∘ (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ))
  ≡⟨ (cont-fun-extensionality λ x → refl) ⟩
    ((z⊥ ∘ ⟦ Γ ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ)
  ∎
comm-triangle {Γ} {Δ} (`pred t) σ =
  begin
    (p⊥ ∘ ⟦ Δ ⊢′ subst σ t ⟧)
  ≡⟨ cong (_∘_ p⊥) (comm-triangle t σ) ⟩
    (p⊥ ∘ (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ))
  ≡⟨ (cont-fun-extensionality λ x → refl) ⟩
    ((p⊥ ∘ ⟦ Γ ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ)
  ∎
comm-triangle {Γ} {Δ} (μ t) σ =
  begin
    (tarski-continuous ∘ ⟦ Δ ⊢′ subst σ t ⟧)
  ≡⟨ cong (_∘_ tarski-continuous) (comm-triangle t σ) ⟩
    (tarski-continuous ∘ (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ))
  ≡⟨ (cont-fun-extensionality λ x → refl) ⟩
    ((tarski-continuous ∘ ⟦ Γ ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ)
  ∎
comm-triangle {Γ} {Δ} (t · t₁) σ =
  begin
    ev-cont ∘ pair-f ⟦ Δ ⊢′ subst σ t ⟧ ⟦ Δ ⊢′ subst σ t₁ ⟧
  ≡⟨ cong (λ x → ev-cont ∘ pair-f x ⟦ Δ ⊢′ subst σ t₁ ⟧) (comm-triangle t σ) ⟩
    (ev-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) ⟦ Δ ⊢′ subst σ t₁ ⟧)
  ≡⟨ cong (λ x → ev-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) x) (comm-triangle t₁ σ) ⟩
    (ev-cont ∘ pair-f ((⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ)) ((⟦ Γ ⊢′ t₁ ⟧ ∘ ⟦ σ ⟧ₛ)))
  ≡⟨ cont-fun-extensionality (λ x → refl) ⟩ 
    (ev-cont ∘ pair-f ⟦ Γ ⊢′ t ⟧ ⟦ Γ ⊢′ t₁ ⟧) ∘ ⟦ σ ⟧ₛ
  ∎
comm-triangle {Γ} {Δ} (if t then t₁ else t₂) σ =
  begin
    if-cont ∘ pair-f ⟦ Δ ⊢′ subst σ t ⟧ (pair-f ⟦ Δ ⊢′ subst σ t₁ ⟧ ⟦ Δ ⊢′ subst σ t₂ ⟧)
  ≡⟨ cong (λ x → if-cont ∘ pair-f x (pair-f ⟦ Δ ⊢′ subst σ t₁ ⟧ ⟦ Δ ⊢′ subst σ t₂ ⟧)) (comm-triangle t σ) ⟩
    if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f ⟦ Δ ⊢′ subst σ t₁ ⟧ ⟦ Δ ⊢′ subst σ t₂ ⟧)
  ≡⟨ cong (λ x → if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f x ⟦ Δ ⊢′ subst σ t₂ ⟧)) (comm-triangle t₁ σ) ⟩
    (if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f (⟦ Γ ⊢′ t₁ ⟧ ∘ ⟦ σ ⟧ₛ) ⟦ Δ ⊢′ subst σ t₂ ⟧))
  ≡⟨ cong (λ x → if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f (⟦ Γ ⊢′ t₁ ⟧ ∘ ⟦ σ ⟧ₛ) x)) (comm-triangle t₂ σ) ⟩
    if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f (⟦ Γ ⊢′ t₁ ⟧ ∘ ⟦ σ ⟧ₛ) (⟦ Γ ⊢′ t₂ ⟧ ∘ ⟦ σ ⟧ₛ))
  ≡⟨ needed-lemma {f₁ = ⟦ Γ ⊢′ t ⟧} {⟦ Γ ⊢′ t₁ ⟧} {⟦ Γ ⊢′ t₂ ⟧} {⟦ σ ⟧ₛ} ⟩
    (if-cont ∘ pair-f ⟦ Γ ⊢′ t ⟧ (pair-f ⟦ Γ ⊢′ t₁ ⟧ ⟦ Γ ⊢′ t₂ ⟧)) ∘ ⟦ σ ⟧ₛ
    ∎
comm-triangle {Γ , X} {Δ} (` Z) σ = cont-fun-extensionality (λ x → refl)
comm-triangle {Γ , X} {Δ} (` (S x)) σ = cont-fun-extensionality (λ x₁ → (cong (λ z → g (mon z) x₁) (comm-triangle {Γ} {Δ} (` x) (weaken-σ σ))))
comm-triangle {Γ} {Δ} (ƛ_ {A = A} {B} t) σ =
  begin
    cur-cont (helpful-lemma-blah {Δ} {A} {B} ⟦ Δ , A ⊢′ subst (exts σ) t ⟧)
  ≡⟨ cong (λ z → cur-cont (helpful-lemma-blah {Δ} {A} {B} z)) (comm-triangle t (exts σ)) ⟩
    cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ ⟦ exts σ ⟧ₛ))
  ≡⟨ cong (λ z → cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ z))) (lemma-53 {Γ} {Δ} {A} {σ}) ⟩
    cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ shift-lemma (⟦ σ ⟧ₛ ×-cont id)))
  ≡⟨ curry-lemma {Γ} {Δ} {A} {B} {⟦ Γ , A ⊢′ t ⟧} {⟦ σ ⟧ₛ } ⟩
    cur-cont (helpful-lemma-blah {Γ} {A} {B} ⟦ Γ , A ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ
  ∎
-}
{-
substitution-lemma′ : ∀ {Γ} {τ τ′ : Type} → (M : Γ ⊢ τ) → (M′ : Γ , τ ⊢ τ′)
  → ⟦ Γ ⊢′ M′ [ M ] ⟧
    ≡
    ⟦ Γ , τ ⊢′ M′ ⟧ ∘ (concat ∘ (pair-f id ⟦ Γ ⊢′ M ⟧))

substitution-lemma′ {Γ} {τ} {τ′} M M′ =
  begin
    ⟦ Γ ⊢′ M′ [ M ] ⟧
  ≡⟨ comm-triangle M′ (σ {Γ} {τ} {M}) ⟩
    ⟦ Γ , τ ⊢′ M′ ⟧ ∘ ⟦ σ {Γ} {τ} {M} ⟧ₛ
  ≡⟨ lemma-55-corr {Γ} {τ} {τ′} {M} {M′}⟩
    ⟦ Γ , τ ⊢′ M′ ⟧ ∘ (concat ∘ pair-f id ⟦ Γ ⊢′ M ⟧)
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
soundness (β-ƛ {A = A} {B} {N} {W}) =
 begin
   term-⟦ (ƛ N) · W ⟧
 ≡⟨ refl ⟩
   ev-cont ∘ pair-f term-⟦ ƛ N ⟧ term-⟦ W ⟧
 ≡⟨ cong (_∘_ ev-cont) (cong (λ x → pair-f x term-⟦ W ⟧) (cont-fun-extensionality (λ x → refl))) ⟩
   (ev-cont ∘ pair-f (cur-cont (⟦ ∅ , A ⊢′ N ⟧ ∘ concat)) term-⟦ W ⟧)
 ≡⟨ pair-lemma-corr {A} {B} {N} {W} ⟩
   (⟦ ∅ , A ⊢′ N ⟧ ∘ (concat ∘ (pair-f id term-⟦ W ⟧)))
 ≡⟨ Eq.sym (substitution-lemma′ W N) ⟩
   term-⟦ N [ W ] ⟧
 ∎
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

-}

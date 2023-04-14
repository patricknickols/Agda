module PCF.soundness where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import DomainTheory.BasicObjects.posets-etc
open import DomainTheory.BasicObjects.theorems
open import PCF.pcf
open import DomainTheory.ContinuousFunctions.ev-cont using (ev-cont)
open import DomainTheory.ContinuousFunctions.if-cont using (if-g; if-cont)
open import DomainTheory.ContinuousFunctions.cur-cont using (cur-cont)
open import DomainTheory.ContinuousFunctions.fix-cont
open import misc

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂)

open poset
open domain
open cont-fun
open monotone-fun

prop-531 : {τ τ′ : Type} {Γ : Context} → (M : Γ ⊢ τ) → (M′ : Γ , τ ⊢ τ′) → Γ ⊢ τ′
prop-531 M M′ = M′ [ M ]

term-⟦_⟧ : ∀ {τ} → (M : ∅ ⊢ τ) → cont-fun context-⟦ ∅ ⟧ ⟦ τ ⟧
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

transform-lemma′ : ∀ {Γ} {τ τ′ : Type} → cont-fun context-⟦ Γ , τ ⟧ ⟦ τ′ ⟧ → cont-fun context-⟦ Γ ⟧ (function-domain ⟦ τ ⟧ ⟦ τ′ ⟧)

transform-lemma′ {Γ} {τ} {τ′} f = cur-cont (helpful-lemma-blah {Γ} {τ} {τ′} f)

rename-lemma : {Γ : Context} {Δ : Context} {τ : Type}
  → (M : Γ ⊢ τ)
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (d : poset.A (pos context-⟦ Δ ⟧))
  → (e : poset.A (pos context-⟦ Γ ⟧))
  → (∀ {A} → (x : Γ ∋ A) → g (mon (project-x Γ x)) e ≡ g (mon (project-x Δ (ρ x))) d)
  → g (mon ⟦ Γ ⊢′ M ⟧) e
    ≡
    g (mon ⟦ Δ ⊢′ rename ρ M ⟧) d

extend-ρ : ∀ {Γ} {A τ : Type} → ((i : Fin (suc (length Γ))) → poset.A (pos ⟦ lookup₂ {Γ , A} i ⟧)) →  (j : Fin (suc (suc (length Γ)))) → poset.A (pos ⟦ lookup₂ {Γ , A , τ} j ⟧)


key-var-lemma : ∀ {Γ : Context} {τ τ′ : Type} {x : Γ ∋ τ′ } {ρ} (M : Γ ⊢ τ) →
  g (mon (project-x Γ x))ρ
  ≡
  g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ ` (S x) ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)

key-var-lemma {x = Z}   M = refl
key-var-lemma {Γ , A} {τ = τ} {τ′} {S x} {ρ} M =
  begin
    g (mon (project-x (Γ , A) (S x)))ρ
  ≡⟨ {!rename-lemma!} ⟩
    g (mon (project-x (Γ , A , τ) (S S x))) (extend-ρ {Γ} {A} {τ} ρ)
  ≡⟨ {!!} ⟩
    g (mon (g (mon (transform-lemma′ {Γ , A} {τ} {τ′} ⟦ Γ , A , τ ⊢′ ` S (S x) ⟧)) ρ)) (g (mon ⟦ Γ , A ⊢′ M ⟧) ρ)
  ∎

key-λ-lemma-2 :  ∀ {Γ} {A B τ τ′ : Type} (M : Γ ⊢ τ) (M′ : Γ , τ , A ⊢ B) →
  transform-lemma′ {Γ} {A} {B} ⟦ Γ , A ⊢′ (subst (exts (σ {Γ} {A ⇒ B} {τ} {ƛ M′} {M})) M′) ⟧
  ≡
  ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {A ⇒ B} ⟦ Γ , τ ⊢′ ƛ M′ ⟧) ⟦ Γ ⊢′ M ⟧


key-λ-lemma : ∀ {Γ} {A B τ τ′ : Type} → (n : ℕ) (pf : n ≡ length Γ) → (M : Γ ⊢ τ) → (M′ : Γ , τ , A ⊢ B) → ∀ {ρ} →
  g (mon (transform-lemma′ {Γ} {A} {B} ⟦ Γ , A ⊢′ (subst (exts (σ {Γ} {A ⇒ B} {τ} {ƛ M′} {M})) M′) ⟧)) ρ
  ≡
  g (mon (g (mon (transform-lemma′ {Γ} {τ} {A ⇒ B} ⟦ Γ , τ ⊢′ ƛ M′ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)

--(transform-lemma′ {Γ} {A} {B} ⟦ Γ , A ⊢′ subst (exts (σ {Γ} {A ⇒ B} {τ} {ƛ M′} {M})) M′ ⟧
--≡
--(ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {A ⇒ B} ⟦ Γ , τ ⊢′ ƛ M′ ⟧) ⟦ Γ ⊢′ M ⟧)

--sub-lemma-generalised : ∀ {Γ} {τ τ′ : Type} → (M : Γ ⊢ τ) → (M′ : Γ , τ ⊢ τ′)
--  → ⟦ Γ ⊢′ M′ [ M ] ⟧
--  ≡ ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧

--sub-lemma-generalised {Γ} {τ} {τ′} M M′ = {!!}

--
substitution-lemma : ∀ {Γ} {τ τ′ : Type} → (M : Γ ⊢ τ) → (M′ : Γ , τ ⊢ τ′) → (ρ : A (pos context-⟦ Γ ⟧))
  → g (mon ⟦ Γ ⊢′ M′ [ M ] ⟧) ρ
    ≡
    g (mon (g (mon (⟦ Γ ⊢′ ƛ M′ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--≡ g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--
--substitution-lemma {Γ} {τ} {τ′} M (if M′ then M′₁ else M′₂) ρ =
--  begin
--    g (mon ⟦ Γ ⊢′ (if M′ then M′₁ else M′₂) [ M ] ⟧) ρ
--  ≡⟨ refl ⟩
--    g (mon (if-cont ∘
--    (pair-f
--      ⟦ Γ ⊢′ M′ [ M ] ⟧
--      (pair-f
--        ⟦ Γ ⊢′ M′₁ [ M ] ⟧
--        ⟦ Γ ⊢′ M′₂ [ M ] ⟧))))
--    ρ
--  ≡⟨ cong (λ x → g (mon (if-cont ∘ (pair-f x (pair-f ⟦ Γ ⊢′ M′₁ [ M ] ⟧ ⟦ Γ ⊢′ M′₂ [ M ] ⟧))))ρ) (cont-fun-extensionality (substitution-lemma M M′)) ⟩
--    g (mon (if-cont ∘
--    (pair-f
--      (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--      (pair-f
--        ⟦ Γ ⊢′ M′₁ [ M ] ⟧
--        ⟦ Γ ⊢′ M′₂ [ M ] ⟧))))
--    ρ
--  ≡⟨ cong (λ x → g (mon (if-cont ∘ (pair-f (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧) (pair-f x  ⟦ Γ ⊢′ M′₂ [ M ] ⟧)))) ρ) (cont-fun-extensionality (substitution-lemma M M′₁)) ⟩
--    g (mon (if-cont ∘
--    (pair-f
--      (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--      (pair-f
--        (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₁ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--        ⟦ Γ ⊢′ M′₂ [ M ] ⟧))))
--    ρ
--  ≡⟨ cong (λ x →  g (mon (if-cont ∘ (pair-f (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧) (pair-f (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₁ ⟧ ) ⟦ Γ ⊢′ M ⟧) x)))) ρ) (cont-fun-extensionality (substitution-lemma M M′₂))  ⟩
--    g (mon (if-cont ∘
--    (pair-f
--      (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--      (pair-f
--        (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₁ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--        (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₂ ⟧ ) ⟦ Γ ⊢′ M ⟧)))))
--    ρ
--  ≡⟨ {!!} ⟩
--    if-g (pair
--      (g (mon (g (mon (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ))
--      (pair {⟦ τ′ ⟧} {⟦ τ′ ⟧}
--        (g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₁ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ))
--        (g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₂ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ))
--      ))
--  ≡⟨ {!!} ⟩
--    if-g (g (mon (
--      pair-f
--        ((g (mon (transform-lemma′ {Γ} {τ} {`bool} ⟦ Γ , τ ⊢′ M′ ⟧))) ρ)
--        (pair-f
--          ((g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₁ ⟧))) ρ)
--          ((g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′₂ ⟧))) ρ)))) (g (mon ⟦ Γ ⊢′ M ⟧) ρ))
--  ≡⟨ {!!} ⟩
--    g (mon (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ if M′ then M′₁ else M′₂ ⟧) ⟦ Γ ⊢′ M ⟧)) ρ
--  ≡⟨ refl ⟩
--    g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ if M′ then M′₁ else M′₂ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--  ∎
--
--
--substitution-lemma {Γ} {τ} {τ′} M ( _·_ {A = A} M′ M′₁) ρ = 
--  begin
--    g (mon ⟦ Γ ⊢′ (M′ · M′₁) [ M ] ⟧) ρ
--  ≡⟨ refl ⟩
--    g (mon (ev-cont ∘ (pair-f
--      ⟦ Γ ⊢′ M′ [ M ] ⟧
--      ⟦ Γ ⊢′ M′₁ [ M ] ⟧)
--      ))
--    ρ
--  ≡⟨ {!!} ⟩
--    g (mon (ev-cont ∘ (pair-f
--      (ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {A ⇒ τ′} ⟦ Γ , τ ⊢′ M′ ⟧ ) ⟦ Γ ⊢′ M ⟧)
--      ⟦ Γ ⊢′ M′₁ [ M ] ⟧)
--      ))
--    ρ
--  ≡⟨ {!!} ⟩
--    g (mon (ev-cont ∘ (pair-f
--      ((ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {A ⇒ τ′} ⟦ Γ , τ ⊢′ M′  ⟧ ) ⟦ Γ ⊢′ M ⟧))
--      ((ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {A}      ⟦ Γ , τ ⊢′ M′₁ ⟧ ) ⟦ Γ ⊢′ M ⟧)))
--      ))
--    ρ
--  ≡⟨ refl ⟩
--    g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ M′ · M′₁ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--  ∎
--
--substitution-lemma {Γ} {τ} {τ′} M (` (S x)) ρ =
--  begin
--    g (mon ⟦ Γ ⊢′ (` (S x)) [ M ] ⟧) ρ
--  ≡⟨ refl ⟩
--    g (mon (project-x Γ x))ρ
--  ≡⟨ key-var-lemma {Γ} {τ} {τ′} {x} {ρ} M ⟩
--    g (mon (g (mon (transform-lemma′ {Γ} {τ} {τ′} ⟦ Γ , τ ⊢′ ` (S x) ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--  ∎
--
--
--substitution-lemma {Γ} {τ} {τ′} M (ƛ_ {A = A} {B} M′) ρ =
--  begin
--    g (mon ⟦ Γ ⊢′ (ƛ M′) [ M ] ⟧) ρ
--  ≡⟨ refl ⟩
--    g (mon (transform-lemma′ {Γ} {A} {B} ⟦ Γ , A ⊢′ (subst (exts (σ {Γ} {A ⇒ B} {τ} {ƛ M′} {M})) M′) ⟧)) ρ
--  ≡⟨ key-λ-lemma {Γ} {A} {B} {τ} {τ′} M M′ ⟩
--    g (mon (g (mon (transform-lemma′ {Γ} {τ} {A ⇒ B} ⟦ Γ , τ ⊢′ ƛ M′ ⟧)) ρ)) (g (mon ⟦ Γ ⊢′ M ⟧) ρ)
--  ∎
--
--substitution-lemma M `zero ρ              = refl
--substitution-lemma M `true ρ              = refl
--substitution-lemma M `false ρ             = refl
--substitution-lemma M (`is-zero M′) ρ      = cong (g (mon z⊥)) (substitution-lemma M M′ ρ)
--substitution-lemma M (`suc M′) ρ          = cong (g (mon s⊥)) (substitution-lemma M M′ ρ)
--substitution-lemma M (`pred M′) ρ         = cong (g (mon p⊥)) (substitution-lemma M M′ ρ)
--substitution-lemma M (μ M′) ρ             = cong (g (mon tarski-continuous)) (substitution-lemma M M′ ρ)
--substitution-lemma {Γ} {τ} {.τ} M (` Z) ρ = refl
--
--sub-corr : {τ τ′ : Type} → (M : ∅ ⊢ τ) → (M′ : ∅ , τ ⊢ τ′) → term-⟦ subst (σ {∅} {τ′} {τ} {M′} {M}) M′ ⟧ ≡ ev-cont ∘ pair-f (transform-lemma′ {∅} {τ} {τ′} ⟦ ∅ , τ ⊢′ M′ ⟧) term-⟦ M ⟧
--
--sub-corr {τ} {τ′} M M′ = cont-fun-extensionality λ ρ → substitution-lemma {∅} M M′ ρ
--
--
--soundness : ∀ {A} → {M : ∅ ⊢ A} {V : ∅ ⊢ A} → (step : M —→ V) → term-⟦ M ⟧ ≡ term-⟦ V ⟧
--soundness (ξ-·₁ {L = L} {L′} {M} L→L′) =
--  begin
--    term-⟦ L · M ⟧
--  ≡⟨ refl ⟩
--    ev-cont ∘ pair-f term-⟦ L ⟧ term-⟦ M ⟧
--  ≡⟨ cong (_∘_ ev-cont) (cong (λ x → pair-f x term-⟦ M ⟧) (soundness L→L′)) ⟩
--    ev-cont ∘ pair-f term-⟦ L′ ⟧ term-⟦ M ⟧
--  ≡⟨ refl ⟩
--    term-⟦ L′ · M ⟧
--  ∎
--
--soundness (β-ƛ {A = A} {B} {N} {W}) =
--  begin
--    term-⟦ (ƛ N) · W ⟧
--  ≡⟨ refl ⟩
--    ev-cont ∘ pair-f term-⟦ ƛ N ⟧ term-⟦ W ⟧
--  ≡⟨ cong (_∘_ ev-cont) (cong (λ x → pair-f x term-⟦ W ⟧) (cont-fun-extensionality (λ x → refl))) ⟩
--    ev-cont ∘ pair-f (transform-lemma′ {∅} {A} {B} ⟦ ∅ , A ⊢′ N ⟧) term-⟦ W ⟧
--  ≡⟨ Eq.sym (sub-corr {A} {B} W N) ⟩
--    term-⟦ subst (λ {A = A₁} → (σ {∅} {B} {A} {N} {W})) N ⟧
--  ≡⟨ refl ⟩
--    term-⟦ N [ W ] ⟧
--  ∎
--
--soundness (ξ-suc {M = M} {M′} M→M′) =
--  begin
--    term-⟦ `suc M ⟧
--  ≡⟨ refl ⟩
--    (s⊥ ∘ term-⟦ M ⟧)
--  ≡⟨ cong (_∘_ s⊥) (soundness M→M′) ⟩
--    (s⊥ ∘ term-⟦ M′ ⟧)
--  ≡⟨ refl ⟩
--    term-⟦ `suc M′ ⟧
--  ∎
--soundness (ξ-pred {M = M} {M′} M→M′) =
--  begin
--    term-⟦ `pred M ⟧
--  ≡⟨ refl ⟩
--    p⊥ ∘ term-⟦ M ⟧
--  ≡⟨ cong (_∘_ p⊥) (soundness M→M′) ⟩
--    p⊥ ∘ term-⟦ M′ ⟧
--  ≡⟨ refl ⟩
--    term-⟦ `pred M′ ⟧
--  ∎
--soundness β-pred₁ = cont-fun-extensionality (λ ⊥ → refl)
--soundness {V = V} (β-pred₂ v) =
--  begin
--    term-⟦ `pred (`suc V) ⟧
--  ≡⟨ refl ⟩
--    p⊥ ∘ (s⊥ ∘ term-⟦ V ⟧)
--  ≡⟨ cont-fun-extensionality (λ ⊥ → p⊥-inv-s⊥) ⟩
--    term-⟦ V ⟧
--  ∎ 
--soundness (ξ-if {B = B} {B′} {x} {y} B→B′) =
--  begin
--    term-⟦ if B then x else y ⟧
--  ≡⟨ refl ⟩
--    if-cont ∘ (pair-f term-⟦ B ⟧ (pair-f term-⟦ x ⟧ term-⟦ y ⟧))
--  ≡⟨ cong (_∘_ if-cont) (cong (λ b → pair-f b (pair-f term-⟦ x ⟧ term-⟦ y ⟧)) (soundness B→B′)) ⟩
--    (if-cont ∘ (pair-f term-⟦ B′ ⟧ (pair-f term-⟦ x ⟧ term-⟦ y ⟧)))
--  ≡⟨ refl ⟩
--    term-⟦ if B′ then x else y ⟧
--  ∎
--soundness {A} {V = V} (β-if₁ {y = y}) =
--  begin
--    term-⟦ if `true then V else y ⟧
--  ≡⟨ refl ⟩
--    (if-cont ∘ (pair-f term-⟦ `true ⟧ (pair-f term-⟦ V ⟧ term-⟦ y ⟧)) )
--  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
--    term-⟦ V ⟧
--  ∎
--soundness {A} {V = V} (β-if₂ {x = x}) =
--  begin
--    term-⟦ if `false then x else V ⟧
--  ≡⟨ refl ⟩
--    if-cont ∘ (pair-f term-⟦ `false ⟧ (pair-f term-⟦ x ⟧ term-⟦ V ⟧))
--  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
--    term-⟦ V ⟧
--  ∎
--soundness {A} (β-μ {N = N}) =
--   begin
--     term-⟦ μ N ⟧
--   ≡⟨ refl ⟩
--     tarski-continuous ∘ term-⟦ N ⟧
--   ≡⟨ cont-fun-extensionality
--     (λ x → lfp-is-fixed { ⟦ A ⟧ } {g (mon term-⟦ N ⟧) x})
--    ⟩
--     ev-cont ∘ pair-f term-⟦ N ⟧ (tarski-continuous ∘ term-⟦ N ⟧)
--   ≡⟨ refl ⟩
--     ev-cont ∘ (pair-f term-⟦ N ⟧ term-⟦ μ N ⟧)
--   ≡⟨ refl ⟩
--     term-⟦ N · (μ N) ⟧
--   ∎
--soundness (ξ-is-zero {M = M} {M′} M→M′) =
--  begin
--    term-⟦ `is-zero M ⟧
--  ≡⟨ refl ⟩
--    z⊥ ∘ term-⟦ M ⟧
--  ≡⟨ cong (_∘_ z⊥) (soundness M→M′) ⟩
--    z⊥ ∘ term-⟦ M′ ⟧
--  ≡⟨ refl ⟩
--    term-⟦ `is-zero M′ ⟧
--  ∎
--soundness β-is-zero₁ =
--  begin
--    term-⟦ `is-zero `zero ⟧
--  ≡⟨ refl ⟩
--    z⊥ ∘ term-⟦ `zero ⟧
--  ≡⟨ cont-fun-extensionality (λ ⊥ → refl) ⟩
--    term-⟦ `true ⟧
--  ∎
--soundness (β-is-zero₂ {M = M} x) =
--  begin
--    term-⟦ `is-zero (`suc M) ⟧
--  ≡⟨ cont-fun-extensionality (λ ⊥ → z⊥∘s⊥-soundness-lemma M x {⊥})⟩
--    term-⟦ `false ⟧
--  ∎
-- 
-- 

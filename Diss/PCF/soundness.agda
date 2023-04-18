module PCF.soundness where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import DomainTheory.BasicObjects.posets-etc
open import DomainTheory.BasicObjects.theorems
open import PCF.pcf
open import DomainTheory.ContinuousFunctions.ev-cont using (ev-cont)
open import DomainTheory.ContinuousFunctions.if-cont using (if-g; if-cont)
open import DomainTheory.ContinuousFunctions.cur-cont using (cur-mon; cur-cont)
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

weaken-σ : {Γ Δ : Context} {τ : Type} (σ : {A : Type} → Γ , τ ∋ A → Δ ⊢ A) → ({A : Type} → Γ ∋ A → Δ ⊢ A)
weaken-σ σ x = σ (S x)

_▷_ : (Γ Δ : Context) → Set
Γ ▷ Δ = ({A : Type} → Δ ∋ A → Γ ∋ A)

--w-⟦_⟧ : {Γ Δ : Context} → (pf : Γ ▷ Δ)  → cont-fun context-⟦ Γ ⟧ context-⟦ Δ ⟧ 

⟦_⟧ₛ : {Δ Γ : Context} → ({A : Type} → Γ ∋ A → Δ ⊢ A) → cont-fun context-⟦ Δ ⟧ context-⟦ Γ ⟧
⟦_⟧ₛ {Γ = ∅} σ = record { mon = record { g = λ x → λ() ; mon = λ x → reflexive (pos context-⟦ ∅ ⟧) } ; lub-preserve = λ c → dependent-function-extensionality (λ()) }
⟦_⟧ₛ {Δ} {Γ = Γ , x} σ = record { mon = record { g = λ δ → λ {fzero → g (mon (⟦ Δ ⊢′ σ Z ⟧))δ; (fsucc n) → (g (mon (⟦ weaken-σ σ ⟧ₛ))δ) n} ; mon = λ x₁ → λ {fzero → mon (mon ⟦ Δ ⊢′ σ Z ⟧) x₁; (fsucc n) → mon (mon ⟦ weaken-σ σ ⟧ₛ) x₁ n} } ; lub-preserve = λ c → dependent-function-extensionality (λ {fzero → lub-preserve ⟦ Δ ⊢′ σ Z ⟧ c; (fsucc n) → cong (λ x → x n) (lub-preserve ⟦ weaken-σ σ ⟧ₛ c)}) } 

_×-cont_ : {A B C D : domain} → cont-fun A B → cont-fun C D → cont-fun (domain-product A C) (domain-product B D)

π₁ : {D₁ D₂ : domain} → cont-fun (domain-product D₁ D₂) D₁
π₁ {D₁} {D₂} = domain-dependent-projection (Fin 2) (domain-projections D₁ D₂) fzero
π₂ : {D₁ D₂ : domain} → cont-fun (domain-product D₁ D₂) D₂
π₂ {D₁} {D₂} = domain-dependent-projection (Fin 2) (domain-projections D₁ D₂) (fsucc fzero)

g (mon (f ×-cont f′)) x fzero = g (mon f) (x fzero)
g (mon (f ×-cont f′)) x (fsucc fzero) = g (mon f′) (x (fsucc fzero))
mon (mon (f ×-cont f′)) x fzero = mon (mon f) (x fzero)
mon (mon (f ×-cont f′)) x (fsucc fzero) = mon (mon f′) (x (fsucc fzero))
lub-preserve (_×-cont_ {A} {B} {C} {D} f f′) c = dependent-function-extensionality
  (λ {        fzero  → lub-preserve f  (chain-of-functions (Fin 2) (domain-projections A C) c fzero)
     ; (fsucc fzero) → lub-preserve f′ (chain-of-functions (Fin 2) (domain-projections A C) c (fsucc fzero))
     })

shift-lemma : {Γ Δ : Context} {τ τ′ : Type} → cont-fun (domain-product context-⟦ Δ ⟧ ⟦ τ ⟧) (domain-product context-⟦ Γ ⟧ ⟦ τ′ ⟧) → cont-fun context-⟦ Δ , τ ⟧ context-⟦ Γ , τ′ ⟧
shift-lemma {Γ} {Δ} {τ} {τ′} f = concat {Γ} {τ′} ∘ (f ∘ unconcat)

weaken-lemma : {Γ Δ : Context} {τ : Type} {σ : {A : Type} → Γ ∋ A → Δ ⊢ A} {i : Fin (length Γ)} {x : A (pos (context-⟦ Δ , τ ⟧))}
  → (g (mon (⟦ weaken-σ {Γ} {Δ , τ} {τ} (exts σ) ⟧ₛ)) x i
    ≡
    g (mon (shift-lemma {Γ} {Δ} {τ} {τ} (pair-f ( ⟦ σ ⟧ₛ ∘ π₁ ) (π₂)))) x (fsucc i))
weaken-lemma {∅} {i = ()}
weaken-lemma {Γ , X} {Δ} {τ} {σ} {i = fzero} {x} = {!g (mon ⟦ Δ , τ ⊢′ weaken-σ (exts σ) Z ⟧) x!}
weaken-lemma {Γ , X} {i = fsucc i} = weaken-lemma { Γ } {i = i}

id : {A : domain} → cont-fun A A
g (mon id) x = x
mon (mon id) x = x
lub-preserve (id {A₁}) c = same-f-same-lub {A₁} {c} {chain-map c (mon (id {A₁}))} refl

lemma-53 : {Γ Δ : Context} {τ : Type} {σ : {A : Type} → Γ ∋ A → Δ ⊢ A} → ⟦_⟧ₛ {Δ , τ} {Γ , τ} (exts σ) ≡ shift-lemma (⟦ σ ⟧ₛ ×-cont id)
lemma-53 {Γ} {Δ} {τ} {σ} = cont-fun-extensionality λ x → dependent-function-extensionality λ {fzero → refl; (fsucc i) →
  begin
    g (mon (⟦ weaken-σ (exts σ) ⟧ₛ)) x i 
  ≡⟨ weaken-lemma {σ = σ} ⟩
    g (mon (shift-lemma {Γ} {Δ} {τ} {τ} (pair-f (⟦ σ ⟧ₛ ∘ π₁) π₂))) x (fsucc i) 
  ≡⟨ refl ⟩
    g (mon (shift-lemma {Γ} {Δ} {τ} {τ} (⟦ σ ⟧ₛ ×-cont (id {⟦ τ ⟧})))) x (fsucc i) 
  ∎}

curry-lemma : ∀ {Γ Δ : Context} {A B : Type}
    {f : cont-fun context-⟦ Γ , A ⟧ ⟦ B ⟧}
    {g : cont-fun context-⟦ Δ ⟧ context-⟦ Γ ⟧}
  → cur-cont (helpful-lemma-blah {Δ} {A} {B} (f ∘ shift-lemma (g ×-cont id {⟦ A ⟧})))
    ≡
    cur-cont (helpful-lemma-blah {Γ} {A} {B} f) ∘ g

curry-lemma {Γ} {Δ} {A} {B} {f = f} {g = g′} =
  cont-fun-extensionality λ x →
    (cont-fun-extensionality (λ x₁ →
      cong
        (g (mon f))
        (dependent-function-extensionality λ {fzero → refl
                                             ; (fsucc n) → refl
                                             })))

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
  ≡⟨ {!comm-triangle t₂ σ!} ⟩
    (if-cont ∘ pair-f (⟦ Γ ⊢′ t ⟧ ∘ ⟦ σ ⟧ₛ) (pair-f (⟦ Γ ⊢′ t₁ ⟧ ∘ ⟦ σ ⟧ₛ) (⟦ Γ ⊢′ t₂ ⟧ ∘ ⟦ σ ⟧ₛ) ))
  ≡⟨ cont-fun-extensionality (λ x → ?) ⟩
    ((if-cont ∘ pair-f ⟦ Γ ⊢′ t ⟧ (pair-f ⟦ Γ ⊢′ t₁ ⟧ ⟦ Γ ⊢′ t₂ ⟧)) ∘ ⟦ σ ⟧ₛ)
    ∎
-}
{-
comm-triangle {Γ} {Δ} (` x) σ = cont-fun-extensionality (λ x₁ → {!!})
comm-triangle {Γ} {Δ} (ƛ_ {A = A} {B} t) σ =
  begin
    cur-cont (helpful-lemma-blah ⟦ Δ , A ⊢′ subst (exts σ) t ⟧)
  ≡⟨ cong (λ x → cur-cont (helpful-lemma-blah {Δ} {A} {B} x)) (comm-triangle t (exts σ)) ⟩
    cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ ⟦ exts σ ⟧ₛ))
  ≡⟨ cong (λ x → cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ x))) lemma-53 ⟩
    cur-cont (helpful-lemma-blah {Δ} {A} {B} (⟦ Γ , A ⊢′ t ⟧ ∘ shift-lemma (⟦ σ ⟧ₛ ×-cont id)))
  ≡⟨ curry-lemma {Γ} {Δ} {A} {B} {⟦ Γ , A ⊢′ t ⟧} {⟦ σ ⟧ₛ } ⟩
    (cur-cont (helpful-lemma-blah {Γ} {A} {B} ⟦ Γ , A ⊢′ t ⟧) ∘ ⟦ σ ⟧ₛ)
  ∎
-}
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

id-σ : {Γ : Context} → ({A : Type} → Γ ∋ A → Γ ⊢ A)
id-σ {∅} ()
id-σ {Γ , τ} x = ` x


weaken-σ-comp : {Γ Δ : Context} {τ : Type} {σ : {A : Type} → Γ , τ ∋ A → Δ ⊢ A} → ⟦ weaken-σ {Γ} {Δ} {τ} σ ⟧ₛ ≡ (π₁ ∘ unconcat) ∘ ⟦ σ ⟧ₛ
weaken-σ-comp  = cont-fun-extensionality (λ x₁ → dependent-function-extensionality (λ i → refl))

abstracted-calc : {Γ Δ : Context} {τ τ′ X : Type} {M : Γ , X ⊢ τ} {x : A (pos (context-⟦ Γ , X ⟧))} {n : Fin (length Γ)}
  → g (mon ((π₁ ∘ unconcat) ∘  ⟦ weaken-σ (σ {Γ , X} {τ} {M}) ⟧ₛ)) x n
    ≡
    g (mon ((π₁ ∘ unconcat) ∘ id)) x n

key-lemma-55 : {Γ : Context} {τ τ′ X : Type} {M : Γ , X ⊢ τ} → ∀ {x : A (pos context-⟦ Γ , X ⟧)} {n : Fin (length Γ)}
  → (λ { fzero → g (mon ⟦ Γ , X ⊢′ weaken-σ (λ {A = A₁} → (σ {Γ , X} {τ} {M})) Z ⟧) x
       ; (fsucc n) → g (mon ⟦ weaken-σ (weaken-σ ((σ {Γ , X} {τ} {M} ))) ⟧ₛ) x n
       })
    ≡
    x

key-lemma-55 {x = x} = dependent-function-extensionality λ {fzero → refl; (fsucc n) → {!!}}

{-
lemma-52 : {Γ Γ′ : Context} {τ : Type} → Γ ⊢ τ → ({A : Type} → Γ ∋ A → Γ′ ⊢ A) → Γ′ ⊢ τ  
lemma-52 (` x) σ = σ x
lemma-52 (ƛ t) σ = ƛ lemma-52 t (exts σ)
lemma-52 (t · t₁) σ = (lemma-52 t σ) · (lemma-52 t₁ σ) 
lemma-52 `zero σ = `zero
lemma-52 (`is-zero t) σ = `is-zero (lemma-52 t σ)
lemma-52 (`suc t) σ = `suc (lemma-52 t σ)
lemma-52 (`pred t) σ = `pred (lemma-52 t σ)
lemma-52 `true σ = `true
lemma-52 `false σ = `false
lemma-52 (if t then t₁ else t₂) σ = if (lemma-52 t σ) then (lemma-52 t₁ σ) else (lemma-52 t₂ σ)
lemma-52 (μ t) σ = μ (lemma-52 t σ)
-}

restrict-context : {Γ : Context} {X : Type} → (A (pos context-⟦ Γ , X ⟧)) → (A (pos context-⟦ Γ ⟧))
restrict-context x = λ i → x (fsucc i)

refl-sublemma : {Γ Δ : Context} {X : Type} {σ : {A : Type} → Γ , X ∋ A → Δ ⊢ A} {x₁ : A (pos (context-⟦ Δ ⟧))} {n : Fin (length Γ)}
  → g (mon ⟦ weaken-σ σ ⟧ₛ) x₁ n ≡ g (mon ⟦ σ ⟧ₛ) x₁ (fsucc n)

refl-sublemma = refl

actual-final-sublemma₁ : {Γ : Context} {X τ : Type} → {x : A (pos (context-⟦ Γ , τ , X ⟧))} {n : Fin (length Γ)}
  → g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , τ , X} ⟧ₛ)) x (fsucc n) ≡ g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , τ} ⟧ₛ)) (restrict-context x) n

actual-final-sublemma₂ : {Γ : Context} {τ τ′ : Type} → {x : A (pos (context-⟦ Γ , τ , τ′ ⟧))} {n : Fin (length Γ)}
  → g (mon (⟦ `_ {Γ} ⟧ₛ ∘ (π₁ ∘ unconcat))) (restrict-context x) n ≡ g (mon (⟦ `_ {Γ , τ} ⟧ₛ ∘ (π₁ ∘ unconcat))) x (fsucc n)

final-sublemma-maybe : {Γ : Context} {X : Type} → {x : A (pos (context-⟦ Γ , X  ⟧))} {n : Fin (length Γ)}
  → g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , X} ⟧ₛ)) x n ≡ g (mon (⟦ `_ {Γ} ⟧ₛ ∘ (π₁ ∘ unconcat))) x n
final-sublemma-maybe {Γ , x} {n = fzero} = refl
final-sublemma-maybe {Γ , x} {X} {x₁} {fsucc n} =
  begin
    g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , x , X} ⟧ₛ)) x₁ (fsucc n)
  ≡⟨ actual-final-sublemma₁ {Γ} {X} {x} {x₁} {n} ⟩
    g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , x} ⟧ₛ)) (restrict-context x₁) n
  ≡⟨ final-sublemma-maybe {Γ} {x} {restrict-context x₁} {n} ⟩
    g (mon (⟦ `_ {Γ} ⟧ₛ ∘ (π₁ ∘ unconcat))) (restrict-context x₁) n
  ≡⟨ actual-final-sublemma₂ {Γ} {x} {X} {x₁} {n} ⟩
    g (mon (⟦ `_ {Γ , x} ⟧ₛ ∘ (π₁ ∘ unconcat))) x₁ (fsucc n)
  ∎

--final-sublemma-maybe {Γ} {Δ , x} {n = fzero} = {!!}
--final-sublemma-maybe {Γ} {Δ , x} {x₁} {n = fsucc n} = {!final-sublemma-maybe {Γ} {Δ} {x₁} {n}!}

final-lemma-maybe : {Γ : Context} → {x : A (pos (context-⟦ Γ ⟧))} → {n : Fin (length Γ)}
  → g (mon ( ⟦ `_ ⟧ₛ)) x n ≡ x n
{-
final-lemma-maybe {∅} = dependent-function-extensionality (λ ())
final-lemma-maybe {Γ , x} {x₂} = dependent-function-extensionality (λ {fzero → refl; (fsucc n) →
  begin
    g (mon (π₁ ∘ unconcat)) (g (mon ⟦ `_ ⟧ₛ) x₂) n
  ≡⟨ cong (λ z → g (mon (π₁ ∘ unconcat)) z n) {!!} ⟩
    g (mon (π₁ ∘ unconcat)) x₂ n
  ≡⟨ refl ⟩
    x₂ (fsucc n)
  ∎})
-}

final-lemma-maybe {Γ , x} {n = fzero} = refl
final-lemma-maybe {Γ , x₁ , x} {x₂} {fsucc n} =
  begin
    g (mon ⟦ weaken-σ `_ ⟧ₛ) x₂ n
  ≡⟨ refl ⟩
    g (mon ((π₁ ∘ unconcat) ∘ ⟦ `_ {Γ , x₁ , x} ⟧ₛ)) x₂ n
  ≡⟨ final-sublemma-maybe {Γ , x₁} {x} {x₂} {n} ⟩
    g (mon (⟦ `_ {Γ , x₁} ⟧ₛ ∘ (π₁ ∘ unconcat))) x₂ n
  ≡⟨ refl ⟩
    g (mon ⟦ `_ ⟧ₛ) (g (mon (π₁ ∘ unconcat)) x₂) n
  ≡⟨ refl ⟩
    g (mon ⟦ `_ ⟧ₛ) (restrict-context x₂) n
  ≡⟨ final-lemma-maybe {Γ , x₁} {restrict-context x₂} {n}⟩
    x₂ (fsucc n)
  ∎
{-
final-lemma-maybe {Γ , x₁ , x} {x₂} {fsucc (fsucc n)} =
  begin
    g (mon ⟦ weaken-σ `_ ⟧ₛ) x₂ (fsucc n)
  ≡⟨ refl ⟩
    g (mon (((π₁ ∘ unconcat) ∘ (π₁ ∘ unconcat)) ∘ ⟦ `_ ⟧ₛ)) x₂ n
  ≡⟨ {!!} ⟩
    g (mon ((π₁ ∘ unconcat) ∘ (π₁ ∘ unconcat))) x₂ n
  ≡⟨ refl ⟩
    x₂ (fsucc (fsucc n))
  ∎
-}
--weaken-σ-comp : {Γ Δ : Context} {τ : Type} {σ : {A : Type} → Γ , τ ∋ A → Δ ⊢ A} → ⟦ weaken-σ {Γ} {Δ} {τ} σ ⟧ₛ ≡ (π₁ ∘ unconcat) ∘ ⟦ σ ⟧ₛ

refl-lemma-maybe : {Γ : Context} {X : Type} → ∀ {x₁ : A (pos (context-⟦ Γ , X ⟧))} {n}
  → g (mon ⟦ weaken-σ (λ x₂ → ` x₂) ⟧ₛ) x₁ n ≡ x₁ (fsucc n)
refl-lemma-maybe {Γ} {X} {x₁} {n} =
  begin
    g (mon ⟦ weaken-σ `_ ⟧ₛ) x₁ n
  ≡⟨ refl-sublemma {Γ} {Γ , X} {X} {`_} ⟩
    g (mon ⟦ `_ ⟧ₛ) x₁ (fsucc n)
  ≡⟨ final-lemma-maybe {Γ , X} {x₁} {(fsucc n)} ⟩
    x₁ (fsucc n)
  ∎

-- g (mon (⟦ Δ ⊢′ σ Z ⟧))δ; (fsucc n) → (g (mon (⟦ weaken-σ σ ⟧ₛ))δ) n}

--comm-id : {Γ : Context} {X : Type} {f : (A (pos context-⟦ Γ , X ⟧)) → A (pos (context-⟦ Γ , X ⟧))} {x₁ : A (pos context-⟦ Γ , X ⟧)} {n : Fin {!!}}
--  → f x₁ (fsucc n) ≡ f (λ i → x₁ (fsucc i)) n



annoying-lemma : {Γ : Context} {X : Type} {x₁ : A (pos context-⟦ Γ , X ⟧)} {n : Fin (length Γ)}
  → g (mon ⟦ id-σ ⟧ₛ) x₁ (fsucc n) ≡ g (mon ⟦ id-σ ⟧ₛ) (λ i → x₁ (fsucc i)) n

annoying-lemma {Γ , x} {X} {x₁} {fzero} = refl
annoying-lemma {Γ , x} {X} {x₁} {fsucc n} =
  begin
    g (mon ⟦ id-σ {Γ , x , X} ⟧ₛ) x₁ (fsucc (fsucc n))
  ≡⟨ refl-lemma-maybe {Γ , x} {X} {x₁} {fsucc n} ⟩
    x₁ (fsucc (fsucc n))
  ≡⟨ Eq.sym (refl-lemma-maybe {Γ} {x} {restrict-context x₁} {n = n}) ⟩
    g (mon ⟦ id-σ {Γ , x} ⟧ₛ) (λ i → x₁ (fsucc i)) (fsucc n)
  ∎

lemma-55′ : (Γ : Context) → ⟦ id-σ {Γ} ⟧ₛ ≡ id
lemma-55-try-2 : (Γ : Context) → ∀ {x₁ : A (pos context-⟦ Γ ⟧) } {n : Fin (length Γ)}
  → g (mon ⟦ id-σ {Γ} ⟧ₛ) x₁ n ≡ x₁ n


lemma-55-try-2 (Γ , x) {n = fzero} = refl
lemma-55-try-2 (Γ , x) {x₁} {fsucc n} =
  begin
    g (mon ⟦ id-σ ⟧ₛ) x₁ (fsucc n)
  ≡⟨ annoying-lemma {Γ} {x} {x₁} {n} ⟩
    g (mon ⟦ id-σ ⟧ₛ) (λ i → x₁ (fsucc i)) n
  ≡⟨ lemma-55-try-2 Γ {restrict-context x₁} {n} ⟩
    x₁ (fsucc n)
  ∎


lemma-55′ ∅ = cont-fun-extensionality λ x → dependent-function-extensionality λ ()
lemma-55′ (Γ , x) = cont-fun-extensionality (λ x₁ → dependent-function-extensionality (λ
  { fzero → refl
  ; (fsucc n) →
    begin
      g (mon ⟦ id-σ ⟧ₛ) x₁ (fsucc n)
    ≡⟨ refl ⟩
      g (mon ⟦ weaken-σ `_ ⟧ₛ ) x₁ n
    ≡⟨ {!!} ⟩ 
      x₁ (fsucc n)
    ≡⟨ refl ⟩
      g (mon (id {context-⟦ Γ , x ⟧})) x₁ (fsucc n)
      ∎
  }))

lemma-55-key : {Γ : Context} {τ : Type} {x : A (pos context-⟦ Γ ⟧)} {n : Fin (length Γ)} {M : Γ ⊢ τ}
  → g (mon ⟦ (σ {Γ} {τ} {M}) ⟧ₛ) x (fsucc n) ≡ x n

lemma-55-key {Γ , x} {n = fzero} = refl
lemma-55-key {Γ , x} {τ} {x = x₁} {fsucc n} {M} =
  begin
    {!!}
  ≡⟨ {!lemma-55-key {?} {τ} {τ′} {?} {n} {M} {M′}!} ⟩
    {!!}
  ≡⟨ {!!} ⟩
    {!!} 

lemma-55′′ : {Γ : Context} {τ : Type} {M : Γ ⊢ τ}
  → ⟦ weaken-σ (σ {Γ} {τ} {M}) ⟧ₛ ≡ id

lemma-55′′ {∅} = cont-fun-extensionality (λ x → dependent-function-extensionality λ ())
lemma-55′′ {Γ , X} {τ} {M} =
  begin ⟦ weaken-σ (σ {Γ , X} {τ} {M}) ⟧ₛ ≡⟨ cont-fun-extensionality (λ x → dependent-function-extensionality (λ {fzero → refl; (fsucc n) →
      begin
        g (mon ⟦ weaken-σ (σ {Γ , X} {τ} {M}) ⟧ₛ) x (fsucc n)
      ≡⟨ refl ⟩
        g (mon ⟦ (σ {Γ , X} {τ} {M}) ⟧ₛ) x (fsucc (fsucc n))
      ≡⟨ lemma-55-key {Γ , X} {τ} {x} {fsucc n} {M} ⟩
        x (fsucc n)
      ∎}))
  ⟩ id
  ∎ 

lemma-55-corr : {Γ : Context} {τ τ′ : Type} {M : Γ ⊢ τ} {M′ : Γ , τ ⊢ τ′}
  → (⟦ Γ , τ ⊢′ M′ ⟧ ∘ ⟦ σ {Γ} {τ} {M} ⟧ₛ) ≡ (⟦ Γ , τ ⊢′ M′ ⟧ ∘ (concat ∘ pair-f id ⟦ Γ ⊢′ M ⟧))

lemma-55-corr {Γ} {τ} {τ′} {M} {M′} = cont-fun-extensionality
  (λ x → cong (λ z → (g (mon ⟦ Γ , τ ⊢′ M′ ⟧) z))
  (dependent-function-extensionality
    λ { fzero → refl
      ; (fsucc n) → cong (λ z → (g (mon z)) x n) (lemma-55′′ {Γ} {τ} {M})
      }
  ))

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


--sub-corr : {τ τ′ : Type} → (M : ∅ ⊢ τ) → (M′ : ∅ , τ ⊢ τ′) → term-⟦ subst (σ {∅} {τ′} {τ} {M′} {M}) M′ ⟧ ≡ ev-cont ∘ pair-f (transform-lemma′ {∅} {τ} {τ′} ⟦ ∅ , τ ⊢′ M′ ⟧) term-⟦ M ⟧
--
--sub-corr {τ} {τ′} M M′ = cont-fun-extensionality λ ρ → substitution-lemma {∅} M M′ ρ

pair-lemma : {τ : Type} {x : poset.A (pos context-⟦ ∅ ⟧)} {W : ∅ ⊢ τ}
  → pair x (g (mon term-⟦ W ⟧) x)
    ≡
    g (mon (pair-f id term-⟦ W ⟧)) x

pair-lemma = dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl})

pair-lemma-corr : {A τ : Type} {N : ∅ , A ⊢ τ} {W : ∅ ⊢ A}
  → ev-cont ∘ pair-f (cur-cont (⟦ ∅ , A ⊢′ N ⟧ ∘ concat)) term-⟦ W ⟧
    ≡
    ⟦ ∅ , A ⊢′ N ⟧ ∘ (concat ∘ pair-f id term-⟦ W ⟧)

pair-lemma-corr {A} {τ} {N} {W} = cont-fun-extensionality
  (λ x₁ → cong (λ z → g (mon ⟦ ∅ , A ⊢′ N ⟧) (g (mon concat) z)) (pair-lemma {A} {x₁} {W}))
     



{-
test-lemma′ = cont-fun-extensionality λ x → {!dependent-function-extensionality!}
-}
{-
test-lemma : ∀ {D₁ D₂ D₃ : domain} {Γ : Context} {τ τ′ : Type} {f : cont-fun context-⟦ Γ , τ ⟧ ⟦ τ′ ⟧} {f′ : cont-fun context-⟦ Γ ⟧ ⟦ τ ⟧}
  → ev-cont ∘ pair-f (transform-lemma′ {Γ} {τ} {τ′} f) f′
    ≡
    f ∘ (concat ∘ (pair-f id f′))
test-lemma = cont-fun-extensionality λ x → {!!}
-}

--Below here typechecks fine
{-
  begin
    (ev-cont ∘ pair-f (transform-lemma′ ⟦ ∅ , A ⊢′ N ⟧) x)
  ≡⟨ cont-fun-extensionality {!!} ⟩
    ((⟦ ∅ , A ⊢′ N ⟧ ∘ concat) ∘ (pair-f id x))
  ≡⟨ cont-fun-extensionality (λ x₁ → refl) ⟩
    (⟦ ∅ , A ⊢′ N ⟧ ∘ (concat ∘ (pair-f id x)))
  ∎
-}
{-
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

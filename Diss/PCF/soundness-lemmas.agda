module PCF.soundness-lemmas where

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
Γ ▷ Δ = ({A : Type} → Γ ∋ A → Δ ∋ A)

⟦_⟧ₛ : {Δ Γ : Context} → ({A : Type} → Γ ∋ A → Δ ⊢ A) → cont-fun context-⟦ Δ ⟧ context-⟦ Γ ⟧
⟦_⟧ₛ {Γ = ∅} σ = record { mon = record { g = λ x → λ() ; mon = λ x → reflexive (pos context-⟦ ∅ ⟧) } ; lub-preserve = λ c → dependent-function-extensionality (λ()) }
⟦_⟧ₛ {Δ} {Γ = Γ , x} σ = record { mon = record { g = λ δ → λ {fzero → g (mon (⟦ Δ ⊢′ σ Z ⟧))δ; (fsucc n) → (g (mon (⟦ weaken-σ σ ⟧ₛ))δ) n} ; mon = λ x₁ → λ {fzero → mon (mon ⟦ Δ ⊢′ σ Z ⟧) x₁; (fsucc n) → mon (mon ⟦ weaken-σ σ ⟧ₛ) x₁ n} } ; lub-preserve = λ c → dependent-function-extensionality (λ {fzero → lub-preserve ⟦ Δ ⊢′ σ Z ⟧ c; (fsucc n) → cong (λ x → x n) (lub-preserve ⟦ weaken-σ σ ⟧ₛ c)}) } 


⟦_⟧ᵣ : {Γ Δ : Context} (ρ : Δ ▷ Γ) → A (pos context-⟦ Γ ⟧) → A (pos context-⟦ Δ ⟧)
⟦_⟧ᵣ {Γ} {Δ , x} ρ γ fzero = g (mon (project-x Γ (ρ Z))) γ
⟦_⟧ᵣ {Γ} {Δ , x} ρ γ (fsucc i) = ⟦  (λ v → ρ (S v)) ⟧ᵣ γ i

_×-cont_ : {A B C D : domain} → cont-fun A B → cont-fun C D → cont-fun (domain-product A C) (domain-product B D)

g (mon (f ×-cont f′)) x fzero = g (mon f) (x fzero)
g (mon (f ×-cont f′)) x (fsucc fzero) = g (mon f′) (x (fsucc fzero))
mon (mon (f ×-cont f′)) x fzero = mon (mon f) (x fzero)
mon (mon (f ×-cont f′)) x (fsucc fzero) = mon (mon f′) (x (fsucc fzero))
lub-preserve (_×-cont_ {A} {B} {C} {D} f f′) c = dependent-function-extensionality
  (λ {        fzero  → lub-preserve f  (chain-of-functions (Fin 2) (domain-projections A C) c fzero)
     ; (fsucc fzero) → lub-preserve f′ (chain-of-functions (Fin 2) (domain-projections A C) c (fsucc fzero))
     })

id : {A : domain} → cont-fun A A
g (mon id) x = x
mon (mon id) x = x
lub-preserve (id {A₁}) c = same-f-same-lub {A₁} {c} {chain-map c (mon (id {A₁}))} refl


shift-lemma : {Γ Δ : Context} {τ τ′ : Type} → cont-fun (domain-product context-⟦ Δ ⟧ ⟦ τ ⟧) (domain-product context-⟦ Γ ⟧ ⟦ τ′ ⟧) → cont-fun context-⟦ Δ , τ ⟧ context-⟦ Γ , τ′ ⟧
shift-lemma {Γ} {Δ} {τ} {τ′} f = concat {Γ} {τ′} ∘ (f ∘ unconcat)

restrict-context : {Γ : Context} {X : Type} → (A (pos context-⟦ Γ , X ⟧)) → (A (pos context-⟦ Γ ⟧))
restrict-context = g (mon (restrict-context-cont))


weaken'-ρ-lemma : {Γ Δ : Context} {τ : Type} (ρ : Γ ▷ Δ)(δ : A (pos context-⟦ Δ , τ ⟧))(i : Fin (length Γ))
            → ⟦ (λ v → S (ρ v)) ⟧ᵣ δ i ≡ ⟦ ρ ⟧ᵣ (restrict-context δ) i
weaken'-ρ-lemma {Γ , x} {Δ} ρ δ fzero = refl
weaken'-ρ-lemma {Γ , x} {Δ} ρ δ (fsucc i) = weaken'-ρ-lemma {Γ} (λ v → ρ (S v)) δ i

restrict-lemma : ∀ {Δ : Context} {τ : Type} {δ : A (pos context-⟦ Δ ⟧)} {x₁ : A (pos ⟦ τ ⟧)} {i} → restrict-context {Δ} {τ} (g (mon concat) (pair δ x₁)) i ≡ δ i
restrict-lemma {Δ , x} {i = fzero} = refl
restrict-lemma {Δ , x} {i = fsucc i} = refl

extend-lemma : (Γ Δ : Context){τ′ : Type}(ρ : Γ ▷ Δ)(δ : A (pos context-⟦ Δ ⟧)) → ∀ {x} {i}
  → (⟦ ext ρ {B = τ′} ⟧ᵣ (g (mon concat) (pair δ x))) i ≡ ((g (mon concat) (pair (⟦ ρ ⟧ᵣ δ) x))) i

extend-lemma Γ Δ ρ δ {i = fzero} = refl
extend-lemma (Γ , x) Δ {τ′} ρ δ {x₁} {fsucc i} =
  begin
    ⟦ (λ v → S (ρ v)) ⟧ᵣ (g (mon concat) (pair δ x₁)) i
  ≡⟨ weaken'-ρ-lemma ρ (g (mon concat) (pair δ x₁)) i  ⟩
    ⟦ ρ ⟧ᵣ (restrict-context {Δ} {τ′} (g (mon concat) (pair δ x₁))) i
  ≡⟨ cong (λ z → ⟦ ρ ⟧ᵣ z i) (dependent-function-extensionality (λ i₁ → restrict-lemma {Δ} {τ′} {δ} {x₁} {i₁})) ⟩
    ⟦ ρ ⟧ᵣ δ i
  ∎

rename-sound : (Γ Δ : Context){τ : Type}(ρ : Γ ▷ Δ)(t : Γ ⊢ τ)(δ : A (pos context-⟦ Δ ⟧))
        → g (mon (⟦ Δ ⊢′ rename ρ t ⟧)) δ ≡ g (mon (⟦ Γ ⊢′ t ⟧)) (⟦ ρ ⟧ᵣ δ)

rename-sound Γ Δ ρ (` Z) δ = refl
rename-sound (Γ , τ) Δ ρ (` (S x)) δ = rename-sound Γ Δ (λ z → ρ (S z)) (` x) δ
rename-sound Γ Δ ρ (ƛ_ {A = A₁} t) δ = cont-fun-extensionality (λ x →
  begin
    g (mon (⟦ Δ , A₁ ⊢′ rename (ext ρ) t ⟧)) (g (mon concat) (pair δ x))
  ≡⟨ rename-sound (Γ , A₁) (Δ , A₁) (ext ρ) t (g (mon concat) (pair δ x)) ⟩
    g (mon ⟦ Γ , A₁ ⊢′ t ⟧) (⟦ ext ρ ⟧ᵣ (g (mon concat) (pair δ x)))
  ≡⟨ cong (g (mon ⟦ Γ , A₁ ⊢′ t ⟧)) (dependent-function-extensionality (λ i → extend-lemma Γ Δ ρ δ {x} {i})) ⟩
    g (mon ⟦ Γ , A₁ ⊢′ t ⟧) (g (mon concat) (pair (⟦ ρ ⟧ᵣ δ) x))
  ∎)
rename-sound Γ Δ ρ (t · t₁) δ = Eq.cong₂ (λ f f′ → g (mon f) f′) (rename-sound Γ Δ ρ t δ) (rename-sound Γ Δ ρ t₁ δ)
rename-sound Γ Δ ρ `zero δ = refl
rename-sound Γ Δ ρ (`is-zero t) δ = cong (g (mon z⊥)) (rename-sound Γ Δ ρ t δ)
rename-sound Γ Δ ρ (`suc t) δ = cong (g (mon s⊥)) (rename-sound Γ Δ ρ t δ)
rename-sound Γ Δ ρ (`pred t) δ = cong (g (mon p⊥)) (rename-sound Γ Δ ρ t δ)
rename-sound Γ Δ ρ `true δ = refl
rename-sound Γ Δ ρ `false δ = refl
rename-sound Γ Δ ρ (if t then t₁ else t₂) δ = cong (g (mon if-cont)) (
  begin
    g (mon (pair-f ⟦ Δ ⊢′ rename ρ t ⟧ (pair-f ⟦ Δ ⊢′ rename ρ t₁ ⟧ ⟦ Δ ⊢′ rename ρ t₂ ⟧))) δ
  ≡⟨ dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl})}) ⟩
    pair (g (mon ⟦ Δ ⊢′ rename ρ t ⟧) δ) (pair (g (mon ⟦ Δ ⊢′ rename ρ t₁ ⟧) δ) (g (mon ⟦ Δ ⊢′ rename ρ t₂ ⟧) δ))
  ≡⟨ cong (λ z → pair z (pair (g (mon ⟦ Δ ⊢′ rename ρ t₁ ⟧) δ) (g (mon ⟦ Δ ⊢′ rename ρ t₂ ⟧) δ))) (rename-sound Γ Δ ρ t δ) ⟩
    pair (g (mon ⟦ Γ ⊢′ t ⟧) (⟦ ρ ⟧ᵣ δ)) (pair (g (mon ⟦ Δ ⊢′ rename ρ t₁ ⟧) δ) (g (mon ⟦ Δ ⊢′ rename ρ t₂ ⟧) δ))
  ≡⟨ cong (λ z → pair (g (mon ⟦ Γ ⊢′ t ⟧) (⟦ ρ ⟧ᵣ δ)) (pair z (g (mon ⟦ Δ ⊢′ rename ρ t₂ ⟧) δ))) (rename-sound Γ Δ ρ t₁ δ) ⟩
    pair (g (mon ⟦ Γ ⊢′ t ⟧) (⟦ ρ ⟧ᵣ δ)) (pair (g (mon ⟦ Γ ⊢′ t₁ ⟧) (⟦ ρ ⟧ᵣ δ)) (g (mon ⟦ Δ ⊢′ rename ρ t₂ ⟧) δ))
  ≡⟨ cong (λ z → pair (g (mon ⟦ Γ ⊢′ t ⟧) (⟦ ρ ⟧ᵣ δ)) (pair (g (mon ⟦ Γ ⊢′ t₁ ⟧) (⟦ ρ ⟧ᵣ δ)) z)) (rename-sound Γ Δ ρ t₂ δ) ⟩
    pair (g (mon ⟦ Γ ⊢′ t ⟧) (⟦ ρ ⟧ᵣ δ)) (pair (g (mon ⟦ Γ ⊢′ t₁ ⟧) (⟦ ρ ⟧ᵣ δ)) (g (mon ⟦ Γ ⊢′ t₂ ⟧) (⟦ ρ ⟧ᵣ δ))) 
  ≡⟨ dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl})}) ⟩
    g (mon (pair-f ⟦ Γ ⊢′ t ⟧ (pair-f ⟦ Γ ⊢′ t₁ ⟧ ⟦ Γ ⊢′ t₂ ⟧))) (⟦ ρ ⟧ᵣ δ)
  ∎)
rename-sound Γ Δ ρ (μ t) δ = cong (g (mon tarski-continuous)) (rename-sound Γ Δ ρ t δ)


⟦id⟧ᵣ : {Γ : Context}(γ : A (pos context-⟦ Γ ⟧))(i : Fin (length Γ)) → ⟦ (λ v → v) ⟧ᵣ γ i ≡ γ i
⟦S⟧-fsucc : {τ : Type} (Γ : Context)(γ : A (pos context-⟦ Γ , τ ⟧))(i : Fin (length Γ))
      → ⟦ S_ ⟧ᵣ γ i ≡ γ (fsucc i)

⟦id⟧ᵣ {Γ , x} γ fzero = refl
⟦id⟧ᵣ {Γ , x} γ (fsucc i) = ⟦S⟧-fsucc Γ γ i

⟦S⟧-fsucc {A} Γ γ i = begin
      ⟦ S_ ⟧ᵣ γ i
  ≡⟨ weaken'-ρ-lemma (λ v → v) γ i ⟩
      ⟦ (λ v → v) ⟧ᵣ (restrict-context γ) i
  ≡⟨ ⟦id⟧ᵣ (restrict-context γ) i ⟩
      γ (fsucc i)
  ∎

weaken-tm-lemma : (Γ : Context){τ B : Type}(t : Γ ⊢ τ)(γ : A (pos context-⟦ Γ , B ⟧))
     → g (mon (⟦ Γ , B ⊢′ rename S_ t ⟧)) γ ≡ g (mon (⟦ Γ ⊢′ t ⟧)) (restrict-context γ)
weaken-tm-lemma Γ {A}{B} t γ =
  begin
     g (mon ⟦ Γ , B ⊢′ rename S_ t ⟧) γ
  ≡⟨ rename-sound Γ (Γ , B) S_ t γ ⟩
     g (mon ⟦ Γ ⊢′ t ⟧) (⟦ S_ ⟧ᵣ γ)
  ≡⟨ cong (g (mon ⟦ Γ ⊢′ t ⟧)) (dependent-function-extensionality (⟦S⟧-fsucc Γ γ)) ⟩
     g (mon (⟦ Γ ⊢′ t ⟧)) (restrict-context γ)
  ∎

inv-cats : {Γ : Context} {τ : Type} → unconcat {Γ} {τ} ∘ concat ≡ id
inv-cats = cont-fun-extensionality (λ x → dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl})

∘-assoc-lemma : {D₁ D₂ D₃ D₄ D₅ D₆ : domain} → ∀ {f₁ : cont-fun D₂ D₁} {f₂ : cont-fun D₃ D₂} {f₃ : cont-fun D₄ D₃} {f₄ : cont-fun D₅ D₄} {f₅ : cont-fun D₆ D₅} → (f₁ ∘ f₂) ∘ ((f₃ ∘ f₄) ∘ f₅) ≡ (f₁ ∘ (f₂ ∘ f₃)) ∘ (f₄ ∘ f₅)
∘-assoc-lemma = cont-fun-extensionality (λ x → refl)

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


needed-sublemma : {D₁ D₂ D₃ : domain} {f₁ : cont-fun D₂ 𝔹⊥} {f₂ f₃ : cont-fun D₂ D₃ } {f′ : cont-fun D₁ D₂} → ∀ {x}
  → g (mon (pair-f (f₁ ∘ f′) (pair-f (f₂ ∘ f′) (f₃ ∘ f′)))) x
    ≡
    g (mon (pair-f f₁ (pair-f f₂ f₃))) (g (mon f′) x)

needed-sublemma = dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl})}

needed-lemma : {D₁ D₂ D₃ : domain} {f₁ : cont-fun D₂ 𝔹⊥} {f₂ f₃ : cont-fun D₂ D₃ } {f′ : cont-fun D₁ D₂}
  → (if-cont ∘ pair-f (f₁ ∘ f′) (pair-f (f₂ ∘ f′) (f₃ ∘ f′)))
    ≡
    (if-cont ∘ pair-f f₁ (pair-f f₂ f₃)) ∘ f′

needed-lemma {f₁ = f₁} {f₂} {f₃} {f′} = cont-fun-extensionality λ x →
  begin
    g (mon if-cont) (g (mon (pair-f (f₁ ∘ f′) (pair-f (f₂ ∘ f′) (f₃ ∘ f′)))) x)
  ≡⟨ cong if-g (needed-sublemma {f₁ = f₁} {f₂} {f₃} {f′} {x}) ⟩
    g (mon if-cont) (g (mon (pair-f f₁ (pair-f f₂ f₃))) (g (mon f′) x))
  ∎


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


weaken'-σ : {Γ Δ : Context} {τ : Type} (σ : {A : Type} → Γ ∋ A → Δ ⊢ A) → ({A : Type} → Γ ∋ A → Δ , τ ⊢ A)
weaken'-σ σ x = rename S_ (σ x)

weaken'-σ-lemma : {Γ Δ : Context} {τ : Type} (σ : {A : Type} → Γ ∋ A → Δ ⊢ A)(δ : A (pos context-⟦ Δ , τ ⟧)) (i : Fin (length Γ))
  → g (mon ⟦ weaken'-σ σ ⟧ₛ) δ i ≡ g (mon (⟦ σ ⟧ₛ)) (restrict-context {Δ} δ) i

weaken'-σ-lemma {Γ = Γ , x}{Δ} σ δ fzero = weaken-tm-lemma Δ (σ Z) δ
weaken'-σ-lemma {Γ , x} σ δ (fsucc i) = weaken'-σ-lemma {Γ} (weaken-σ σ) δ i


lemma-53 : {Γ Δ : Context} {τ : Type} {σ : {A : Type} → Γ ∋ A → Δ ⊢ A} → ⟦_⟧ₛ {Δ , τ} {Γ , τ} (exts σ) ≡ shift-lemma (⟦ σ ⟧ₛ ×-cont id)
lemma-53 {Γ} {Δ} {τ} {σ} = cont-fun-extensionality λ x → dependent-function-extensionality λ {fzero → refl; (fsucc i) →
  begin
    g (mon (⟦ weaken'-σ {Γ} {Δ} {τ} σ ⟧ₛ)) x i
  ≡⟨ weaken'-σ-lemma {Γ} {Δ} {τ} σ x i ⟩
    g (mon ⟦ σ ⟧ₛ) (restrict-context x) i
  ≡⟨ refl ⟩
    g (mon (shift-lemma {Γ} {Δ} {τ} {τ} (⟦ σ ⟧ₛ ×-cont (id {⟦ τ ⟧})))) x (fsucc i) 
  ∎}

lemma-55 : {Γ : Context} → (γ : A (pos (context-⟦ Γ ⟧))) (i : (Fin (length Γ))) → g (mon (⟦ `_ ⟧ₛ)) γ i ≡ γ i
lemma-55 {Γ , x} γ fzero = refl
lemma-55 {Γ , x} γ (fsucc i) =
  begin
    g (mon (⟦ `_ ⟧ₛ)) γ (fsucc i)
  ≡⟨⟩
    g (mon (⟦ weaken'-σ `_ ⟧ₛ)) γ i
  ≡⟨ weaken'-σ-lemma `_ γ i ⟩
    g (mon (⟦ `_ ⟧ₛ)) (restrict-context {Γ} γ) i
  ≡⟨ lemma-55 {Γ} (restrict-context {Γ} γ) i ⟩
    restrict-context {Γ} γ i
  ≡⟨⟩
    γ (fsucc i)
  ∎


lemma-55-corr : {Γ : Context} {τ τ′ : Type} {M : Γ ⊢ τ} {M′ : Γ , τ ⊢ τ′}
  → (⟦ Γ , τ ⊢′ M′ ⟧ ∘ ⟦ σ {Γ} {τ} {M} ⟧ₛ) ≡ (⟦ Γ , τ ⊢′ M′ ⟧ ∘ (concat ∘ pair-f id ⟦ Γ ⊢′ M ⟧))

lemma-55-corr {Γ} {τ} {τ′} {M} {M′} = cont-fun-extensionality
  (λ x → cong (λ z → (g (mon ⟦ Γ , τ ⊢′ M′ ⟧) z))
  (dependent-function-extensionality
    λ { fzero → refl
      ; (fsucc n) → lemma-55 {Γ} x n
      }
  ))

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

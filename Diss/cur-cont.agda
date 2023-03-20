module cur-cont where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import posets2
open import useful-functions using (pair)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain

cur-cont : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → cont-fun D′ (function-domain D E)

cur-mon : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → monotone-fun (pos D′) (pos (function-domain D E))

helpful-chain-1 : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → chain (pos D) → A (pos D′) → chain (pos (domain-product D′ D))
helpful-chain-1 f c d′ = record
  { monotone = record
    { g = λ x i → pair d′ ((g (monotone c) x)) i
    ; mon = {!!}
    }
  }


helpful-chain-2 : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → chain (pos D′) → A (pos D) → chain (pos (domain-product D′ D))
helpful-chain-2 {D} f c d = record
  { monotone = record
    { g = λ x i → pair ((g (monotone c)) x) d i
    ; mon = λ x → (λ { fzero → mon (monotone c) x ; (fsucc fzero) → reflexive (pos D) })
    }
  }


g (mon (g (cur-mon {D} {D′} {E} f) d′)) d = g (mon f) (pair d′ d)
mon (mon (g (cur-mon {D} {D′} {E} f) d′)) a≤a′ = mon (mon f) λ {fzero → reflexive (pos D′); (fsucc fzero) → a≤a′}
lub-preserve (g (cur-mon {D} {D′} {E} f) d′) c =
  begin
    g (mon (g (cur-mon f) d′)) (⊔ (chain-complete D c))
  ≡⟨ refl ⟩
    g (mon f) (pair d′ (⊔ (chain-complete D c)))
  ≡⟨ cong (g (mon f)) (dependent-function-extensionality ((λ { fzero → {!!} ; (fsucc fzero) → refl }))) ⟩
    g (mon f) (⊔ (chain-complete (domain-product D′ D) (helpful-chain-1 f c d′))) 
  ≡⟨ lub-preserve f (helpful-chain-1 f c d′) ⟩
    ⊔ (chain-complete E (chain-map c (mon (g (cur-mon f) d′))))
  ∎

mon (cur-mon {D} {D′} {E} f) a≤a′ = mon (mon f) λ {fzero → a≤a′; (fsucc fzero) → reflexive (pos D)}

         
mon (cur-cont {D} {D′} {E} f) = cur-mon {D} {D′} {E} f
lub-preserve (cur-cont {D} {D′} {E} f) c = cont-fun-extensionality λ x →
  begin
    g (mon (g (mon (cur-cont f)) (⊔ (chain-complete D′ c)))) x
  ≡⟨ refl ⟩
    g (mon f) (pair (⊔ (chain-complete D′ c)) x)
  ≡⟨ cong (g (mon f)) (dependent-function-extensionality (λ { fzero → refl ; (fsucc fzero) → {!!} })) ⟩
    g (mon f) (⊔ (chain-complete (domain-product D′ D) (helpful-chain-2 f c x)))
  ≡⟨ lub-preserve f (helpful-chain-2 f c x) ⟩
    ⊔ (chain-complete E (chain-map (helpful-chain-2 f c x) (mon f)))
  ≡⟨ same-f-same-lub
       {E} {chain-map (helpful-chain-2 f c x) (mon f)} {chain-of-fₙ[d] D E (chain-map c (cur-mon f)) x}
       refl
   ⟩
    ⊔-chain-of-fₙ[d] D E (chain-map c (cur-mon f)) x
  ≡⟨ refl ⟩
    g (mon (⊔ (chain-complete (function-domain D E)(chain-map c (mon (cur-cont f)))))) x
  ∎
                                 

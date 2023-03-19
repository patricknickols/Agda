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

g (mon (g (cur-mon {D} {D′} {E} f) d′)) d = g (mon f) (pair d′ d)
mon (mon (g (cur-mon {D} {D′} {E} f) d′)) a≤a′ = mon (mon f) λ {fzero → reflexive (pos D′); (fsucc fzero) → a≤a′}
lub-preserve (g (cur-mon {D} {D′} {E} f) d′) c =
  begin
    g (mon (g (cur-mon f) d′)) (⊔ (chain-complete D c))
  ≡⟨ {!!} ⟩
    {!!}
  ≡⟨ {!!} ⟩
    ⊔ (chain-complete E (chain-map c (mon (g (cur-mon f) d′))))
  ∎

mon (cur-mon {D} {D′} {E} f) a≤a′ = mon (mon f) λ {fzero → a≤a′; (fsucc fzero) → reflexive (pos D)}

         
mon (cur-cont {D} {D′} {E} f) = cur-mon {D} {D′} {E} f
lub-preserve (cur-cont {D} {D′} {E} f) c =
  begin
    g (mon (cur-cont f)) (⊔ (chain-complete D′ c))
  ≡⟨ {!!} ⟩
    ⊔ (chain-complete (function-domain D E) (chain-map c (mon (cur-cont f))))
  ∎
                                 

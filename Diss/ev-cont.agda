module ev-cont where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import posets2
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain

ev-cont : ∀ {D E} → cont-fun (domain-product (function-domain D E) D) E
ev-mon : ∀ {D E} → monotone-fun (pos (domain-product (function-domain D E) D)) (pos E)

g (ev-mon {D} {E}) x = g (mon (x fzero)) (x (fsucc fzero))
mon (ev-mon {D} {E}) {x} {y} a≤a′ = transitive (pos E)
                                      (mon (mon (x fzero)) (a≤a′ (fsucc fzero)))
                                      (a≤a′ fzero {y (fsucc fzero)})

fₙ,dₙ→fₙ[dₙ] : ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → chain (pos E)
fₙ,dₙ→fₙ[dₙ] c = chain-map c ev-mon

fₙ,dₙ→fₙ[⊔dₙ] : ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → chain (pos E)
fₙ,dₙ→fₙ[⊔dₙ] {D} {E} c = record
  { monotone = record
    { g = λ n → g (mon (g (monotone (proj₁-chain c)) n)) (⊔ (domain.chain-complete D (proj₂-chain c)))
    ; mon = λ a≤a′ → mon (monotone c) a≤a′ fzero
    }
  }

fₙ,dₙ→fᵢdⱼ-chain : ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → ℕ → chain (pos E) 
fₙ,dₙ→fᵢdⱼ-chain {D} {E} c i = record
  { monotone = record
    { g = λ j → g (mon (g (monotone (posets2.proj₁-chain c)) i)) (g (monotone (posets2.proj₂-chain c)) j)
    ; mon = λ a≤a′ → mon (mon (g (monotone c) i fzero)) (mon (monotone c) a≤a′ (fsucc fzero))
    }
  }

fₙ,dₙ→⊔ⱼfᵢdⱼ :  ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → chain (pos E)

fₙ,dₙ→⊔ⱼfᵢdⱼ {D} {E} c = record
  { monotone = record
    { g = λ i → ⊔ (chain-complete E (fₙ,dₙ→fᵢdⱼ-chain {D} {E} c i))
    ; mon = λ {a} {a′} a≤a′ → lub2 (chain-complete E (fₙ,dₙ→fᵢdⱼ-chain c a))
      λ {n} → poset.transitive (pos E)
        (mon (monotone c) a≤a′ (fzero))
        (lub1 (chain-complete E (fₙ,dₙ→fᵢdⱼ-chain c a′)))
    }
  }

fᵢdⱼ : {D E : domain} → chain (pos (domain-product (function-domain D E) D)) → monotone-fun posets2.nats²-pos (pos E)
g (fᵢdⱼ c) ⟨ i , j ⟩ = let fᵢ = g (mon (g (monotone (proj₁-chain c)) i)) in
                       let dⱼ = g (monotone (proj₂-chain c)) j in
                       fᵢ dⱼ

mon (fᵢdⱼ {D} {E} c) {a} {a′} ⟨ i≤i′ , j≤j′ ⟩ =
  transitive (pos E)
    ((mon (monotone c) i≤i′) fzero)
    (mon (mon (g (monotone c) (proj₁ a′) fzero)) (mon (monotone c) j≤j′ (fsucc fzero)))



mon (ev-cont {D} {E}) = ev-mon {D} {E}
lub-preserve (ev-cont {D} {E}) c =
   let ev = monotone-fun.g (ev-mon {D} {E}) in
   let D→E = function-domain D E in
   let fₙ-chain = proj₁-chain {D→E} {D} c in
   let dₙ-chain = proj₂-chain {D→E} {D} c in
   let ⊔fₙ = posets2.function-domain-⊔ D E fₙ-chain in
   let ⊔dₙ = posets2.lub.⊔ (domain.chain-complete D dₙ-chain) in
   let ev[⊔fₙ,⊔dₙ] = ev (posets2.lub.⊔ (domain.chain-complete (domain-product (D→E) D) c)) in
   let [⊔fₙ][⊔dₙ] = monotone-fun.g (cont-fun.mon ⊔fₙ) ⊔dₙ in
   let ⊔[fₙ[⊔dₙ]] = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→fₙ[⊔dₙ] c)) in
   let ⊔ᵢ⊔ⱼfᵢdⱼ = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→⊔ⱼfᵢdⱼ c)) in
   let ⊔fₙdₙ = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→fₙ[dₙ] c)) in
   let ⊔ev[fₙ,dₙ] = posets2.lub.⊔ (domain.chain-complete E (chain-map c ev-mon)) in
  begin
    ev[⊔fₙ,⊔dₙ]
  ≡⟨ refl ⟩
    [⊔fₙ][⊔dₙ]
  ≡⟨ same-f-same-lub
       {E} {posets2.chain-of-fₙ[d] D E fₙ-chain ⊔dₙ} {fₙ,dₙ→fₙ[⊔dₙ] c}
       refl
   ⟩
    ⊔[fₙ[⊔dₙ]]
  ≡⟨ same-f-same-lub
       {E} {fₙ,dₙ→fₙ[⊔dₙ] c} {fₙ,dₙ→⊔ⱼfᵢdⱼ c}
       (posets2.function-extensionality λ n → lub-preserve (g (monotone fₙ-chain) n) dₙ-chain)
   ⟩
    ⊔ᵢ⊔ⱼfᵢdⱼ
  ≡⟨ same-f-same-lub
        {E} {fₙ,dₙ→⊔ⱼfᵢdⱼ c} {posets2.chain-⊔fₙₖ-with-n-fixed E (fᵢdⱼ c)}
        (posets2.function-extensionality (λ x →
           same-f-same-lub
             {E} {fₙ,dₙ→fᵢdⱼ-chain c x} {posets2.chain-fₘₙ-with-m-fixed E (fᵢdⱼ c) x}
             refl))
   ⟩
    ⊔ ((chain-complete E) (posets2.chain-⊔fₙₖ-with-n-fixed E (fᵢdⱼ c)))
  ≡⟨ posets2.diagonalising-lemma-1 E (fᵢdⱼ c) ⟩
    ⊔ ((chain-complete E) (posets2.fₖₖ-chain E (fᵢdⱼ c)))
  ≡⟨ same-f-same-lub
       {E} {posets2.fₖₖ-chain E (fᵢdⱼ c)} {fₙ,dₙ→fₙ[dₙ] c}
       (posets2.function-extensionality (λ x → refl) )
   ⟩
    ⊔fₙdₙ
  ≡⟨ refl ⟩
    ⊔ev[fₙ,dₙ]
    ∎

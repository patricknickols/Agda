module DomainTheory.ContinuousFunctions.fix-cont where

open import DomainTheory.BasicObjects.posets-etc
open import DomainTheory.BasicObjects.theorems

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; cong)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; suc; zero)
open import misc

open poset
open domain
open lub
open monotone-fun
open cont-fun
open least-element
open pre-fixed
open least-pre-fixed


tarski-continuous : ∀ {P : domain} → cont-fun (function-domain P P) P

tarski-mon : ∀ (P : domain) → monotone-fun (pos (function-domain P P)) (pos P)

tarski-lub-preserve : ∀ (P : domain)
  → (c : chain (pos (function-domain P P)))
  → g (tarski-mon P) (⊔ (chain-complete (function-domain P P) c)) ≡ ⊔ (chain-complete P (chain-map c (tarski-mon P)))


fix-f′-is-pre-fixed : ∀ (P : domain) → (f : cont-fun P P) → (f′ : cont-fun P P) → (f⊑f′ : function-⊑ f f′) → R (pos P) (g (mon f) (⊔ (chain-complete P (tarski-chain-of-fⁿ⊥ P f′)))) (⊔ (chain-complete P (tarski-chain-of-fⁿ⊥ P f′)))

fix-f′-is-pre-fixed P f f′ f⊑f′ = transitive (pos P) ((f⊑f′ {d (lfp1 (tarski-fix P f′))})) (pre-fix (lfp1 (tarski-fix P f′)))


tarski-mon P = record { g =  λ (cont-fun : cont-fun P P) → d (lfp1 (tarski-fix P cont-fun))
                      ; mon = λ {f} {f′} f⊑f′ → lfp2 (tarski-fix P f) (fix-f′-is-pre-fixed P f f′ f⊑f′)
                      }


fix⋃fₙ⊑⋃fixfₙ : (P : domain) → (c : chain (function-pos P P)) → (d : chain (function-pos P P))
  → R (pos P)
     (⊔ (chain-complete P (tarski-chain-of-fⁿ⊥ P (function-domain-⊔ P P d))))
     (⊔ (chain-complete P (chain-map d (tarski-mon P))))

⋃fixfₙ-is-pre-fix : (P : domain) → (c : chain (function-pos P P)) → (d : chain (function-pos P P))
  → R (pos P)
    (g (mon (function-domain-⊔ P P d))
     (⊔
      (chain-complete P
       (chain-map d
        (tarski-mon P)))))
    (⊔
     (chain-complete P
      (chain-map d
        (tarski-mon P))))


chain-of-fₖ[fixfₖ] : (P : domain) → (d : chain (function-pos P P)) → chain (pos P)

chain-of-fₖ[fixfₖ] P d = record { g = λ k → g (mon (g d k)) ((g (tarski-mon P)) (g d k))
                                ; mon = λ {a} {a′} a≤a′ →
                                    transitive (pos P)
                                      (mon d a≤a′)
                                      ((mon (mon (g d a′)))(mon (tarski-mon P) (mon d a≤a′)))
                                }
                                           

⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] : (P : domain) → (d : chain (function-pos P P)) →
  ⊔-chain-of-fₙ[d] P P d (⊔ (chain-complete P (chain-map d (tarski-mon P))))
  ≡
  ⊔ (chain-complete P (chain-of-fₖ[fixfₖ] P d))

m,n→fₘfixfₙ : (P : domain) → (c : chain (function-pos P P)) → monotone-fun nats²-pos (pos P)

m,n→fₘfixfₙ P c = record { g = λ m,n
                           → let m = Data.Product.proj₁ m,n in
                             let n = Data.Product.proj₂ m,n in
                             let f = g c in 
                             let fixfₙ = d (lfp1 (tarski-fix P (f n))) in
                           g (mon (f m)) (fixfₙ)     
                         ; mon = λ {m,n} {m′,n′} m,n≤m′,n′
                           → let m≤m′ = Data.Product.proj₁ m,n≤m′,n′ in
                             let n≤n′ = Data.Product.proj₂ m,n≤m′,n′ in
                             let m′ = Data.Product.proj₁ m′,n′ in
                           transitive (pos P) (mon c m≤m′) ((mon (mon (g c m′))) (mon (tarski-mon P) (mon c n≤n′)))
                         }

⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] P d =
  let ⋃ = chain-complete P in
  let [⋃fₘ][⋃fixfₙ] = ⊔-chain-of-fₙ[d] P P d (⊔ (⋃ (chain-map d (tarski-mon P)))) in
  begin
    [⋃fₘ][⋃fixfₙ]
  ≡⟨ same-f-same-lub {P}
      {chain-of-fₙ[d] P P d (⊔ (⋃(chain-map d (tarski-mon P))))}
      {chain-⊔fₙₖ-with-n-fixed P (m,n→fₘfixfₙ P d)}
      (function-extensionality λ n →
       Eq.trans
       (lub-preserve (g d n) (chain-map d (tarski-mon P)))
       (same-f-same-lub {P}
        {chain-map (chain-map d (tarski-mon P)) (mon (g d n))}
        {chain-fₘₙ-with-m-fixed P (m,n→fₘfixfₙ P d) n}
        Eq.refl)) ⟩
    ⊔ (⋃ (chain-⊔fₙₖ-with-n-fixed P (m,n→fₘfixfₙ P d)))
  ≡⟨ diagonalising-lemma-1 P (m,n→fₘfixfₙ P d) ⟩
    ⊔ (⋃ (fₖₖ-chain P (m,n→fₘfixfₙ P d)))
  ≡⟨ same-f-same-lub {P} {fₖₖ-chain P (m,n→fₘfixfₙ P d)} {chain-of-fₖ[fixfₖ] P d} Eq.refl ⟩
    ⊔ (⋃ (chain-of-fₖ[fixfₖ] P d))
  ∎ 

⋃fixfₙ-is-pre-fix P c d = a≡b≤c→a≤c {A (pos P)} {R (pos P)} (⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] P d) (same-f-same-lub-≤ P (chain-of-fₖ[fixfₖ] P d) (chain-map d (tarski-mon P)) λ n → pre-fix (lfp1 (tarski-fix P (g d n)))) 


fix⋃fₙ⊑⋃fixfₙ P c d = lfp2 (tarski-fix P (function-domain-⊔ P P d)) (⋃fixfₙ-is-pre-fix P c d)


tarski-lub-preserve P c = lub-preserve (remark-237 ((function-domain P P)) P c (tarski-mon P) (fix⋃fₙ⊑⋃fixfₙ P c)) c

tarski-continuous {P} = record { mon = tarski-mon P
                               ; lub-preserve = tarski-lub-preserve P
                               }


scott-induction : {D : domain}
  → (f : cont-fun D D) (P : A (pos D) → Set)
  → P (⊥ (bottom D))
  → ({n : ℕ} → (P (iterate n (g (mon f)) (⊥ (bottom D)))) → P (iterate (suc n) (g (mon f)) (⊥ (bottom D))))
  → ((c : chain (pos D)) → ((n : ℕ) → (P (g c n))) → P (⊔ (chain-complete D c)))
  → P (g (tarski-mon D) f)

scott-induction-1 : {D : domain}
  → (f : cont-fun D D) (P : A (pos D) → Set)
  → P (⊥ (bottom D))
  → ({n : ℕ} → (P (iterate n (g (mon f)) (⊥ (bottom D)))) → P (iterate (suc n) (g (mon f)) (⊥ (bottom D))))
  → ((n : ℕ) → P (iterate n (g (mon f)) (⊥ (bottom D))))

scott-induction-1 f P P⊥ induction zero = P⊥
scott-induction-1 f P P⊥ induction (suc n) = induction {n} (scott-induction-1 f P P⊥ (λ {n} → induction {n}) n)

scott-induction {D} f P P⊥ induction chain-closed = chain-closed (tarski-chain-of-fⁿ⊥ D f) (scott-induction-1 f P P⊥ λ {n} → induction {n})



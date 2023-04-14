module DomainTheory.BasicObjects.theorems where

open import DomainTheory.BasicObjects.posets-etc
open import misc
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (refl; _≡_; cong)

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open least-element
open eventually-constant
open pre-fixed
open least-pre-fixed

product-equality : {S₁ S₂ : Set} {a a′ : S₁} {b b′ : S₂} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
product-equality {a} {a′} {b} {b′} Eq.refl Eq.refl = Eq.refl

domain-product : domain → domain → domain

domain-projections : (D₁ D₂ : domain) → (Fin 2) → domain
domain-projections D₁ D₂ fzero = D₁
domain-projections D₁ D₂ (fsucc x) = D₂

domain-dependent-product : (I : Set) → (I → domain) → domain
domain-dependent-product-pos : (I : Set) → (I → domain) → poset
domain-dependent-R : (I : Set) → (f : I → domain) → ((i : I) → (A (pos (f i))))  → ((i : I) → (A (pos (f i)))) → Set

domain-dependent-R I f p₁ p₂ = (i : I) → R (pos (f i)) (p₁ i) (p₂ i)

domain-product D₁ D₂ = domain-dependent-product (Fin 2) (domain-projections D₁ D₂)

product-pos : domain → domain → poset
product-pos D₁ D₂ = pos (domain-product D₁ D₂)


domain-dependent-refl : (I : Set) → (f : I → domain) → {p : (i : I) → (A (pos (f i)))} → domain-dependent-R I f p p
domain-dependent-refl I f i = reflexive (pos (f i))

domain-dependent-antisym : (I : Set) → (f : I → domain) → {p₁ p₂ : (i : I) → (A (pos (f i)))} → domain-dependent-R I f p₁ p₂ → domain-dependent-R I f p₂ p₁ → p₁ ≡ p₂
domain-dependent-antisym I f p₁≤p₂ p₂≤p₁ = dependent-function-extensionality λ i → antisymmetric (pos (f i)) (p₁≤p₂ i) (p₂≤p₁ i)


domain-dependent-trans : (I : Set) → (f : I → domain) → {p₁ p₂ p₃ : (i : I) → (A (pos (f i)))} → domain-dependent-R I f p₁ p₂ → domain-dependent-R I f p₂ p₃ → domain-dependent-R I f p₁ p₃
domain-dependent-trans I f p₁≤p₂ p₂≤p₃ = λ i → transitive (pos (f i)) (p₁≤p₂ i) (p₂≤p₃ i)


domain-dependent-product-pos I f = record
                                   { A = (i : I) → (A (pos (f i)))
                                   ; R = domain-dependent-R I f
                                   ; reflexive = domain-dependent-refl I f
                                   ; antisymmetric = domain-dependent-antisym I f
                                   ; transitive = domain-dependent-trans I f
                                   }

chain-of-functions : (I : Set) → (f : I → domain) → (c : chain (domain-dependent-product-pos I f)) → (i : I) → chain (pos (f i))
chain-of-functions I f c i = record
                                      { g = λ n → g c n i
                                      ; mon = λ a≤a′ → (mon c a≤a′) i
                                      }
                                    


domain-dependent-product I f = record { pos = domain-dependent-product-pos I f
                                      ; chain-complete = λ c → record
                                        { ⊔ = λ i → ⊔ (chain-complete (f i) (chain-of-functions I f c i))
                                        ; lub1 = λ i → lub1 (chain-complete (f i) (chain-of-functions I f c i))
                                        ; lub2 = λ x i → lub2 (chain-complete (f i) (chain-of-functions I f c i)) (x i)
                                        }
                                      ; bottom = record
                                        { ⊥ = λ i → ⊥ (bottom (f i))
                                        ; ⊥-is-bottom = λ i → ⊥-is-bottom (bottom (f i))
                                        }
                                      }


proj₁-chain : {D₁ D₂ : domain} → chain (product-pos D₁ D₂) → chain (pos D₁)
proj₁-chain c = record { g = λ n → g c n fzero
                       ; mon = λ x → mon c x fzero
                       }
                       

proj₂-chain : {D₁ D₂ : domain} → chain (product-pos D₁ D₂) → chain (pos D₂)
proj₂-chain c = record { g = λ n → g c n (fsucc fzero)
                       ; mon = λ x → mon c x (fsucc fzero)
                       }

nats²-R : ℕ × ℕ → ℕ × ℕ → Set
nats²-R (m , n) (m′ , n′) = (m ≤ m′) × (n ≤ n′) 

nats²-R-antisymmetric : {a b : ℕ × ℕ} → nats²-R a b → nats²-R b a → a ≡ b
nats²-R-antisymmetric (m≤m′ , n≤n′) (m′≤m , n′≤n) = product-equality (antisym-≤ m≤m′ m′≤m) (antisym-≤ n≤n′ n′≤n)

nats²-R-transitive : {a b c : ℕ × ℕ} → nats²-R a b → nats²-R b c → nats²-R a c
nats²-R-transitive (a₁≤b₁ , a₂≤b₂) (b₁≤c₁ , b₂≤c₂) = trans-≤ a₁≤b₁ b₁≤c₁ , trans-≤ a₂≤b₂ b₂≤c₂

nats²-pos : poset
nats²-pos = record
              { A = ℕ × ℕ
              ; R = nats²-R
              ; reflexive = refl-≤ , refl-≤
              ; antisymmetric = nats²-R-antisymmetric
              ; transitive = nats²-R-transitive
              }

chain-fₘₙ-with-m-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (ℕ → chain (pos P))
chain-fₘₙ-with-n-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (ℕ → chain (pos P))

chain-fₘₙ-with-m-fixed P double-index-fun m = record { g = λ n → (g double-index-fun) (m , n)
                                                     ; mon = λ a≤a′ → mon (double-index-fun) (refl-≤ , a≤a′)
                                                     }
                                                                 


chain-fₘₙ-with-n-fixed P double-index-fun n = record { g = λ m → (g double-index-fun) (m , n)
                                                     ; mon = λ a≤a′ → mon (double-index-fun) (a≤a′ , refl-≤)
                                                     }
                                                                  
chain-⊔fₙₖ-with-n-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (chain (pos P))
chain-⊔fₙₖ-with-n-fixed P double-index-fun = let ⋃ = chain-complete P in
  record
    { g = λ n → ⊔ (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n))
    ; mon = λ {n} {n′} n≤n′ → lub2
                                (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n)) λ {n₁} →
                                  (transitive (pos P))
                                    (mon double-index-fun (n≤n′ , refl-≤))
                                    (lub1 (chain-complete P (chain-fₘₙ-with-m-fixed P double-index-fun n′)) {n₁})
    }
  


chain-⊔fₖₙ-with-n-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (chain (pos P))
chain-⊔fₖₙ-with-n-fixed P double-index-fun = let ⋃ = chain-complete P in
  record
    { g = λ m → ⊔ (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m))
    ; mon = λ {m} {m′} m≤m′ → lub2
                                (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m)) λ {n} →
                                  (transitive (pos P))
                                    (mon double-index-fun (refl-≤ , m≤m′))
                                    (lub1 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m′)) {n})
    }
  

fₖₖ-chain : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → chain (pos P)
fₖₖ-chain P double-index-fun = record { g = λ x → (g double-index-fun) (x , x)
                                      ; mon = λ a≤a′ → (mon double-index-fun) (a≤a′ , a≤a′)
                                      }
                                     

diagonalising-lemma-1 : (P : domain)
  → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₙₖ-with-n-fixed P double-index-fun))
    ≡
    ⊔ ((chain-complete P) (fₖₖ-chain P double-index-fun))

diagonalising-lemma-2 : (P : domain)
  → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₖₙ-with-n-fixed P double-index-fun))
    ≡
    ⊔ ((chain-complete P) (fₖₖ-chain P double-index-fun))

diagonalising-lemma : (P : domain)
  → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₙₖ-with-n-fixed P double-index-fun))
    ≡
    ⊔ ((chain-complete P) (chain-⊔fₖₙ-with-n-fixed P double-index-fun))

swap-≡ : {A : Set} {a b : A} → a ≡ b → b ≡ a
swap-≡ Eq.refl = Eq.refl


dₘₙ≤⊔dₖₖ : {m n : ℕ} (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → R (pos P) (g (double-index-fun) (m , n)) (⊔ (chain-complete P (fₖₖ-chain P double-index-fun)))

dₘₙ≤⊔dₖₖ {m} {n} P double-index-fun = let ⋃ = chain-complete P in
  transitive (pos P)
   (mon double-index-fun (a≤max-a-b m , a≤b≡c→a≤c (a≤max-a-b {m} n) (max-sym n m)))
   (lub1 (⋃ (fₖₖ-chain P double-index-fun)) {max m n})

diagonalising-lemma-1 P double-index-fun = let ⋃ = chain-complete P in 
  antisymmetric (pos P)
    (lub2
      (⋃ (chain-⊔fₙₖ-with-n-fixed P double-index-fun))
      (λ {n} → lub2
        (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n))
        (λ {n₁} → dₘₙ≤⊔dₖₖ {n} {n₁} P double-index-fun)))
    (lub2
      (⋃ (fₖₖ-chain P double-index-fun))
      λ {n} → transitive (pos P)
                (lub1 (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n)) {n})
                (lub1 (⋃ (chain-⊔fₙₖ-with-n-fixed P double-index-fun)) {n}))


diagonalising-lemma-2 P double-index-fun = let ⋃ = chain-complete P in
  antisymmetric (pos P)
    (lub2
      (⋃ (chain-⊔fₖₙ-with-n-fixed P double-index-fun))
      (λ {m} →
        lub2
          (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m))
          (λ {n} → dₘₙ≤⊔dₖₖ P double-index-fun)))
    (lub2
      (⋃ (fₖₖ-chain P double-index-fun))
      (λ {n} →
        transitive (pos P)
          (lub1 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun n)) {n})
          (lub1 (⋃ (chain-⊔fₖₙ-with-n-fixed P double-index-fun)))))

diagonalising-lemma P double-index-fun = Eq.trans (diagonalising-lemma-1 P double-index-fun) (swap-≡ (diagonalising-lemma-2 P double-index-fun))

------------------------------------------------------------------------------------------------------------------------------------------------------------

function-⊑ : {P P′ : domain} (f : cont-fun P P′) → (f′ : cont-fun P P′) → Set

function-⊑ {P} {P′} f f′ = ∀ {x : A (pos P)} → (R (pos P′)) ((g (mon f)) x) ((g (mon f′)) x)

function-⊑-antisymmetry : (P P′ : domain) (f : cont-fun P P′) (f′ : cont-fun P P′) → function-⊑ f f′ → function-⊑ f′ f → f ≡ f′

function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f = cont-fun-extensionality (λ x → antisymmetric (pos P′) (f⊑f′ {x}) (f′⊑f {x}))

function-pos : (P P′ : domain) → poset

function-pos P P′ = record { A = cont-fun P P′
                           ; R = function-⊑
                           ; reflexive = λ {a} {x} → reflexive (pos P′)
                           ; antisymmetric = λ {f} {f′} f⊑f′ f′⊑f → function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f
                           ; transitive = λ {a} {b} {c} f⊑f′ f′⊑f″ → λ {x} → transitive (pos P′) (f⊑f′ {x}) (f′⊑f″ {x})
                           }

function-domain : (P P′ : domain) → domain


function-domain-chain-complete : (P P′ : domain) → ∀ (c : chain (function-pos P P′)) → lub c

function-domain-⊔ : (P P′ : domain) → ∀ (c : chain (function-pos P P′)) → cont-fun P P′   


chain-of-fₙ[d] : (P P′ : domain) → (chain-of-fₙ : chain (function-pos P P′)) → (d : A (pos P)) → chain (pos P′)

chain-of-fₙ[d] P P′ chain-of-fₙ d = record { g = λ n →
                                               let fₙ = g (mon (g chain-of-fₙ n)) in
                                               fₙ d
                                           ; mon = λ a≤a′ → mon chain-of-fₙ a≤a′
                                           }
                                          

⊔-chain-of-fₙ[d] : (P P′ : domain) → (chain-of-fₙ : chain (function-pos P P′)) → (d : A (pos P)) → A (pos P′)

⊔-chain-of-fₙ[d] P P′ chain-of-fₙ d = let ⋃ = chain-complete P′ in
  ⊔ (⋃ (chain-of-fₙ[d] P P′ chain-of-fₙ d))

                           
lub-preserve-lemma : (P P′ : domain) → (c : chain (function-pos P P′)) → (c₁ : chain (pos P)) → (λ z → g (mon (g c z)) (⊔ (chain-complete P c₁))) ≡ (λ z → ⊔ (chain-complete P′ (chain-map c₁ (mon (g c z)))))

lub-preserve-lemma P P′ c c₁ = function-extensionality ((λ (n : ℕ) → (lub-preserve (g c n) c₁)))

same-f-same-lub : {P : domain} {c c′ : chain (pos P)} → g c ≡ g c′ → ⊔ (chain-complete P c) ≡ ⊔ (chain-complete P c′)

same-f-same-lub {P} {c} {c′} Eq.refl = let ⋃ = chain-complete P in
  antisymmetric (pos P)
   (lub2 (⋃ c) (lub1 (⋃ c′)))
   (lub2 (⋃ c′) (lub1 (⋃ c)))


same-f-same-lub-≤ : (P : domain) (c c′ : chain (pos P)) → ((n : ℕ) → (R (pos P)) (g c n) (g c′ n)) → (R (pos P)) (⊔ (chain-complete P c)) (⊔ (chain-complete P c′))

same-f-same-lub-≤ P c c′ fₖ≤gₖ = let ⋃ = chain-complete P in
  lub2 (⋃ c) (λ {k} →
   transitive (pos P)
    (fₖ≤gₖ k)
    (lub1 (⋃ c′)))


function-domain-⊔-mon : (P P′ : domain) → (c : chain (function-pos P P′)) → monotone-fun (pos P) (pos P′)
function-domain-⊔-mon P P′ c = let ⋃ = chain-complete P′ in
  record { g = ⊔-chain-of-fₙ[d] P P′ c 
         ; mon = λ {d} {d′} d≤d′ →
           lub2
            (⋃ (chain-of-fₙ[d] P P′ c d))
            (λ {n} →
             transitive (pos P′)
              (mon (mon (g c n)) d≤d′)
              (lub1 (⋃ (chain-of-fₙ[d] P P′ c d′)) {n}))
         }

function-domain-chain : (P P′ : domain) (c : chain (function-pos P P′)) → (c′ : chain (pos P)) → chain (pos P′)
function-domain-chain P P′ c c′ = let ⋃ = chain-complete P′ in
  record { g =  λ z → ⊔ (⋃ (chain-map c′ (mon (g c z))))
         ; mon = λ {a} {a′} a≤a′ → lub2
                                     (⋃ (chain-map c′ (mon (g c a)))) λ {n} →
                                       transitive (pos P′)
                                         (mon c a≤a′)
                                         (lub1 (⋃ (chain-map c′ (mon (g c a′)))) {n})
         }
   

function-domain-doubly-indexed-fun : (P P′ : domain) → (c : chain (function-pos P P′)) → (c′ : chain (pos P)) → monotone-fun nats²-pos (pos P′)
function-domain-doubly-indexed-fun P P′ c c′  =
  record { g = λ x → 
             let m = (Data.Product.proj₁ x) in
             let n = (Data.Product.proj₂ x) in
             let c′-fun = g c′ in
             let chain-of-funs = g c in
             let fₘ = g (mon (chain-of-funs m))  in
             let dₙ = c′-fun n in 
           fₘ dₙ
         ; mon = λ {m₁,n₁} {m₂,n₂} m₁,n₁≤m₂,n₂ →
             let m₂ = Data.Product.proj₁ m₂,n₂ in
             let m₁≤m₂ = Data.Product.proj₁ m₁,n₁≤m₂,n₂ in
             let n₁≤n₂ = Data.Product.proj₂ m₁,n₁≤m₂,n₂ in
             let fₘ₁dₙ₁≤fₘ₂dₙ₁ = mon c m₁≤m₂ in
             let fₘ₂dₙ₁≤fₘ₂dₙ₂ = mon (mon (g c m₂)) (mon c′ n₁≤n₂) in
           transitive (pos P′) fₘ₁dₙ₁≤fₘ₂dₙ₁ fₘ₂dₙ₁≤fₘ₂dₙ₂
         }



function-domain-⊔-lemma-1 : (P P′ : domain) → (c : chain (function-pos P P′)) → (c′ : chain (pos P))
  → ⊔ (chain-complete P′ (function-domain-chain P P′ c c′))
    ≡
    ⊔ (chain-complete P′ (chain-⊔fₙₖ-with-n-fixed P′ (function-domain-doubly-indexed-fun P P′ c c′)))

function-domain-⊔-lemma-1 P P′ c c′ =
  same-f-same-lub {P′}
   {function-domain-chain P P′ c c′}
   {chain-⊔fₙₖ-with-n-fixed P′
    (function-domain-doubly-indexed-fun P P′ c c′)
   }
   (function-extensionality
    λ x → same-f-same-lub {P′}
           {chain-map c′ (mon (g c x))}
           {chain-fₘₙ-with-m-fixed P′
            (function-domain-doubly-indexed-fun P P′ c c′)
            x
           }
           Eq.refl
   )


function-domain-⊔-lemma-2 : (P P′ : domain) → (c : chain (function-pos P P′)) → (c′ : chain (pos P)) → 
    ⊔ (chain-complete P′ (chain-⊔fₖₙ-with-n-fixed P′ (function-domain-doubly-indexed-fun P P′ c c′)))
    ≡
    ⊔ (chain-complete P′ (chain-map c′ (function-domain-⊔-mon P P′ c)))

function-domain-⊔-lemma-2 P P′ c c′ =
  same-f-same-lub {P′} {chain-⊔fₖₙ-with-n-fixed P′
   (function-domain-doubly-indexed-fun P P′ c c′)}
   {chain-map c′ (function-domain-⊔-mon P P′ c)}
   (function-extensionality
    (λ x → same-f-same-lub {P′}
     {chain-fₘₙ-with-n-fixed P′
      (function-domain-doubly-indexed-fun P P′ c c′) x
     }
     {chain-of-fₙ[d] P P′ c (g c′ x)}
     Eq.refl
    )
   )


function-domain-⊔ P P′ c =
  let ⋃ = chain-complete P in
  let ⋃′ = chain-complete P′ in
  record
    { mon = function-domain-⊔-mon P P′ c
    ; lub-preserve = λ c₁ →
      begin
        ⊔-chain-of-fₙ[d] P P′ c (⊔ (⋃ c₁))
      ≡⟨ same-f-same-lub {P′}
          {chain-of-fₙ[d] P P′ c (⊔ (⋃ c₁))}
          {function-domain-chain P P′ c c₁}
          (function-extensionality
           (λ n → lub-preserve (g c n )c₁)
          )
       ⟩
        ⊔ (⋃′ (function-domain-chain P P′ c c₁))
      ≡⟨ function-domain-⊔-lemma-1 P P′ c c₁ ⟩
        ⊔ (⋃′ (chain-⊔fₙₖ-with-n-fixed P′ (function-domain-doubly-indexed-fun P P′ c c₁)))
      ≡⟨  diagonalising-lemma P′ (function-domain-doubly-indexed-fun P P′ c c₁) ⟩
        ⊔ (⋃′ (chain-⊔fₖₙ-with-n-fixed P′ (function-domain-doubly-indexed-fun P P′ c c₁)))
      ≡⟨ function-domain-⊔-lemma-2 P P′ c c₁ ⟩
        ⊔ (⋃′ (chain-map c₁ (function-domain-⊔-mon P P′ c)))
      ∎
    }

function-domain-chain-complete P P′ c = let ⋃ = chain-complete P′ in record
  { ⊔ = function-domain-⊔ P P′ c
  ; lub1 = λ {n} {x} → lub1 (⋃ (chain-of-fₙ[d] P P′ c x))
  ; lub2 = λ x → λ {x₁} → lub2 (⋃ (chain-of-fₙ[d] P P′ c x₁)) x
  }


function-domain-⊥-function : (P P′ : domain) → cont-fun P P′
function-domain-⊥-func-mon : (P P′ : domain) → monotone-fun (pos P) (pos P′)
function-domain-⊥-func-mon P P′ = record { g = λ x → ⊥ (bottom P′)
                                         ; mon = λ a≤a′ → reflexive (pos P′)
                                         }


function-domain-⊥-function P P′ = record { mon = function-domain-⊥-func-mon P P′  
                                         ; lub-preserve = λ c → antisymmetric (pos P′)
                                           (⊥-is-bottom (bottom P′))
                                           (lub2 (chain-complete P′ (chain-map c (function-domain-⊥-func-mon P P′)))
                                             (λ {n} → reflexive (pos P′)))
                                         }
                                         
function-domain P  P′ = record
  { pos = function-pos P P′
  ; chain-complete = function-domain-chain-complete P P′
  ; bottom = record { ⊥ = function-domain-⊥-function P P′
                    ; ⊥-is-bottom = λ {a} {x} → ⊥-is-bottom (bottom P′)
                    }
  }



remark-237 : (P : domain) → (P′ : domain) → (c : chain (pos P)) → (f : monotone-fun (pos P) (pos P′))
  → (∀ (d : chain (pos P)) → (R (pos P′)) ((g f) (⊔ (chain-complete P d))) (⊔ (chain-complete P′ (chain-map d f))))
  → cont-fun P P′


unique-lub : ∀ (P : poset) → (c : chain P) → (a b : lub c) → ⊔ a ≡ ⊔ b
unique-lub P c a b = antisymmetric P (lub2 a (lub1 b)) (lub2 b (lub1 a))

remark-237 P P′ c f f⋃dₙ⊑⋃fdₙ = record { mon = f
                                       ; lub-preserve = λ c →
                                           antisymmetric (pos P′)
                                             (f⋃dₙ⊑⋃fdₙ c)
                                             (lub2 (chain-complete P′ (chain-map c f)) (λ {n} → mon f (lub1 (chain-complete P c))))
                                       }


lfp-is-fixed : ∀ {D : domain} {f : cont-fun D D} → d (lfp1 (tarski-fix D f)) ≡ g (mon f) (d (lfp1 (tarski-fix D f)))

lfp-is-fixed {D} {f} =
  antisymmetric (pos D)
    (lfp2 ((tarski-fix D f)) ((((mon (mon f)) (pre-fix (lfp1 (tarski-fix D f)))))))
    (pre-fix (lfp1 (tarski-fix D f)))



constant-fun-is-cont : {B : Set} → {D : domain} → B → cont-fun D (flat-domain B)
constant-fun-is-cont-mon : {B : Set} → {D : domain} → B → monotone-fun (pos D) (pos (flat-domain B))
constant-fun-is-cont-mon {B} {D} b = record { g = λ x → inj b
                                            ; mon = λ x → x≼x
                                            }
constant-fun-is-cont {B} {D} b = record { mon = constant-fun-is-cont-mon {B} {D} b
                                        ; lub-preserve = λ c → antisymmetric (pos (flat-domain B))
                                            (lub1
                                              {pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete (flat-domain B) (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {0}
                                            )
                                            (lub2
                                              {pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete (flat-domain B) (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {inj b}
                                              (λ {n} → x≼x)
                                            )
                                        }

pair-f : ∀ {D D₁ D₂ : domain} → cont-fun D D₁ → cont-fun D D₂ → cont-fun D (domain-product D₁ D₂)
g (mon (pair-f f₁ f₂)) x fzero = g (mon f₁) x
g (mon (pair-f f₁ f₂)) x (fsucc i) = g (mon f₂) x
mon (mon (pair-f f₁ f₂)) a≦a′ fzero = mon (mon f₁) a≦a′
mon (mon (pair-f f₁ f₂)) a≦a′ (fsucc y) = mon (mon f₂) a≦a′
lub-preserve (pair-f f₁ f₂) c = dependent-function-extensionality (λ { fzero → (lub-preserve f₁) c ; (fsucc x) → (lub-preserve f₂) c })


_∘_ : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → cont-fun D₁ D₃

∘-mon : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → monotone-fun (domain.pos D₁) (domain.pos D₃)
∘-mon f₂ f₁ = record { g = λ x → g (mon f₂) (g (mon f₁) x)
                     ; mon = λ a≤a′ → mon (mon f₂) (mon (mon f₁) a≤a′)
                     }


_∘_ {D₁ = D₁} {D₂ = D₂} {D₃ = D₃} f₂ f₁  =
                     record { mon = ∘-mon f₂ f₁
                            ; lub-preserve = λ c →
                            begin
                              g (mon f₂) (g (mon f₁) (⊔ (chain-complete D₁ c)))
                            ≡⟨ cong (g (mon f₂)) (lub-preserve f₁ c) ⟩
                              g (mon f₂) (⊔ (chain-complete D₂ (chain-map c (mon f₁))))
                            ≡⟨ lub-preserve f₂ (chain-map c (mon f₁)) ⟩
                              ⊔ (chain-complete D₃ (chain-map c (∘-mon f₂ f₁)))
                            ∎ 
                            }

extend-function : ∀ {X Y} → (X → B⊥ Y) → cont-fun (flat-domain X) (flat-domain Y)
extend-function-mon : ∀ {X Y} → (X → B⊥ Y) → monotone-fun (flat-domain-pos X) (flat-domain-pos Y)
extend-function-mon f = record { g = λ { ⊥₁ → ⊥₁
                                       ; (inj x) → f x
                                       }
                               ; mon = λ {z≼n → z≼n; x≼x → x≼x}
                               }

mon (extend-function {X} {Y} f) = extend-function-mon f

lub-preserve (extend-function {X} {Y} f) c = constant-UP-useful
  {flat-domain-pos Y}
  {chain-map c (extend-function-mon f)}
  {flat-domain-chain-eventually-constant (chain-map c (extend-function-mon f))}
  {g (mon (extend-function f)) (⊔ (chain-complete (flat-domain X) c))}
  {index (flat-domain-chain-eventually-constant c)}
  (λ {m} index≤m →
    cong
      (g (mon (extend-function f)))
      (eventually-val (flat-domain-chain-eventually-constant c) index≤m))

ℕ⊥ : domain
𝔹⊥ : domain

ℕ⊥ = flat-domain ℕ
𝔹⊥ = flat-domain Bool

domain-dependent-projection : (I : Set) → (f : I → domain) → (i : I) → cont-fun (domain-dependent-product I f) (f i)
domain-dependent-projection-mon : (I : Set) → (f : I → domain) → (i : I) → monotone-fun (pos (domain-dependent-product I f)) (pos (f i))
domain-dependent-projection-mon I f i = record { g = λ p → p i ; mon = λ a≤a′ → a≤a′ i } 


domain-dependent-projection I f i = record { mon = domain-dependent-projection-mon I f i
                                           ; lub-preserve = λ c →
                                               same-f-same-lub
                                                 {f i} {chain-of-functions I f c i} {chain-map c (domain-dependent-projection-mon I f i)}
                                                 refl
                                           }

pair : ∀ {D} {E} → (A (pos D)) → (A (pos E)) → A (pos (domain-product D E))
pair d e fzero = d
pair d e (fsucc fzero) = e

pair-equality : ∀ {D} {E} → {d₁ d₂ : A (pos D)} → {e₁ e₂ : A (pos E)} → (d₁ ≡ d₂) → (e₁ ≡ e₂) → pair {D} {E} d₁ e₁ ≡ pair {D} {E} d₂ e₂
pair-equality refl refl = refl

pair-η : ∀ {D} {E} → {a : poset.A (pos (domain-product D E))} → pair {D} {E} (a fzero) (a (fsucc fzero)) ≡ a
pair-η = dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}

module DomainTheory.ContinuousFunctions.if-cont where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; _≤_)
open import Data.Bool using (Bool; true; false)
open import DomainTheory.BasicObjects.posets-etc
open import misc using (𝔹⊥; pair; pair-η; pair-equality)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open least-element
open eventually-constant


poset-projections : (P₁ P₂ : poset) → (Fin 2) → poset
poset-projections P₁ P₂ fzero = P₁
poset-projections P₁ P₂ (fsucc x) = P₂

poset-dependent-product : (I : Set) → (I → poset) → poset
poset-dependent-R : (I : Set) → (f : I → poset) → ((i : I) → (A (f i)))  → ((i : I) → (A (f i))) → Set

poset-dependent-R I f p₁ p₂ = (i : I) → R (f i) (p₁ i) (p₂ i)

poset-dependent-refl : (I : Set) → (f : I → poset) → {p : (i : I) → (A (f i))} → poset-dependent-R I f p p
poset-dependent-refl I f i = reflexive (f i)


poset-dependent-antisym : (I : Set) → (f : I → poset) → {p₁ p₂ : (i : I) → (A (f i))} → poset-dependent-R I f p₁ p₂ → poset-dependent-R I f p₂ p₁ → p₁ ≡ p₂
poset-dependent-antisym I f p₁≤p₂ p₂≤p₁ = dependent-function-extensionality λ i → antisymmetric (f i) (p₁≤p₂ i) (p₂≤p₁ i)


poset-dependent-trans : (I : Set) → (f : I → poset) → {p₁ p₂ p₃ : (i : I) → (A (f i))} → poset-dependent-R I f p₁ p₂ → poset-dependent-R I f p₂ p₃ → poset-dependent-R I f p₁ p₃
poset-dependent-trans I f p₁≤p₂ p₂≤p₃ = λ i → transitive (f i) (p₁≤p₂ i) (p₂≤p₃ i)


poset-dependent-product I f = record
                                   { A = (i : I) → A (f i)
                                   ; R = poset-dependent-R I f
                                   ; reflexive = poset-dependent-refl I f
                                   ; antisymmetric = poset-dependent-antisym I f
                                   ; transitive = poset-dependent-trans I f
                                   }

poset-product : poset → poset → poset

poset-product P₁ P₂ = poset-dependent-product (Fin 2) (poset-projections P₁ P₂)

pair-pos : ∀ {D} {E} → A D → A E → A (poset-product D E)
pair-pos d e fzero = d
pair-pos d e (fsucc fzero) = e

pair-η-pos : ∀ {D} {E} → {a : A (poset-product D E)} → pair-pos {D} {E} (a fzero) (a (fsucc fzero)) ≡ a
pair-η-pos = dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}

a≤b≡c→a≤c₂ : {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ⊑ b → b ≡ c → a ⊑ c
a≤b≡c→a≤c₂ a≤b Eq.refl = a≤b

slide-33-prop : ∀ {D E F}
  → (f : A (pos (domain-product D E)) → A (pos F))
  → ({d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e)) (f (pair d′ e)))
  → ({d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e)) (f (pair d e′)))
  → monotone-fun (pos (domain-product D E)) (pos F)

g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) = f
mon (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) a≤a′ =
  transitive (pos F)
    (a≡b≤c→a≤c {A (pos F)} {R (pos F)} (Eq.sym (cong f (pair-η))) (mon-arg-1 (a≤a′ fzero)))
    (a≤b≡c→a≤c₂ {A (pos F)} {R (pos F)} (mon-arg-2 (a≤a′ (fsucc fzero))) (cong f (pair-η)) )

slide-33-prop′ : {D E F : poset}
  → (f : A (poset-product D E) → A F)
  → ({d d′ : A D} → {e : A E} → (R D) d d′ → (R F) (f (pair-pos d e)) (f (pair-pos d′ e)))
  → ({d : A D} → {e e′ : A E} → (R E) e e′ → (R F) (f (pair-pos d e)) (f (pair-pos d e′)))
  → monotone-fun (poset-product D E) F


g (slide-33-prop′ {D} {E} {F} f mon-arg-1 mon-arg-2) = f
mon (slide-33-prop′ {D} {E} {F} f mon-arg-1 mon-arg-2) a≤a′ =
  transitive F
    (a≡b≤c→a≤c
      {A F} {R F}
      (cong f (Eq.sym (pair-η-pos)))
      (mon-arg-1 (a≤a′ fzero)))
    (a≤b≡c→a≤c₂
      {A F} {R F}
      (mon-arg-2 (a≤a′ (fsucc fzero)))
      (cong f (pair-η-pos)))


chain-fix-d-slide-33 : ∀ {D E}
  → chain (pos (domain-product D E))
  → A (pos D)
  → chain (pos (domain-product D E))


g (chain-fix-d-slide-33 {D} {E} c d) n fzero = d
g (chain-fix-d-slide-33 {D} {E} c d) n (fsucc i) = g (proj₂-chain {D} {E} c) n
mon (chain-fix-d-slide-33 {D} {E} c d) a≤a′ fzero = reflexive (pos D)
mon (chain-fix-d-slide-33 {D} {E} c d) a≤a′ (fsucc fzero) = mon c a≤a′ (fsucc fzero)

chain-fix-e-slide-33 : ∀ {D E}
  → chain (pos (domain-product D E))
  → A (pos E)
  → chain (pos (domain-product D E))


g (chain-fix-e-slide-33 {D} {E} c _) n fzero = g (proj₁-chain {D} {E} c) n
g (chain-fix-e-slide-33 _ e) _ (fsucc fzero) = e
mon (chain-fix-e-slide-33 c _) a≤a′ fzero = mon c a≤a′ fzero
mon (chain-fix-e-slide-33 {E = E} _ _) _ (fsucc fzero) = reflexive (pos E)


if-g : ∀ {D} → A (pos (domain-product 𝔹⊥ (domain-product D D))) → A (pos D)
if-g {D} x with (x fzero)
...                     | inj false = x (fsucc fzero) (fsucc fzero)
...                     | inj true  = x (fsucc fzero) fzero
...                     | ⊥₁        = least-element.⊥ (bottom D)


if-mon-first : {D : domain} → {b b′ : A (pos 𝔹⊥)} → {e : A (pos (domain-product D D))} → (R (pos 𝔹⊥)) b b′ → (R (pos D)) (if-g {D} (pair b e) ) (if-g {D} (pair b′ e))


if-mon-first {D} z≼n = least-element.⊥-is-bottom (bottom D)
if-mon-first {D} x≼x = reflexive (pos D)

if-mon-second : (D : domain)
  → ((b : B⊥ Bool)
  → (e e′ : A (pos (domain-product D D)))
  → (R (pos (domain-product D D))) e e′
  → (R (pos D)) (if-g {D} (pair b e)) (if-g {D} (pair b e′)))
if-mon-second D ⊥₁ e e′ e≤e′ = ⊥-is-bottom (bottom D)
if-mon-second D (inj false) e e′ e≤e′ = e≤e′ (fsucc fzero) 
if-mon-second D (inj true) e e′ e≤e′ = e≤e′ fzero


if-mon : ∀ {D} → monotone-fun (product-pos 𝔹⊥ (domain-product D D)) (pos D)
if-mon {D} =
  slide-33-prop
    {𝔹⊥} {domain-product D D} {D}
    if-g
    (if-mon-first {D})
    (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂)

slide-33-prop-cont : ∀ {D E F}
   → (f : (A (pos (domain-product D E)) → A (pos F)))
   → (mon-arg-1 : {d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e) ) (f (pair d′ e)))
   → (mon-arg-2 : {d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e) ) (f (pair d e′)))
   → ({c : chain (product-pos D E)}
     → {e : A (pos E)}
     → f (pair (⊔ (chain-complete D (proj₁-chain {D} {E} c))) e)
       ≡
       ⊔ (chain-complete F (chain-map (chain-fix-e-slide-33 {D} {E} c e) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)))
     )
   → ({c : chain (pos (domain-product D E))}
     → {d : A (pos D)}
     → f (pair d (⊔ (chain-complete E (proj₂-chain {D} {E} c))))
       ≡
       ⊔ (chain-complete F (chain-map (chain-fix-d-slide-33 {D} {E} c d) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)))
     )
   → cont-fun (domain-product D E) F

[dₙ,eₙ],f→f[dₙ,⊔eⱼ] : {D E F : domain} → (c : chain (pos (domain-product D E))) → (f : monotone-fun (pos (domain-product D E)) (pos F)) → chain (pos F)
[dₙ,eₙ],f→f[dₙ,⊔eⱼ] {D} {E} {F} c f = record
    { g = λ n → g f (pair (g (proj₁-chain c) n) (⊔ (chain-complete E (proj₂-chain c))))
    ; mon = λ n≤n′ → mon f (λ {fzero → (mon c n≤n′ fzero); (fsucc fzero) → reflexive (pos E)})
    }
  

[dₙ,eₙ],f,n→f[dₙ,eⱼ] : {D E F : domain} → (c : chain (pos (domain-product D E))) → (f : monotone-fun (pos (domain-product D E)) (pos F)) → ℕ → chain (pos F)
[dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n = record
    { g = λ j → g f (pair (g (proj₁-chain c) n) (g (proj₂-chain c) j))
    ; mon = λ j≤j′ → mon f λ { fzero → reflexive (pos D); (fsucc fzero) → mon c j≤j′ (fsucc fzero)}
    }

[dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] : {D E F : domain} → (c : chain (pos (domain-product D E))) → (f : monotone-fun (pos (domain-product D E)) (pos F)) → chain (pos F)
[dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] {D} {E} {F} c f = record
    { g = λ n → ⊔ (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n))
    ; mon = λ {n} {n′} n≤n′ → lub2 (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n))
      (transitive (pos F)
        (mon f (λ { fzero → mon c n≤n′ fzero ; (fsucc fzero) → reflexive (pos E)}))
        (lub1 (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n′)))
      )
    }
  

f[dᵢeⱼ] : {D E F : domain}
  → chain (pos (domain-product D E))
  → (f : (A (pos (domain-product D E)) → A (pos F)))
  → ({d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e) ) (f (pair d′ e)))
  → ({d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e) ) (f (pair d e′)))
  → monotone-fun nats²-pos (pos F)

a≡b≤c≡d→a≤d : {D : Set} → {_⊑_ : D → D → Set} → {a b c d : D} → a ≡ b → b ⊑ c → c ≡ d → a ⊑ d
a≡b≤c≡d→a≤d refl b⊑c refl = b⊑c

g (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) ⟨ i , j ⟩ = let dᵢ = g (proj₁-chain c) i in
                                                            let eⱼ = g (proj₂-chain c) j in
                                                            f (pair dᵢ eⱼ)


mon (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) {⟨ i , j ⟩} {⟨ i′ , j′ ⟩} ⟨ i≤i′ , j≤j′ ⟩ =
  a≡b≤c≡d→a≤d
    {A (pos F)} {R (pos F)}
    {f (pair (g c i fzero) (g c j (fsucc fzero)))}
    {g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) (pair (g c i fzero) (g c j (fsucc fzero))) }
    {g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) (pair (g c i′ fzero) (g c j′ (fsucc fzero)))}
    {f (pair ((g c) i′ fzero) (g c j′ (fsucc fzero)))}
      refl
      (mon (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) λ {fzero → mon c i≤i′ fzero; (fsucc fzero) → mon c j≤j′ (fsucc fzero)})
      refl

helpful-chain : {D E F : domain}
  → chain (pos (domain-product D E))
  → (f : (A (pos (domain-product D E)) → A (pos F)))
  → ({d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e) ) (f (pair d′ e)))
  → ({d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e) ) (f (pair d e′)))
  → chain (pos F)

helpful-chain {D} {E} {F} c f mon-arg-1 mon-arg-2 = record
    { g = λ n → ⊔ (chain-complete F (chain-map (chain-fix-d-slide-33 c (g (proj₁-chain c) n)) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)))
    ; mon = λ {a} {a′} a≤a′ →
      same-f-same-lub-≤ F
        (chain-map (chain-fix-d-slide-33 c (g c a fzero)) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2))
        (chain-map (chain-fix-d-slide-33 c (g c a′ fzero)) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2))
        λ n → mon (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)
                λ {fzero → mon c a≤a′ fzero; (fsucc fzero) → reflexive (pos E)}
    }

mon (slide-33-prop-cont {D} {E} {F} f mon-arg-1 mon-arg-2 _ _) = slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2
lub-preserve (slide-33-prop-cont {D} {E} {F} f mon-arg-1 mon-arg-2 cont-arg-1 cont-arg-2) c =
  let f-mon = slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2 in
  let ⊔dₙ = ⊔ (chain-complete D (proj₁-chain c)) in
  let ⊔eₙ = ⊔ (chain-complete E (proj₂-chain c)) in
  let ⊔[dₙeₙ] = ⊔ (chain-complete (domain-product D E) c) in
  let f[dᵢ,⊔eⱼ] = [dₙ,eₙ],f→f[dₙ,⊔eⱼ] {D} {E} {F} c f-mon in
  let ⊔ᵢf[dᵢ,⊔eⱼ] = ⊔ (chain-complete F f[dᵢ,⊔eⱼ]) in
  let ⊔ⱼ[f[dₙ,eⱼ]] = [dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] {D} {E} {F} c f-mon in
  let ⊔ᵢ⊔ⱼf[dᵢ,eⱼ] = ⊔ (chain-complete F ⊔ⱼ[f[dₙ,eⱼ]]) in
  begin
    f ⊔[dₙeₙ]
  ≡⟨ cong f (Eq.sym pair-η) ⟩
    f (pair (⊔dₙ) (⊔eₙ))
  ≡⟨ cont-arg-1 {c} {⊔eₙ} ⟩
    ⊔ (chain-complete F (chain-map (chain-fix-e-slide-33 c ⊔eₙ) f-mon))
  ≡⟨ same-f-same-lub {F} {chain-map (chain-fix-e-slide-33 c ⊔eₙ) f-mon} {[dₙ,eₙ],f→f[dₙ,⊔eⱼ] {D} {E} {F} c f-mon}
      (function-extensionality λ n →
        cong f (dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}))
   ⟩
    ⊔ᵢf[dᵢ,⊔eⱼ]
  ≡⟨ same-f-same-lub
       {F} {f[dᵢ,⊔eⱼ]} {helpful-chain {D} {E} {F} c f mon-arg-1 mon-arg-2}
       (function-extensionality λ n → cont-arg-2 {c} {g (proj₁-chain {D} {E} c) n})
   ⟩
     ⊔ (chain-complete F (helpful-chain {D} {E} {F} c f mon-arg-1 mon-arg-2))                
  ≡⟨ same-f-same-lub
       {F} {helpful-chain {D} {E} {F} c f mon-arg-1 mon-arg-2} {⊔ⱼ[f[dₙ,eⱼ]]}
       (function-extensionality λ i → 
         same-f-same-lub
           {F}
           {chain-map (chain-fix-d-slide-33 c (g (proj₁-chain c) i)) f-mon}
           {[dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f-mon i}
           (function-extensionality λ j
             → cong f (dependent-function-extensionality (λ {fzero → refl; (fsucc fzero) → refl}))
           )
       )
   ⟩
    ⊔ᵢ⊔ⱼf[dᵢ,eⱼ]
  ≡⟨ same-f-same-lub
       {F} {⊔ⱼ[f[dₙ,eⱼ]]} {chain-⊔fₙₖ-with-n-fixed F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)}
       (function-extensionality (λ x →
         same-f-same-lub
           {F} {[dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f-mon x} {chain-fₘₙ-with-m-fixed F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) x}
           refl)
       )
   ⟩
    ⊔ (chain-complete F (chain-⊔fₙₖ-with-n-fixed F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)))
  ≡⟨ diagonalising-lemma-1 F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) ⟩
    ⊔ (chain-complete F (fₖₖ-chain F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)))
  ≡⟨ same-f-same-lub
       {F} {fₖₖ-chain F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)} {chain-map c f-mon}
       (function-extensionality (λ x → cong f pair-η))
   ⟩
    ⊔ (chain-complete F (chain-map c f-mon))
  ∎

lemma-blah-blah : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (m : ℕ)
  → (index≤m : Data.Nat._≤_ (index ev-const) m)
  → g (chain-fix-e-slide-33 c e) m ≡ pair (g (proj₁-chain c) m) e

lemma-blah-blah {D} c e ev-const m index≤m = dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}


lemma-fun-fun : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e
    ≡
    g (chain-fix-e-slide-33 c e) (index (flat-domain-chain-eventually-constant (proj₁-chain c)))

lemma-fun-fun c e ev-const = dependent-function-extensionality (λ {fzero → Eq.sym (eventually-val (flat-domain-chain-eventually-constant (proj₁-chain c)) refl-≤); (fsucc fzero) → refl})


very-useful-lemma : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj true))
  → (n : ℕ)
  → R (pos D) (if-g (g (chain-fix-e-slide-33 c e) n)) (e fzero)


very-useful-lemma″ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj true))
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → g (chain-fix-e-slide-33 c e) n ≡ pair (inj true) e

very-useful-lemma″ c e ev-const ev-val≡true n index≤n = dependent-function-extensionality (λ {fzero → Eq.trans (eventually-val ev-const index≤n) (ev-val≡true); (fsucc fzero) → refl})


very-useful-lemma₂″ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj false))
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → g (chain-fix-e-slide-33 c e) n ≡ pair (inj false) e


very-useful-lemma₂″ c e ev-const ev-val≡false n index≤n = dependent-function-extensionality (λ {fzero → Eq.trans (eventually-val ev-const index≤n) (ev-val≡false); (fsucc fzero) → refl}) 


very-useful-lemma₂′ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj false))
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → if-g (g (chain-fix-e-slide-33 c e) n) ≡ if-g (pair (inj false) e)

very-useful-lemma₂′ c e ev-const ev-val≡false n index≤n = cong if-g (very-useful-lemma₂″ c e ev-const ev-val≡false n index≤n)



very-useful-lemma′ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj true))
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → if-g (g (chain-fix-e-slide-33 c e) n) ≡ if-g (pair (inj true) e)

very-useful-lemma′ c e ev-const ev-val≡true n index≤n = cong if-g (very-useful-lemma″ c e ev-const ev-val≡true n index≤n)


very-useful-lemma {D} c e ev-const ev-val≡true n with ≤-dichotomy {n} {index ev-const}
...                                  | (inj₁ n≤index) = transitive (pos D)
                                                          (mon (chain-map (chain-fix-e-slide-33 c e) (if-mon {D})) n≤index)
                                                          (a≤b≡c→a≤c′ {A (pos D)} {R (pos D)}
                                                            (reflexive (pos D))
                                                            (very-useful-lemma′ c e ev-const ev-val≡true (index ev-const) refl-≤)
                                                          )
...                                  | (inj₂ index≤n) = a≡b≤c→a≤c {A (pos D)} {R (pos D)}
                                                          (very-useful-lemma′ {D} c e ev-const ev-val≡true n index≤n)
                                                          (reflexive (pos D))

very-useful-lemma₂ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ (inj false))
  → (n : ℕ)
  → R (pos D) (if-g (g (chain-fix-e-slide-33 c e) n)) (e (fsucc fzero))


very-useful-lemma₂ {D} c e ev-const ev-val≡false n with ≤-dichotomy {n} {index ev-const}
...               | inj₁ n≤index = transitive (pos D)
                                     (mon (chain-map (chain-fix-e-slide-33 c e) (if-mon {D})) n≤index)
                                     (a≡b≤c→a≤c
                                       {A (pos D)} {R (pos D)}
                                       (very-useful-lemma₂′ {D} c e ev-const ev-val≡false (index ev-const) refl-≤) (reflexive (pos D)))
...               | inj₂ index≤n = a≡b≤c→a≤c {A (pos D)} {R (pos D)} (very-useful-lemma₂′ {D} c e ev-const ev-val≡false n index≤n) (reflexive (pos D))


very-useful-lemma₁″ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ ⊥₁)
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → g (chain-fix-e-slide-33 c e) n ≡ pair ⊥₁ e


very-useful-lemma₁″ c e ev-const ev-val≡⊥ n index≤n = dependent-function-extensionality (λ {fzero → Eq.trans (eventually-val ev-const index≤n) (ev-val≡⊥); (fsucc fzero) → refl}) 


very-useful-lemma₁′ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ ⊥₁)
  → (n : ℕ)
  → (index (ev-const) ≤ n)
  → if-g (g (chain-fix-e-slide-33 c e) n) ≡ if-g (pair ⊥₁ e)

very-useful-lemma₁′ c e ev-const ev-val≡⊥₁ n index≤n = cong if-g (very-useful-lemma₁″ c e ev-const ev-val≡⊥₁ n index≤n)

very-useful-lemma₁ : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (ev-const : eventually-constant (proj₁-chain c))
  → (eventual-val (ev-const) ≡ ⊥₁)
  → (n : ℕ)
  → R (pos D) (if-g (g (chain-fix-e-slide-33 c e) n)) (⊥ (bottom D))


very-useful-lemma₁ {D} c e ev-const ev-val≡⊥ n with ≤-dichotomy {n} {index ev-const}
...               | inj₁ n≤index = transitive (pos D)
                                     (mon (chain-map (chain-fix-e-slide-33 c e) (if-mon {D})) n≤index)
                                     (a≡b≤c→a≤c
                                       {A (pos D)} {R (pos D)}
                                       (very-useful-lemma₁′ {D} c e ev-const ev-val≡⊥ (index ev-const) refl-≤) (reflexive (pos D)))
...               | inj₂ index≤n = a≡b≤c→a≤c {A (pos D)} {R (pos D)} (very-useful-lemma₁′ {D} c e ev-const ev-val≡⊥ n index≤n) (reflexive (pos D))



eventually-constant-d-slide-33-lemma : ∀ {D}
  → (c : chain (pos (domain-product 𝔹⊥ (domain-product D D))))
  → (e : A (pos (domain-product D D)))
  → (eventually-constant (proj₁-chain c))
  → (eventually-constant (chain-map (chain-fix-e-slide-33 c e) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂))))


eventually-constant-d-slide-33-lemma {D} c e ev-const = 
  record
                                                      { index = index ev-const
                                                      ; eventual-val = if-g {D} (pair (eventual-val ev-const) e)  
                                                      ; eventually-val = λ {m} index≤m →
                                                          begin
                                                            g (chain-map (chain-fix-e-slide-33 c e) if-mon) m
                                                          ≡⟨ refl ⟩
                                                            if-g (g (chain-fix-e-slide-33 c e) m)
                                                          ≡⟨ cong if-g (lemma-blah-blah {D} c e ev-const m index≤m) ⟩
                                                            if-g (pair (g (proj₁-chain c) m) e)
                                                          ≡⟨ cong (λ x → if-g (pair x e)) (eventually-val ev-const index≤m) ⟩
                                                            if-g (pair (eventual-val ev-const) e)
                                                          ∎
                                                      }

if-cont-first : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {e : A (pos (domain-product D D))}
  → if-g (pair (⊔ (chain-complete 𝔹⊥ (proj₁-chain c))) e)
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D})
        (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂))))


data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


if-cont-first {D} {c} {e} with inspect (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c)))
...                            | ⊥₁ with≡ eq = 
                                  begin
                                    if-g (pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e)
                                  ≡⟨ cong (λ x → if-g (pair x e)) eq ⟩
                                    ⊥ (bottom D)
                                  ≡⟨ antisymmetric (pos D)
                                       (⊥-is-bottom (bottom D))
                                       (lub2 (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon)) {⊥ (bottom D)} (λ {n} → very-useful-lemma₁ c e (flat-domain-chain-eventually-constant (proj₁-chain c)) eq n))
                                   ⟩ 
                                    ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon))
                                  ∎
...                            | (inj false) with≡ eq = 
                                  begin
                                    if-g (pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e)
                                  ≡⟨ cong (λ x → if-g (pair x e)) eq ⟩
                                    e (fsucc fzero)
                                  ≡⟨ antisymmetric (pos D)
                                       (a≡b≤c→a≤c {A (pos D)} {R (pos D)}
                                         (begin
                                           e (fsucc fzero)
                                          ≡⟨ Eq.sym (cong (λ x → if-g (pair x e)) eq) ⟩
                                            if-g (pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e)
                                          ≡⟨ Eq.sym
                                               (eventually-val
                                                 (eventually-constant-d-slide-33-lemma c e
                                                   (flat-domain-chain-eventually-constant (proj₁-chain c)))
                                                  refl-≤)
                                           ⟩
                                            g (chain-map (chain-fix-e-slide-33 c e) if-mon) (index (flat-domain-chain-eventually-constant (proj₁-chain c)))
                                          ∎)
                                          (lub1 (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon)) {index (flat-domain-chain-eventually-constant (proj₁-chain c))}))
                                       (lub2 (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon)) {e (fsucc fzero)} (λ {n} → very-useful-lemma₂ c e (flat-domain-chain-eventually-constant (proj₁-chain c)) eq n))
                                   ⟩
                                    ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon))
                                  ∎
...                            | (inj true) with≡ eq = 
                                     begin
                                       if-g (pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e)
                                     ≡⟨ cong (λ x → if-g (pair x e)) eq ⟩
                                       e fzero
                                     ≡⟨ antisymmetric (pos D)
                                          (a≡b≤c→a≤c {A (pos D)} {R (pos D)}
                                            (begin
                                              e fzero
                                            ≡⟨ refl ⟩
                                              if-g (pair (inj true) e)
                                            ≡⟨ Eq.sym (cong (λ x → if-g (pair x e)) eq) ⟩
                                              if-g (pair (eventual-val (flat-domain-chain-eventually-constant (proj₁-chain c))) e)
                                            ≡⟨ cong if-g (lemma-fun-fun c e (flat-domain-chain-eventually-constant (proj₁-chain c)))  ⟩
                                              g (chain-map (chain-fix-e-slide-33 c e) if-mon) (index (flat-domain-chain-eventually-constant (proj₁-chain c)))
                                            ∎
                                            )
                                            (lub1 (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon)) {index (flat-domain-chain-eventually-constant (proj₁-chain c))}))
                                          (lub2 (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon)) {e fzero} (λ {n} → very-useful-lemma c e (flat-domain-chain-eventually-constant (proj₁-chain c)) eq n))
                                      ⟩
                                        ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) if-mon))
                                     ∎



if-cont-second : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {d : A (pos 𝔹⊥)}
  → if-g (pair d (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c d) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (λ {d′} {e₁} {e₂} → if-mon-second D d′ e₁ e₂))))

if-cont-second {D} {c} {⊥₁} =
  let if-mon = slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂) in
  begin
    if-g (pair ⊥₁ (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    least-element.⊥ (bottom D)
  ≡⟨ antisymmetric (pos D)
       (least-element.⊥-is-bottom (bottom D))
       (lub2 (chain-complete D (chain-map (chain-fix-d-slide-33 c ⊥₁) if-mon)) λ {n} → reflexive (pos D))
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c ⊥₁) if-mon))
  ∎
if-cont-second {D} {c} {inj true} =
  let if-mon = slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂) in
  begin
    if-g (pair (inj true) (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    ⊔ (chain-complete D (proj₁-chain (proj₂-chain c)))
  ≡⟨ same-f-same-lub {D}
       {proj₁-chain (proj₂-chain c)}
       {chain-map (chain-fix-d-slide-33 c (inj true)) if-mon}
       refl
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c (inj true)) if-mon))
  ∎
if-cont-second {D} {c} {inj false} =
  let if-mon = slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂) in
  begin
    if-g (pair (inj false) (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    ⊔ (chain-complete D (proj₂-chain (proj₂-chain c)))
  ≡⟨ same-f-same-lub {D}
       {proj₂-chain (proj₂-chain c)}
       {chain-map (chain-fix-d-slide-33 c (inj false)) if-mon}
       refl
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c (inj false)) if-mon))
  ∎

if-cont : ∀ {D} → cont-fun (domain-product 𝔹⊥ (domain-product D D)) D
if-cont {D} =
  slide-33-prop-cont
    {𝔹⊥} {domain-product D D} {D}
    if-g
    (if-mon-first {D}) (λ {d} {e₁} {e₂} → if-mon-second D d e₁ e₂)
    if-cont-first
    (if-cont-second {D})

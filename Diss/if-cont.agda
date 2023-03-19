module if-cont where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import posets2
open import useful-functions using (𝔹⊥; pair; pair-η)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain


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
pair-η-pos = posets2.dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}

a≤b≡c→a≤c₂ : {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ⊑ b → b ≡ c → a ⊑ c
a≤b≡c→a≤c₂ a≤b Eq.refl = a≤b

slide-33-prop : ∀ {D E F}
  → (f : poset.A (domain.pos (domain-product D E)) → poset.A (domain.pos F))
  → ({d d′ : poset.A (domain.pos D)} → {e : poset.A (domain.pos E)} → (poset.R (domain.pos D)) d d′ → (poset.R (domain.pos F)) (f (pair d e)) (f (pair d′ e)))
  → ({d : poset.A (domain.pos D)} → {e e′ : poset.A (domain.pos E)} → (poset.R (domain.pos E)) e e′ → (poset.R (domain.pos F)) (f (pair d e)) (f (pair d e′)))
  → monotone-fun (domain.pos (domain-product D E)) (domain.pos F)

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


g (monotone (chain-fix-d-slide-33 {D} {E} c d)) n fzero = d
g (monotone (chain-fix-d-slide-33 {D} {E} c d)) n (fsucc i) = g (monotone (proj₂-chain {D} {E} c)) n
mon (monotone (chain-fix-d-slide-33 {D} {E} c d)) a≤a′ fzero = reflexive (pos D)
mon (monotone (chain-fix-d-slide-33 {D} {E} c d)) a≤a′ (fsucc fzero) = mon (monotone c) a≤a′ (fsucc fzero)

chain-fix-e-slide-33 : ∀ {D E}
  → chain (pos (domain-product D E))
  → A (pos E)
  → chain (pos (domain-product D E))


g (monotone (chain-fix-e-slide-33 {D} {E} c _)) n fzero = g (monotone (proj₁-chain {D} {E} c)) n
g (monotone (chain-fix-e-slide-33 _ e)) _ (fsucc fzero) = e
mon (monotone (chain-fix-e-slide-33 c _)) a≤a′ fzero = mon (monotone c) a≤a′ fzero
mon (monotone (chain-fix-e-slide-33 {E = E} _ _)) _ (fsucc fzero) = poset.reflexive (pos E)


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
  { monotone = record
    { g = λ n → g f (pair (g (monotone (posets2.proj₁-chain c)) n) (⊔ (chain-complete E (posets2.proj₂-chain c))))
    ; mon = λ n≤n′ → mon f (λ {fzero → (mon (monotone c) n≤n′ fzero); (fsucc fzero) → reflexive (pos E)})
    }
  }

[dₙ,eₙ],f,n→f[dₙ,eⱼ] : {D E F : domain} → (c : chain (pos (domain-product D E))) → (f : monotone-fun (pos (domain-product D E)) (pos F)) → ℕ → chain (pos F)
[dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n = record
  { monotone = record
    { g = λ j → g f (pair (g (monotone (posets2.proj₁-chain c)) n) (g (monotone (posets2.proj₂-chain c)) j))
    ; mon = λ j≤j′ → mon f λ { fzero → reflexive (pos D); (fsucc fzero) → mon (monotone c) j≤j′ (fsucc fzero)}
    }
  }

[dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] : {D E F : domain} → (c : chain (pos (domain-product D E))) → (f : monotone-fun (pos (domain-product D E)) (pos F)) → chain (pos F)
[dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] {D} {E} {F} c f = record
  { monotone = record
    { g = λ n → ⊔ (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n))
    ; mon = λ {n} {n′} n≤n′ → lub2 (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n))
      (transitive (pos F)
        (mon f (λ { fzero → mon (monotone c) n≤n′ fzero ; (fsucc fzero) → reflexive (pos E)}))
        (lub1 (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] {D} {E} {F} c f n′)))
      )
    }
  }

f[dᵢeⱼ] : {D E F : domain}
  → chain (pos (domain-product D E))
  → (f : (A (pos (domain-product D E)) → A (pos F)))
  → ({d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e) ) (f (pair d′ e)))
  → ({d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e) ) (f (pair d e′)))
  → monotone-fun nats²-pos (pos F)

a≡b≤c≡d→a≤d : {D : Set} → {_⊑_ : D → D → Set} → {a b c d : D} → a ≡ b → b ⊑ c → c ≡ d → a ⊑ d
a≡b≤c≡d→a≤d refl b⊑c refl = b⊑c

g (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) ⟨ i , j ⟩ = let dᵢ = g (monotone (proj₁-chain c)) i in
                                                            let eⱼ = g (monotone (proj₂-chain c)) j in
                                                            f (pair dᵢ eⱼ)


mon (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) {⟨ i , j ⟩} {⟨ i′ , j′ ⟩} ⟨ i≤i′ , j≤j′ ⟩ =
  a≡b≤c≡d→a≤d
    {A (pos F)} {R (pos F)}
    {f (pair ((g (monotone c)) i fzero) (g (monotone c) j (fsucc fzero)))}
    {g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) (pair ((g (monotone c)) i fzero) (g (monotone c) j (fsucc fzero))) }
    {g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) (pair ((g (monotone c)) i′ fzero) (g (monotone c) j′ (fsucc fzero)))}
    {f (pair ((g (monotone c)) i′ fzero) (g (monotone c) j′ (fsucc fzero)))}
      refl
      (mon (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) λ {fzero → mon (monotone c) i≤i′ fzero; (fsucc fzero) → mon (monotone c) j≤j′ (fsucc fzero)})
      refl

mon (slide-33-prop-cont {D} {E} {F} f mon-arg-1 mon-arg-2 _ _) = slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2
lub-preserve (slide-33-prop-cont {D} {E} {F} f mon-arg-1 mon-arg-2 cont-arg-1 cont-arg-2) c =
  let f-mon = slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2 in
  let ⊔dₙ = ⊔ (chain-complete D (posets2.proj₁-chain c)) in
  let ⊔eₙ = ⊔ (chain-complete E (posets2.proj₂-chain c)) in
  let ⊔[dₙeₙ] = ⊔ (chain-complete (domain-product D E) c) in
  let ⊔ᵢf[dᵢ,⊔eⱼ] = ⊔ (chain-complete F ([dₙ,eₙ],f→f[dₙ,⊔eⱼ] {D} {E} {F} c f-mon)) in
  let ⊔ᵢ⊔ⱼf[dᵢ,eⱼ] = ⊔ (chain-complete F ([dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] {D} {E} {F} c f-mon)) in
  begin
    f ⊔[dₙeₙ]
  ≡⟨ cong f (Eq.sym pair-η) ⟩
    f (pair (⊔dₙ) (⊔eₙ))
  ≡⟨ cont-arg-1 {c} {⊔eₙ} ⟩
    ⊔ (chain-complete F (chain-map (chain-fix-e-slide-33 c ⊔eₙ) f-mon))
  ≡⟨ posets2.same-f-same-lub {F} {chain-map (chain-fix-e-slide-33 c ⊔eₙ) f-mon} {[dₙ,eₙ],f→f[dₙ,⊔eⱼ] {D} {E} {F} c f-mon}
      (posets2.function-extensionality λ n →
        cong f (posets2.dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}))
   ⟩
    ⊔ᵢf[dᵢ,⊔eⱼ]
  ≡⟨ posets2.same-f-same-lub
       {F} {[dₙ,eₙ],f→f[dₙ,⊔eⱼ] c f-mon} {{!!}}
       (posets2.function-extensionality λ n → cont-arg-2 {c} {g (monotone (proj₁-chain {D} {E} c)) n})
   ⟩
     {!!}                
  ≡⟨ {!!} ⟩
    ⊔ᵢ⊔ⱼf[dᵢ,eⱼ]
  ≡⟨ same-f-same-lub
       {F} {[dₙ,eₙ],f→⊔ⱼ[f[dₙ,eⱼ]] c f-mon} {posets2.chain-⊔fₙₖ-with-n-fixed F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)}
       (posets2.function-extensionality λ x → {!!})
   ⟩
    ⊔ (chain-complete F (posets2.chain-⊔fₙₖ-with-n-fixed F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)))
  ≡⟨ posets2.diagonalising-lemma-1 F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2) ⟩
    ⊔ (chain-complete F (posets2.fₖₖ-chain F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)))
  ≡⟨ same-f-same-lub
       {F} {posets2.fₖₖ-chain F (f[dᵢeⱼ] {D} {E} {F} c f mon-arg-1 mon-arg-2)} {chain-map c f-mon}
       (posets2.function-extensionality (λ x → cong f pair-η))
   ⟩
    ⊔ (chain-complete F (chain-map c f-mon))
  ∎

if-g : ∀ {D} → A (pos (domain-product 𝔹⊥ (domain-product D D))) → A (pos D)
if-g {D} x with (x fzero)
...                     | inj false = x (fsucc fzero) (fsucc fzero)
...                     | inj true  = x (fsucc fzero) fzero
...                     | ⊥₁        = posets2.least-element.⊥ (bottom D)


if-mon-first : {D : domain} → {b b′ : A (pos 𝔹⊥)} → {e : A (pos (domain-product D D))} → (R (pos 𝔹⊥)) b b′ → (R (pos D)) (if-g {D} (pair b e) ) (if-g {D} (pair b′ e))


if-mon-first {D} z≼n = posets2.least-element.⊥-is-bottom (bottom D)
if-mon-first {D} x≼x = reflexive (pos D)

if-mon-second : {D : domain} → ({b : posets2.B⊥ Bool} → {e e′ : A (pos (domain-product D D))} → (R (pos (domain-product D D))) e e′ → (R (pos D)) (if-g {D} (pair b e)) (if-g {D} (pair b e′)))
if-mon-second {D} {⊥₁} a = posets2.least-element.⊥-is-bottom (domain.bottom D)
if-mon-second {D} {inj false} e≤e′ = e≤e′ (fsucc fzero) 
if-mon-second {D} {inj true} e≤e′ = e≤e′ fzero

if-cont-first : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {e : A (pos (domain-product D D))}
  → if-g (pair (⊔ (chain-complete 𝔹⊥ (posets2.proj₁-chain c))) e)
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (if-mon-second {D}))))

if-cont-first {D} {c} {e} = {!!}


if-cont-second : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {d : A (pos 𝔹⊥)}
  → if-g (pair d (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c d) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (if-mon-second {D}))))

if-cont-second {D} {c} {⊥₁} =
  begin
    if-g (pair ⊥₁ (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    posets2.least-element.⊥ (bottom D)
  ≡⟨ antisymmetric (pos D)
       (least-element.⊥-is-bottom (bottom D))
       (lub2 (chain-complete D (chain-map (chain-fix-d-slide-33 c ⊥₁) (slide-33-prop if-g if-mon-first if-mon-second))) λ {n} → reflexive (pos D))
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c ⊥₁) (slide-33-prop if-g if-mon-first if-mon-second)))
  ∎
if-cont-second {D} {c} {inj true} =
  begin
    if-g (pair (inj true) (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    ⊔ (chain-complete D (proj₁-chain (proj₂-chain c)))
  ≡⟨ same-f-same-lub
       {D} {proj₁-chain (proj₂-chain c)} {chain-map (chain-fix-d-slide-33 c (inj true)) (slide-33-prop if-g if-mon-first if-mon-second)}
       refl
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c (inj true)) (slide-33-prop if-g if-mon-first if-mon-second)))
  ∎
if-cont-second {D} {c} {inj false} =
  begin
    if-g (pair (inj false) (⊔ (chain-complete (domain-product D D) (proj₂-chain c))))
  ≡⟨ refl ⟩
    ⊔ (chain-complete D (proj₂-chain (proj₂-chain c)))
  ≡⟨ same-f-same-lub
       {D} {proj₂-chain (proj₂-chain c)} {chain-map (chain-fix-d-slide-33 c (inj false)) (slide-33-prop if-g if-mon-first if-mon-second)}
       refl
   ⟩
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c (inj false)) (slide-33-prop if-g if-mon-first if-mon-second)))
  ∎

if-cont : ∀ {D} → cont-fun (domain-product 𝔹⊥ (domain-product D D)) D
if-mon : ∀ {D} → monotone-fun (posets2.product-pos 𝔹⊥ (domain-product D D)) (pos D)
if-mon {D} = slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) (if-mon-second {D})

if-cont {D} = slide-33-prop-cont {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) if-mon-second if-cont-first if-cont-second

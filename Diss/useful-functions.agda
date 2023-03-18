
{-# OPTIONS --allow-unsolved-metas #-}
module useful-functions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import posets2 using (poset; lub; domain; monotone-fun; cont-fun; flat-domain; flat-domain-pos; inj; x≼x; chain-map; chain-complete-flat-domain-pos-B; domain-product; product-equality; ⊥₁; z≼n; function-domain; chain; product-pos; domain-dependent-product; fsucc; fzero; proj₁-chain; proj₂-chain)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open poset
open domain
open monotone-fun
open cont-fun
open lub
open chain


constant-fun-is-cont : {B : Set} → {D : domain} → B → cont-fun D (flat-domain B)
constant-fun-is-cont-mon : {B : Set} → {D : domain} → B → monotone-fun (domain.pos D) (domain.pos (flat-domain B))
constant-fun-is-cont-mon {B} {D} b = record { g = λ x → inj b
                                            ; mon = λ x → x≼x
                                            }
constant-fun-is-cont {B} {D} b = record { mon = constant-fun-is-cont-mon {B} {D} b
                                        ; lub-preserve = λ c → poset.antisymmetric (domain.pos (flat-domain B))
                                            (posets2.lub.lub1
                                              {domain.pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete-flat-domain-pos-B (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {0}
                                            )
                                            (posets2.lub.lub2
                                              {domain.pos (flat-domain B)}
                                              {chain-map c (constant-fun-is-cont-mon {B} {D} b)}
                                              (chain-complete-flat-domain-pos-B (chain-map c (constant-fun-is-cont-mon {B} {D} b)))
                                              {inj b}
                                              (λ {n} → x≼x)
                                            )
                                        }

pair-f : ∀ {D D₁ D₂ : domain} → cont-fun D D₁ → cont-fun D D₂ → cont-fun D (domain-product D₁ D₂)
g (mon (pair-f f₁ f₂)) x fzero = monotone-fun.g (cont-fun.mon f₁) x
g (mon (pair-f f₁ f₂)) x (fsucc i) = monotone-fun.g (cont-fun.mon f₂) x
mon (mon (pair-f f₁ f₂)) a≦a′ posets2.fzero = monotone-fun.mon (cont-fun.mon f₁) a≦a′
mon (mon (pair-f f₁ f₂)) a≦a′ (posets2.fsucc y) = monotone-fun.mon (cont-fun.mon f₂) a≦a′
lub-preserve (pair-f f₁ f₂) c = posets2.dependent-function-extensionality (λ { fzero → (lub-preserve f₁) c ; (fsucc x) → (lub-preserve f₂) c })


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

extend-function : ∀ {X Y} → (X → posets2.B⊥ Y) → cont-fun (flat-domain X) (flat-domain Y)
extend-function-mon : ∀ {X Y} → (X → posets2.B⊥ Y) → monotone-fun (flat-domain-pos X) (flat-domain-pos Y)
extend-function-mon f = record { g = λ { ⊥₁ → ⊥₁
                                       ; (inj x) → f x
                                       }
                               ; mon = λ {z≼n → z≼n; x≼x → x≼x}
                               }

mon (extend-function {X} {Y} f) = extend-function-mon f
lub-preserve (extend-function {X} {Y} f) c = poset.antisymmetric (flat-domain-pos Y)
  {!!}
  (lub2 (chain-complete-flat-domain-pos-B (chain-map c (extend-function-mon f)))
    (λ {n} → mon (extend-function-mon f) (lub1 (chain-complete (flat-domain X) c))))


ℕ⊥ : domain
𝔹⊥ : domain

ℕ⊥ = flat-domain ℕ
𝔹⊥ = flat-domain Bool

domain-dependent-projection : (I : Set) → (f : I → domain) → (i : I) → cont-fun (domain-dependent-product I f) (f i)
domain-dependent-projection-mon : (I : Set) → (f : I → domain) → (i : I) → monotone-fun (pos (domain-dependent-product I f)) (pos (f i))
domain-dependent-projection-mon I f i = record { g = λ p → p i ; mon = λ a≤a′ → a≤a′ i } 


domain-dependent-projection I f i = record { mon = domain-dependent-projection-mon I f i
                                           ; lub-preserve = λ c →
                                               posets2.same-f-same-lub
                                                 {f i} {posets2.chain-of-functions I f c i} {chain-map c (domain-dependent-projection-mon I f i)}
                                                 refl
                                           }

-- if-mon {D} = record { g = (λ { ⟨ inj true , ⟨ d , _ ⟩ ⟩ → d
--                              ; ⟨ inj false , ⟨ _ , d′ ⟩ ⟩ → d′
--                              ; ⟨ ⊥₁ , ⟨ _ , _ ⟩ ⟩ → posets2.least-element.⊥ (domain.bottom D)
--                              })
--                     ; mon = λ { {⟨ ⊥₁ , b₁ ⟩} → λ a≤a′ → (posets2.least-element.⊥-is-bottom (domain.bottom D))
--                               ; {⟨ inj true , _ ⟩} {⟨ inj true , _ ⟩} → λ a≤a′ → proj₁ (proj₂ a≤a′)
--                               ; {⟨ inj false , _ ⟩} {⟨ inj false , _ ⟩} → λ a≤a′ → proj₂ (proj₂ a≤a′)
--                               }
--                     }


pair : ∀ {D} {E} → (A (pos D)) → (A (pos E)) → A (pos (domain-product D E))
pair d e fzero = d
pair d e (fsucc fzero) = e

pair-equality : ∀ {D} {E} → {d₁ d₂ : A (pos D)} → {e₁ e₂ : A (pos E)} → (d₁ ≡ d₂) → (e₁ ≡ e₂) → pair {D} {E} d₁ e₁ ≡ pair {D} {E} d₂ e₂
pair-equality refl refl = refl

pair-η : ∀ {D} {E} → {a : poset.A (pos (domain-product D E))} → pair {D} {E} (a fzero) (a (fsucc fzero)) ≡ a
pair-η = posets2.dependent-function-extensionality λ {fzero → refl; (fsucc fzero) → refl}


slide-33-prop : ∀ {D E F}
  → (f : poset.A (domain.pos (domain-product D E)) → poset.A (domain.pos F))
  → ({d d′ : poset.A (domain.pos D)} → {e : poset.A (domain.pos E)} → (poset.R (domain.pos D)) d d′ → (poset.R (domain.pos F)) (f (pair d e)) (f (pair d′ e)))
  → ({d : poset.A (domain.pos D)} → {e e′ : poset.A (domain.pos E)} → (poset.R (domain.pos E)) e e′ → (poset.R (domain.pos F)) (f (pair d e)) (f (pair d e′)))
  → monotone-fun (domain.pos (domain-product D E)) (domain.pos F)

g (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) = f
mon (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) {a} {a′} a≤a′ =
  transitive (pos F)
    {!!}
    {!!}

chain-fix-d-slide-33 : ∀ {D E}
  → chain (pos (domain-product D E))
  → poset.A (domain.pos D)
  → chain (pos (domain-product D E))


g (monotone (chain-fix-d-slide-33 {D} {E} c d)) n fzero = d
g (monotone (chain-fix-d-slide-33 {D} {E} c d)) n (fsucc i) = g (monotone (posets2.proj₂-chain {D} {E} c)) n
mon (monotone (chain-fix-d-slide-33 {D} {E} c d)) a≤a′ fzero = poset.reflexive (pos D)
mon (monotone (chain-fix-d-slide-33 {D} {E} c d)) a≤a′ (fsucc fzero) = mon (monotone c) a≤a′ (fsucc fzero)

chain-fix-e-slide-33 : ∀ {D E}
  → chain (product-pos D E)
  → poset.A (domain.pos E)
  → chain (product-pos D E)


g (monotone (chain-fix-e-slide-33 {D} {E} c _)) n fzero = g (monotone (posets2.proj₁-chain {D} {E} c)) n
g (monotone (chain-fix-e-slide-33 _ e)) _ (fsucc fzero) = e
mon (monotone (chain-fix-e-slide-33 c _)) a≤a′ fzero = mon (monotone c) a≤a′ fzero
mon (monotone (chain-fix-e-slide-33 {E = E} _ _)) _ (fsucc fzero) = poset.reflexive (pos E)


slide-33-prop-cont : ∀ {D E F}
  → (f : (A (pos (domain-product D E)) → A (pos F)))
  → (mon-arg-1 : {d d′ : A (pos D)} → {e : A (pos E)} → (R (pos D)) d d′ → (R (pos F)) (f (pair d e) ) (f (pair d′ e)))
  → (mon-arg-2 : {d : A (pos D)} → {e e′ : A (pos E)} → (R (pos E)) e e′ → (R (pos F)) (f (pair d e) ) (f (pair d e′)))
  → ({c : chain (product-pos D E)}
    → {e : A (pos E)}
    → f (pair (⊔ (chain-complete D (posets2.proj₁-chain {D} {E} c))) e)
      ≡
      ⊔ (chain-complete F (chain-map (chain-fix-e-slide-33 {D} {E} c e) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)))
    )
  → ({c : chain (pos (domain-product D E))}
    → {d : A (pos D)}
    → f (pair d (⊔ (chain-complete E (posets2.proj₂-chain {D} {E} c))))
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
        (lub1 (chain-complete F ([dₙ,eₙ],f,n→f[dₙ,eⱼ] c f n′)))
      )
    }
  }
  
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
  ≡⟨ posets2.same-f-same-lub {F} {[dₙ,eₙ],f→f[dₙ,⊔eⱼ] c f-mon} {{!!}}
       (posets2.function-extensionality λ n → cont-arg-2)
   ⟩
    ⊔ (chain-complete F (chain-map {!!} {!!}))                
  ≡⟨ {!!} ⟩
    ⊔ᵢ⊔ⱼf[dᵢ,eⱼ]
  ≡⟨ {!!} ⟩
    ⊔
      (chain-complete F
       (chain-map c
        (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)))
  ∎

if-g : ∀ {D} → A (pos (domain-product 𝔹⊥ (domain-product D D))) → A (pos D)
--if-g {D} ⟨ ⊥₁ , _ ⟩ = posets2.least-element.⊥ (domain.bottom D)
--if-g {D} ⟨ inj false , a ⟩ = a (fsucc fzero)
--if-g {D} ⟨ inj true , a ⟩ = a fzero

if-mon-first : {D : domain} → {b b′ : A (pos 𝔹⊥)} → {e : A (pos (domain-product D D))} → (poset.R (domain.pos 𝔹⊥)) b b′ → (poset.R (domain.pos D)) (if-g {D} (pair b e) ) (if-g {D} (pair b′ e))


--if-mon-first {D} z≼n = posets2.least-element.⊥-is-bottom (domain.bottom D)
--if-mon-first {D} x≼x = poset.reflexive (domain.pos D)

if-mon-second : ∀ {D} → ({b : posets2.B⊥ Bool} → {e e′ : poset.A (domain.pos (domain-product D D))} → (poset.R (domain.pos (domain-product D D))) e e′ → (poset.R (domain.pos D)) (if-g {D} (pair b e)) (if-g {D} (pair b e′)))
--if-mon-second {D} {⊥₁} a = posets2.least-element.⊥-is-bottom (domain.bottom D)
--if-mon-second {D} {inj false} e≦e′ = e≦e′ (fsucc fzero) 
--if-mon-second {D} {inj true} e≦e′ = e≦e′ fzero --

if-cont-first : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {e : A (pos (domain-product D D))}
  → if-g (pair (⊔ (chain-complete 𝔹⊥ (posets2.proj₁-chain c))) e)
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-e-slide-33 c e) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) if-mon-second)))

if-cont-second : ∀ {D}
  → {c : chain (pos (domain-product 𝔹⊥ (domain-product D D)))}
  → {d : A (pos 𝔹⊥)}
  → if-g (pair d (⊔ (chain-complete (domain-product D D) (posets2.proj₂-chain c))))
    ≡
    ⊔ (chain-complete D (chain-map (chain-fix-d-slide-33 c d) (slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) if-mon-second)))



if-cont : ∀ {D} → cont-fun (domain-product 𝔹⊥ (domain-product D D)) D
if-mon : ∀ {D} → monotone-fun (posets2.product-pos 𝔹⊥ (domain-product D D)) (domain.pos D)
if-mon {D} = slide-33-prop {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) if-mon-second

if-cont {D} = slide-33-prop-cont {𝔹⊥} {domain-product D D} {D} if-g (if-mon-first {D}) if-mon-second if-cont-first if-cont-second


cur-cont : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → cont-fun D′ (function-domain D E)

cur-mon : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → monotone-fun (pos D′) (pos (function-domain D E))

g (mon (g (cur-mon {D} {D′} {E} f) d′)) d = g (mon f) (pair d′ d)
mon (mon (g (cur-mon {D} {D′} {E} f) d′)) a≤a′ = mon (mon f) λ {fzero → reflexive (pos D′); (fsucc fzero) → a≤a′}
lub-preserve (g (cur-mon {D} {D′} {E} f) d′) c = {!!}

mon (cur-mon {D} {D′} {E} f) a≤a′ = mon (mon f) λ {fzero → a≤a′; (fsucc fzero) → reflexive (pos D)}

         
cur-cont {D} {D′} {E} f = record { mon = cur-mon {D} {D′} {E} f
                                 ; lub-preserve = λ c → {!!}
                                 }


ev-cont : ∀ {D E} → cont-fun (domain-product (function-domain D E) D) E
ev-mon : ∀ {D E} → monotone-fun (pos (domain-product (function-domain D E) D)) (pos E)

monotone-fun.g (ev-mon {D} {E}) x = g (mon (x fzero)) (x (fsucc fzero))
monotone-fun.mon (ev-mon {D} {E}) {x} {y} a≤a′ = poset.transitive (pos E)
                                                   (mon (mon (x fzero)) (a≤a′ (fsucc fzero)))
                                                   (a≤a′ fzero {y (fsucc fzero)})

fₙ,dₙ→fₙ[dₙ] : ∀ {D} {E} → (c : chain (domain.pos (domain-product (function-domain D E) D))) → chain (domain.pos E)
fₙ,dₙ→fₙ[dₙ] c = chain-map c ev-mon

fₙ,dₙ→fₙ[⊔dₙ] : ∀ {D} {E} → (c : chain (domain.pos (domain-product (function-domain D E) D))) → chain (domain.pos E)
fₙ,dₙ→fₙ[⊔dₙ] {D} {E} c = record
  { monotone = record
    { g = λ n → g (mon (g (monotone (posets2.proj₁-chain c)) n)) (⊔ (domain.chain-complete D (posets2.proj₂-chain c)))
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

--double-index-fun : ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → monotone-fun posets2.nats²-pos (pos E)
--double-index-g : ∀ {D} {E} → (c : chain (pos (domain-product (function-domain D E) D))) → ℕ × ℕ → poset.A (pos E) 
--double-index-g {D} {E} c = {!!}
--double-index-fun {D} {E} c = {!!}

--   begin
--     ev[⊔fₙ,⊔dₙ]
--   ≡⟨ refl ⟩
--     [⊔fₙ][⊔dₙ]
--   ≡⟨ posets2.same-f-same-lub E
--       (posets2.chain-of-fₙ[d] D E (posets2.proj₁-chain {D→E} {D} c)
--         (posets2.lub.⊔ (domain.chain-complete D (posets2.proj₂-chain {D→E} {D} c))))
--       (fₙ,dₙ→fₙ[⊔dₙ] c)
--       refl
--    ⟩
--     ⊔[fₙ[⊔dₙ]]
--   ≡⟨ posets2.same-f-same-lub E
--     (fₙ,dₙ→fₙ[⊔dₙ] c)
--     (fₙ,dₙ→⊔ⱼfᵢdⱼ c)
--     (posets2.function-extensionality
--       λ n → cont-fun.lub-preserve (monotone-fun.g (chain.monotone fₙ-chain) n) (posets2.proj₂-chain {D→E} {D} c))
--    ⟩
--     ⊔⊔fᵢdⱼ
--   ≡⟨ posets2.same-f-same-lub E
--       (fₙ,dₙ→⊔ⱼfᵢdⱼ c)
--       (posets2.chain-⊔fₖₙ-with-n-fixed E (double-index-fun c))
--       (posets2.function-extensionality
--         λ n → posets2.same-f-same-lub E
--               (chain-map (posets2.proj₂-chain {D→E} {D} c) (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) n)))
--               (posets2.chain-fₘₙ-with-n-fixed E (double-index-fun c) n)
--               (posets2.function-extensionality λ m → {!!}))
--    ⟩
--     posets2.lub.⊔ (domain.chain-complete E (posets2.chain-⊔fₖₙ-with-n-fixed E (double-index-fun c)))
--   ≡⟨ posets2.diagonalising-lemma-2 E (double-index-fun c) ⟩
--     posets2.lub.⊔ (domain.chain-complete E (posets2.fₖₖ-chain E (double-index-fun c)))
--   ≡⟨ posets2.same-f-same-lub E
--     (posets2.fₖₖ-chain E (double-index-fun c))
--     (fₙ,dₙ→fₙ[dₙ] c)
--     (posets2.function-extensionality
--       λ n → refl)
--    ⟩ 
--     ⊔fₙdₙ
--   ≡⟨ refl ⟩
--     ⊔ev[fₙ,dₙ]
--   ∎

cont-fun.mon (ev-cont {D} {E}) = ev-mon {D} {E}
cont-fun.lub-preserve (ev-cont {D} {E}) c =
   let ev = monotone-fun.g (ev-mon {D} {E}) in
   let D→E = function-domain D E in
   let fₙ-chain = posets2.proj₁-chain {D→E} {D} c in
   let dₙ-chain = posets2.proj₂-chain {D→E} {D} c in
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
  ≡⟨ posets2.same-f-same-lub
       {E} {posets2.chain-of-fₙ[d] D E fₙ-chain ⊔dₙ} {fₙ,dₙ→fₙ[⊔dₙ] c}
       refl
   ⟩
    ⊔[fₙ[⊔dₙ]]
  ≡⟨ posets2.same-f-same-lub
       {E} {fₙ,dₙ→fₙ[⊔dₙ] c} {fₙ,dₙ→⊔ⱼfᵢdⱼ c}
       (posets2.function-extensionality λ n → lub-preserve (g (monotone fₙ-chain) n) dₙ-chain)
   ⟩
    ⊔ᵢ⊔ⱼfᵢdⱼ
  ≡⟨ {!!} ⟩
    ⊔fₙdₙ
  ≡⟨ refl ⟩
    ⊔ev[fₙ,dₙ]
    ∎


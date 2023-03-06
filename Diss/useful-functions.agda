
{-# OPTIONS --allow-unsolved-metas #-} 
module useful-functions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import posets2 using (poset; domain; monotone-fun; cont-fun; flat-domain; inj; x≼x; chain-map; chain-complete-flat-domain-pos-B; domain-product; product-equality; ⊥₁; z≼n; function-domain; chain; product-pos; domain-dependent-product)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

constant-fun-is-cont : ∀ {B : Set} → {D : domain} → B → cont-fun D (flat-domain B)
constant-fun-is-cont-mon : ∀ {B : Set} → {D : domain} → B → monotone-fun (domain.pos D) (domain.pos (flat-domain B))
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
pair-f f₁ f₂ = record { mon = record { g = λ d → ⟨ monotone-fun.g (cont-fun.mon f₁) d , monotone-fun.g (cont-fun.mon f₂) d ⟩
                                     ; mon = λ a≤a′ → ⟨ monotone-fun.mon (cont-fun.mon f₁) a≤a′ , monotone-fun.mon (cont-fun.mon f₂) a≤a′ ⟩
                                     }
                      ; lub-preserve = λ c → product-equality ((cont-fun.lub-preserve f₁) c) ((cont-fun.lub-preserve f₂) c)
                      }

_∘_ : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → cont-fun D₁ D₃

∘-mon : ∀ {D₁ D₂ D₃} → cont-fun D₂ D₃ → cont-fun D₁ D₂ → monotone-fun (domain.pos D₁) (domain.pos D₃)
∘-mon g f = record { g = λ x → monotone-fun.g (cont-fun.mon g) (monotone-fun.g (cont-fun.mon f) x)
                   ; mon = λ a≤a′ → monotone-fun.mon (cont-fun.mon g) (monotone-fun.mon (cont-fun.mon f) a≤a′)
                   }


_∘_ {D₁ = D₁} {D₂ = D₂} {D₃ = D₃} g f  =
                     record { mon = ∘-mon g f
                            ; lub-preserve = λ c →
                            begin
                              monotone-fun.g (cont-fun.mon g)
                                (monotone-fun.g (cont-fun.mon f)
                                  (posets2.lub.⊔ (domain.chain-complete D₁ c)))
                            ≡⟨ cong (monotone-fun.g (cont-fun.mon g)) (cont-fun.lub-preserve f c) ⟩
                              monotone-fun.g (cont-fun.mon g)
                                (posets2.lub.⊔
                                 (domain.chain-complete D₂ (chain-map c (cont-fun.mon f))))
                            ≡⟨ cont-fun.lub-preserve g (chain-map c (cont-fun.mon f)) ⟩
                              posets2.lub.⊔ (domain.chain-complete D₃ (chain-map c (∘-mon g f)))
                            ∎ 
                            }

extend-function : ∀ {X Y} → (X → posets2.B⊥ Y) → cont-fun (flat-domain X) (flat-domain Y)
extend-function-mon : ∀ {X Y} → (X → posets2.B⊥ Y) → monotone-fun (posets2.flat-domain-pos X) (posets2.flat-domain-pos Y)
extend-function-mon f = record { g = λ { ⊥₁ → ⊥₁
                                       ; (inj x) → f x
                                       }
                               ; mon = λ {z≼n → z≼n; x≼x → x≼x}
                               }

extend-function {X} {Y} f = record { mon = extend-function-mon f
                           ; lub-preserve = λ c → poset.antisymmetric (posets2.flat-domain-pos Y)
                               {!!}
                               (posets2.lub.lub2
                                  (chain-complete-flat-domain-pos-B
                                   (chain-map c (extend-function-mon f)))
                                  λ {n} → monotone-fun.mon (extend-function-mon f) (posets2.lub.lub1 (domain.chain-complete (flat-domain X) c)))
                           }

ℕ⊥ : domain
𝔹⊥ : domain

ℕ⊥ = flat-domain ℕ
𝔹⊥ = flat-domain Bool


if-cont : ∀ {D} → cont-fun (domain-product 𝔹⊥ (domain-product D D)) D
if-mon : ∀ {D} → monotone-fun (posets2.product-pos 𝔹⊥ (domain-product D D)) (domain.pos D)

domain-dependent-projection : (I : Set) → (f : I → domain) → (i : I) → cont-fun (domain-dependent-product I f) (f i)

domain-dependent-projection I f i = record { mon = record { g = λ p → p i
                                                          ; mon = λ a≤a′ → a≤a′ i
                                                          }
                                           ; lub-preserve = {!!}
                                           }

if-mon {D} = record { g = (λ { ⟨ inj true , ⟨ d , _ ⟩ ⟩ → d
                             ; ⟨ inj false , ⟨ _ , d′ ⟩ ⟩ → d′
                             ; ⟨ ⊥₁ , ⟨ _ , _ ⟩ ⟩ → posets2.least-element.⊥ (domain.bottom D)
                             })
                    ; mon = λ { {⟨ ⊥₁ , b₁ ⟩} → λ a≤a′ → (posets2.least-element.⊥-is-bottom (domain.bottom D))
                              ; {⟨ inj true , _ ⟩} {⟨ inj true , _ ⟩} → λ a≤a′ → proj₁ (proj₂ a≤a′)
                              ; {⟨ inj false , _ ⟩} {⟨ inj false , _ ⟩} → λ a≤a′ → proj₂ (proj₂ a≤a′)
                              }
                    }



slide-33-prop : ∀ {D E F}
  → (f : (poset.A (domain.pos D)) × (poset.A (domain.pos E)) → poset.A (domain.pos F))
  → ({d d′ : poset.A (domain.pos D)} → {e : poset.A (domain.pos E)} → (poset.R (domain.pos D)) d d′ → (poset.R (domain.pos F)) (f ⟨ d , e ⟩ ) (f ⟨ d′ , e ⟩))
  → ({d : poset.A (domain.pos D)} → {e e′ : poset.A (domain.pos E)} → (poset.R (domain.pos E)) e e′ → (poset.R (domain.pos F)) (f ⟨ d , e ⟩ ) (f ⟨ d , e′ ⟩))
  → monotone-fun (domain.pos (domain-product D E)) (domain.pos F)
slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2 = record { g = f
                                                         ; mon = λ { {a} {b} ⟨ m≤m′ , n≤n′ ⟩ → poset.transitive (domain.pos F) (mon-arg-1 m≤m′) (mon-arg-2 n≤n′)}
                                                         }

chain-fix-d-slide-33 : ∀ {D E}
  → chain (product-pos D E)
  → poset.A (domain.pos D)
  → chain (product-pos D E)


chain-fix-d-slide-33 {D} {E} c d = record { monotone = record { g = λ n → ⟨ d , monotone-fun.g (chain.monotone (posets2.proj₂-chain {D} {E} c)) n ⟩
                                                              ; mon = λ a≤a′ → ⟨ poset.reflexive (domain.pos D) , proj₂ (monotone-fun.mon (chain.monotone c) a≤a′) ⟩
                                                              }
                                          }

chain-fix-e-slide-33 : ∀ {D E}
  → chain (product-pos D E)
  → poset.A (domain.pos E)
  → chain (product-pos D E)


chain-fix-e-slide-33 {D} {E} c e = record { monotone = record { g = λ n → ⟨ monotone-fun.g (chain.monotone (posets2.proj₁-chain {D} {E} c)) n , e ⟩
                                                              ; mon = λ a≤a′ → ⟨ proj₁ (monotone-fun.mon (chain.monotone c) a≤a′) , poset.reflexive (domain.pos E) ⟩
                                                              }
                                          }


slide-33-prop-cont : ∀ {D E F}
  → (f : (poset.A (domain.pos D)) × (poset.A (domain.pos E)) → poset.A (domain.pos F))
  → (mon-arg-1 : {d d′ : poset.A (domain.pos D)} → {e : poset.A (domain.pos E)} → (poset.R (domain.pos D)) d d′ → (poset.R (domain.pos F)) (f ⟨ d , e ⟩ ) (f ⟨ d′ , e ⟩))
  → (mon-arg-2 : {d : poset.A (domain.pos D)} → {e e′ : poset.A (domain.pos E)} → (poset.R (domain.pos E)) e e′ → (poset.R (domain.pos F)) (f ⟨ d , e ⟩ ) (f ⟨ d , e′ ⟩))
  → ({c : chain (product-pos D E)} → {e : poset.A (domain.pos E)} → f ⟨ posets2.lub.⊔ (domain.chain-complete D (posets2.proj₁-chain {D} {E} c)) , e ⟩ ≡ posets2.lub.⊔ (domain.chain-complete F (chain-map (chain-fix-e-slide-33 {D} {E} c e) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) )))
  → ({c : chain (product-pos D E)} → {d : poset.A (domain.pos D)} → f ⟨ d , posets2.lub.⊔ (domain.chain-complete E (posets2.proj₂-chain {D} {E} c)) ⟩ ≡ posets2.lub.⊔ (domain.chain-complete F (chain-map (chain-fix-d-slide-33 {D} {E} c d) (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2) )))
  → cont-fun (domain-product D E) F



slide-33-prop-cont {D} {E} {F} f mon-arg-1 mon-arg-2 cont-arg-1 cont-arg-2  = record
  { mon = slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2
  ; lub-preserve = λ c → begin
                           monotone-fun.g
                             (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)
                             (posets2.lub.⊔ (domain.chain-complete (domain-product D E) c))
                         ≡⟨ cont-arg-1 {chain-fix-e-slide-33 {D} {E} c (posets2.lub.⊔ (domain.chain-complete E (posets2.proj₂-chain {D} {E} c)))} ⟩
                           posets2.lub.⊔ (domain.chain-complete F (
                             chain-map
                               (chain-fix-e-slide-33 {D} {E} c (posets2.lub.⊔ (domain.chain-complete E (posets2.proj₂-chain {D} {E} c))))
                               (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2)
                           ))
                         ≡⟨ posets2.same-f-same-lub F
                              (chain-map
                                (chain-fix-e-slide-33 {D} {E} c (posets2.lub.⊔ (domain.chain-complete E (posets2.proj₂-chain {D} {E} c))))
                                (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2))
                              {!!}
                              (posets2.function-extensionality λ n →
                                cont-arg-2 {{!!}} {proj₁ (monotone-fun.g (chain.monotone c) n)})
                          ⟩
                           {!posets2.lub.⊔ (domain.chain-complete F (
                             posets2.!}
                         ≡⟨ {!!} ⟩
                           {!!}
                         ≡⟨ {!!} ⟩
                           {!!}
                         ≡⟨ {!!} ⟩
                           posets2.lub.⊔
                             (domain.chain-complete F
                              (chain-map c
                               (slide-33-prop {D} {E} {F} f mon-arg-1 mon-arg-2))) 
                         ∎
  }

if-g : ∀ {D} → poset.A (posets2.product-pos 𝔹⊥ (domain-product D D)) → poset.A (domain.pos D)
if-g {D} ⟨ ⊥₁ , _ ⟩ = posets2.least-element.⊥ (domain.bottom D)
if-g ⟨ inj false , ⟨ _ , d′ ⟩ ⟩ = d′
if-g ⟨ inj true , ⟨ d , _ ⟩ ⟩ = d

if-mon-first : ∀ {D} → ∀ {b b′} → ∀ {e} → (poset.R (domain.pos 𝔹⊥)) b b′ → (poset.R (domain.pos D)) (if-g {D} ⟨ b , e ⟩ ) (if-g {D} ⟨ b′ , e ⟩)
if-mon-first {D} z≼n = posets2.least-element.⊥-is-bottom (domain.bottom D)
if-mon-first {D} x≼x = poset.reflexive (domain.pos D)

if-mon-second : ∀ {D} → ({b : posets2.B⊥ Bool} → {e e′ : poset.A (domain.pos (domain-product D D))} → (poset.R (domain.pos (domain-product D D))) e e′ → (poset.R (domain.pos D)) (if-g {D} ⟨ b , e ⟩ ) (if-g {D} ⟨ b , e′ ⟩))
if-mon-second {D} {b = ⊥₁} x = posets2.least-element.⊥-is-bottom (domain.bottom D)
if-mon-second {b = inj false} ⟨ _ , n≤n′ ⟩ = n≤n′
if-mon-second {b = inj true} ⟨ m≤m′ , _ ⟩ = m≤m′

--if-cont-first : ∀ {D} → ({c : chain (product-pos 𝔹⊥ (domain-product D D))} → {e : poset.A (domain.pos (domain-product D D))} → if-g ⟨ posets2.lub.⊔ (domain.chain-complete 𝔹⊥ (posets2.proj₁-chain c)) , e ⟩ ≡ posets2.lub.⊔ (domain.chain-complete (domain-product 𝔹⊥ (domain-product D D)) (chain-map (chain-fix-e-slide-33 c e) (slide-33-prop if-g if-mon-first if-mon-second) )))

--if-cont-second : ∀ {D} → ({c : chain (product-pos 𝔹⊥ (domain-product D D))} → {d : poset.A (domain.pos 𝔹⊥)} → if-g ⟨ d , posets2.lub.⊔ (domain.chain-complete (domain-product D D) (posets2.proj₂-chain c)) ⟩ ≡ posets2.lub.⊔ (domain.chain-complete (domain-product 𝔹⊥ (domain-product D D)) (chain-map (chain-fix-d-slide-33 c d) (slide-33-prop if-g if-mon-first if-mon-second) )))


if-cont {D} = slide-33-prop-cont {𝔹⊥} {domain-product D D} {D} (if-g {D}) (if-mon-first {D}) {!!} {!!} {!!}


cur-cont : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → cont-fun D′ (function-domain D E)

cur-mon : ∀ {D D′ E} → cont-fun (domain-product D′ D) E → monotone-fun (domain.pos D′) (domain.pos (function-domain D E))
cur-mon {D} {D′} {E} f =
  record { g = λ d′ →
    record { mon =
      record { g = λ d → monotone-fun.g (cont-fun.mon f) ⟨ d′ , d ⟩
             ; mon = λ a≤a′ → monotone-fun.mon (cont-fun.mon f) ⟨ (poset.reflexive (domain.pos D′)) , a≤a′ ⟩
             }
           ; lub-preserve = λ c → {!!}
           }
         ; mon = λ a≤a′ → λ {d} → monotone-fun.mon (cont-fun.mon f) ⟨ a≤a′ , poset.reflexive (domain.pos D) ⟩
         }
         
cur-cont {D} {D′} {E} f = record { mon = cur-mon {D} {D′} {E} f
                                 ; lub-preserve = λ c → {!!}
                                 }


ev-cont : ∀ {D E} → cont-fun (domain-product (function-domain D E) D) E
ev-mon : ∀ {D E} → monotone-fun (posets2.product-pos (function-domain D E) D) (domain.pos E)
ev-mon {D} {E} = record { g = λ {⟨ f , d ⟩ → monotone-fun.g (cont-fun.mon f) d}
                        ; mon = λ { {⟨ f , d ⟩} {⟨ f′ , d′ ⟩} ⟨ f≤f′ , d≤d′ ⟩ →
                          poset.transitive (domain.pos E)
                            (monotone-fun.mon (cont-fun.mon f) d≤d′)
                            (f≤f′ {d′}) }
                        }
ev-lub-preserve : ∀ {D E}
  → (c : chain (posets2.product-pos (function-domain D E) D))
  → (monotone-fun.g ev-mon)
    ⟨
      posets2.function-domain-⊔ D E (posets2.proj₁-chain {function-domain D E} {D} c)
    ,
      posets2.lub.⊔ (domain.chain-complete D (posets2.proj₂-chain {function-domain D E} {D} c))
    ⟩
    ≡ posets2.lub.⊔ (domain.chain-complete E (chain-map c ev-mon))

fₙ,dₙ→fₙ[dₙ] : ∀ {D} {E} → (c : chain (posets2.product-pos (function-domain D E) D)) → chain (domain.pos E)
fₙ,dₙ→fₙ[dₙ] c = chain-map c ev-mon

fₙ,dₙ→fₙ[⊔dₙ] : ∀ {D} {E} → (c : chain (posets2.product-pos (function-domain D E) D)) → chain (domain.pos E)
fₙ,dₙ→fₙ[⊔dₙ] {D} {E} c =
  let D→E = function-domain D E in
  let f = monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) in
  let ⊔dₙ = (posets2.lub.⊔ (domain.chain-complete D (posets2.proj₂-chain {D→E} {D} c))) in
  record
  { monotone =
    record { g = λ n → monotone-fun.g (cont-fun.mon (f n)) ⊔dₙ
           ; mon = λ a≤a′ → monotone-fun.mon (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) a≤a′
           }
  }

fₙ,dₙ→⊔ⱼfᵢdⱼ :  ∀ {D} {E} → (c : chain (posets2.product-pos (function-domain D E) D)) → chain (domain.pos E)

fₙ,dₙ→⊔ⱼfᵢdⱼ {D}{E} c =
  let D→E = function-domain D E in
  record
  { monotone =
    record { g = λ i → posets2.lub.⊔ ((domain.chain-complete E) (chain-map (posets2.proj₂-chain {D→E} {D} c) (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) i))))
           ; mon = λ {a} {a′} a≤a′ →
             posets2.same-f-same-lub-≤ E
               (chain-map (posets2.proj₂-chain {D→E} {D} c) (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) a))) (chain-map (posets2.proj₂-chain {D→E} {D} c)
                                                                                                                            (cont-fun.mon
                                                                                                                             (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) a′)))
               λ n →
                 monotone-fun.mon (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) a≤a′ {monotone-fun.g (chain.monotone (posets2.proj₂-chain {D→E} {D} c)) n}
           }
  }

double-index-fun : ∀ {D} {E} → (c : chain (posets2.product-pos (function-domain D E) D)) → monotone-fun posets2.nats²-pos (domain.pos E)
double-index-g : ∀ {D} {E} → (c : chain (posets2.product-pos (function-domain D E) D)) → ℕ × ℕ → poset.A (domain.pos E) 
double-index-g {D} {E} c ⟨ m , n ⟩ =
  let D→E = function-domain D E in
  monotone-fun.g (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) m)) (monotone-fun.g (chain.monotone (posets2.proj₂-chain {D→E} {D} c))n)   

double-index-fun {D} {E} c =
  let D→E = function-domain D E in
  record
    { g = double-index-g c 
    ; mon = λ { {⟨ m , n ⟩} {⟨ m′ , n′ ⟩} ⟨ m≤m′ , n≤n′ ⟩ →
                poset.transitive (domain.pos E)
                  ((monotone-fun.mon (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) m≤m′ {monotone-fun.g (chain.monotone (posets2.proj₂-chain {D→E} {D} c)) n}))
                  ((monotone-fun.mon (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) m′)) (monotone-fun.mon (chain.monotone (posets2.proj₂-chain {D→E} {D} c)) n≤n′)))
              }
    }

ev-lub-preserve {D} {E} c =
  let ev = monotone-fun.g ev-mon in
  let D→E = function-domain D E in
  let fₙ-chain = (posets2.proj₁-chain {D→E} {D} c) in
  let ⊔fₙ = posets2.function-domain-⊔ D E (posets2.proj₁-chain {D→E} {D} c) in
  let ⊔dₙ = posets2.lub.⊔ (domain.chain-complete D (posets2.proj₂-chain {D→E} {D} c)) in
  let ev[⊔fₙ,⊔dₙ] = ev ⟨ ⊔fₙ , ⊔dₙ ⟩ in
  let [⊔fₙ][⊔dₙ] = monotone-fun.g (cont-fun.mon ⊔fₙ) ⊔dₙ in
  let ⊔[fₙ[⊔dₙ]] = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→fₙ[⊔dₙ] c)) in
  let ⊔⊔fᵢdⱼ = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→⊔ⱼfᵢdⱼ c)) in
  let ⊔fₙdₙ = posets2.lub.⊔ (domain.chain-complete E (fₙ,dₙ→fₙ[dₙ] c)) in
  let ⊔ev[fₙ,dₙ] = posets2.lub.⊔ (domain.chain-complete E (chain-map c ev-mon)) in
  begin
    ev[⊔fₙ,⊔dₙ]
  ≡⟨ refl ⟩
    [⊔fₙ][⊔dₙ]
  ≡⟨ posets2.same-f-same-lub E
      (posets2.chain-of-fₙ[d] D E (posets2.proj₁-chain {D→E} {D} c)
        (posets2.lub.⊔ (domain.chain-complete D (posets2.proj₂-chain {D→E} {D} c))))
      (fₙ,dₙ→fₙ[⊔dₙ] c)
      refl
   ⟩
    ⊔[fₙ[⊔dₙ]]
  ≡⟨ posets2.same-f-same-lub E
    (fₙ,dₙ→fₙ[⊔dₙ] c)
    (fₙ,dₙ→⊔ⱼfᵢdⱼ c)
    (posets2.function-extensionality
      λ n → cont-fun.lub-preserve (monotone-fun.g (chain.monotone fₙ-chain) n) (posets2.proj₂-chain {D→E} {D} c))
   ⟩
    ⊔⊔fᵢdⱼ
  ≡⟨ posets2.same-f-same-lub E
      (fₙ,dₙ→⊔ⱼfᵢdⱼ c)
      (posets2.chain-⊔fₖₙ-with-n-fixed E (double-index-fun c))
      (posets2.function-extensionality
        λ n → posets2.same-f-same-lub E
              (chain-map (posets2.proj₂-chain {D→E} {D} c) (cont-fun.mon (monotone-fun.g (chain.monotone (posets2.proj₁-chain {D→E} {D} c)) n)))
              (posets2.chain-fₘₙ-with-n-fixed E (double-index-fun c) n)
              (posets2.function-extensionality λ m → {!!}))
   ⟩
    posets2.lub.⊔ (domain.chain-complete E (posets2.chain-⊔fₖₙ-with-n-fixed E (double-index-fun c)))
  ≡⟨ posets2.diagonalising-lemma-2 E (double-index-fun c) ⟩
    posets2.lub.⊔ (domain.chain-complete E (posets2.fₖₖ-chain E (double-index-fun c)))
  ≡⟨ posets2.same-f-same-lub E
    (posets2.fₖₖ-chain E (double-index-fun c))
    (fₙ,dₙ→fₙ[dₙ] c)
    (posets2.function-extensionality
      λ n → refl)
   ⟩ 
    ⊔fₙdₙ
  ≡⟨ refl ⟩
    ⊔ev[fₙ,dₙ]
  ∎

--mon (ev-cont {D} {E}) = ?

ev-cont {D} {E} = record { mon = ev-mon
                         ; lub-preserve = ev-lub-preserve
                         }

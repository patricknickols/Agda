module DomainTheory.BasicObjects.posets-etc where

open import misc

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_; cong)

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂) 

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsucc : {n : ℕ} → Fin n → Fin (suc n)

record poset : Set₁ where
  field
    A : Set
    R : A → A → Set
    reflexive     : ∀ {a : A} → R a a 
    antisymmetric : ∀ {a b : A} → R a b → R b a → a ≡ b
    transitive    : ∀ {a b c : A} → R a b → R b c → R a c
open poset

a≡b→a≤b : {P : poset} → {a b : A P} → a ≡ b → (R P) a b
a≡b→a≤b {P} Eq.refl = reflexive P

a≤b≡c≤d→a≤d : ∀ (P : poset) {a b c d : (A P)} → (R P) a b → c ≡ b → (R P) c d → (R P) a d
a≤b≡c≤d→a≤d P a⊑b Eq.refl c⊑d = (transitive P) a⊑b c⊑d

nats : poset
nats = record
         { A = ℕ
         ; R = _≤_
         ; reflexive = refl-≤
         ; antisymmetric = antisym-≤
         ; transitive = trans-≤
         }

record monotone-fun (P : poset) (Q : poset) : Set where
  field
    g : A P → A Q
    mon : ∀ {a a′ : A P} → (R P) a a′ → (R Q) (g a) (g a′)
open monotone-fun

chain : (P≤ : poset) → Set
chain P≤ = monotone-fun nats P≤

record lub {P⊑ : poset} (c : chain P⊑) : Set where
  private P : Set
  P = A P⊑
  private _⊑_ : P → P → Set
  _⊑_ = R P⊑
  private f : ℕ → P
  f = g c
  field
    ⊔ : P
    lub1 : ∀ {n : ℕ} → f n ⊑ ⊔
    lub2 : ∀ {d′ : P} → (∀ {n : ℕ} → f n ⊑ d′) → ⊔ ⊑ d′
open lub

record least-element (P⊑ : poset) : Set where
  private P : Set
  P = A P⊑
  private _⊑_ : P → P → Set
  _⊑_ = R P⊑
  field
    ⊥ : P
    ⊥-is-bottom : ∀ {a : P} → ⊥ ⊑ a
open least-element

record domain : Set₁ where
  field
    pos : poset
    chain-complete : ∀ (c : chain pos) → lub c
    bottom : least-element pos
open domain

chain-map : {P≤ : poset} {Q≤ : poset} (c : chain P≤) → (monotone-fun P≤ Q≤) → (chain Q≤) 

chain-map c f = record { g = λ n → let dₙ = g c n in
                             g f dₙ
                       ; mon = λ a≤a′ → mon f (mon c a≤a′)
                       }

record cont-fun (P P′ : domain) : Set where
  field
    mon : monotone-fun (pos P) (pos P′)
    lub-preserve : (c : chain (pos P))
      → let f = (g mon) in
        let ⊔dₙ = (⊔ (chain-complete P c)) in
        let ⊔fdₙ = ⊔ (chain-complete P′ (chain-map c mon)) in
        f ⊔dₙ ≡ ⊔fdₙ
open cont-fun

record pre-fixed (P≤ : poset) (f : A P≤ → A P≤) : Set where
  field
    d : A P≤
    pre-fix : (R P≤) (f d) d
open pre-fixed

record least-pre-fixed (P≤ : poset) (f : A P≤ → A P≤) : Set where
  field
    lfp1 : pre-fixed P≤ f
    lfp2 : ∀ {d′ : A P≤} → (R P≤) (f d′) d′ → (R P≤) (d lfp1) d′
open least-pre-fixed


iterate : {D : Set} (n : ℕ) → (D → D) → (D → D)
iterate 0 f d = d 
iterate (suc n) f d = f ((iterate n f) d) 
                                             
postulate
  function-extensionality : ∀ {A B : Set} {f f′ : A → B}
    → (∀ (x : A) → f x ≡ f′ x)
      -----------------------
    → f ≡ f′

postulate
  cont-fun-extensionality : ∀ {P P′ : domain} {f f′ : cont-fun P P′}
    → (∀ (x : A (pos P)) → (g (mon f)) x ≡ (g (mon f′)) x)
      -----------------------
    → f ≡ f′

postulate
  dependent-function-extensionality : {I : Set} {D : I → Set} {p p′ : (i : I) → (D i) }
    → (∀ (i : I) → p i ≡ p′ i)
    → p ≡ p′
                       
flat-domain : Set → domain
flat-domain-pos : Set → poset

data B⊥ (B : Set) : Set where
  ⊥₁ : B⊥ B
  inj : B → B⊥ B

data _≼_ : ∀ {B} → B⊥ B → B⊥ B → Set where
  z≼n : ∀ {B} → {b : B⊥ B}
    → ⊥₁ ≼ b
  x≼x : ∀ {B} → {b : B⊥ B}
    → b ≼ b

antisym-≼ : ∀ {B} → {b₁ b₂ : B⊥ B}
        → b₁ ≼ b₂
        → b₂ ≼ b₁
        → b₁ ≡ b₂ 
antisym-≼ z≼n z≼n = Eq.refl
antisym-≼ z≼n x≼x = Eq.refl
antisym-≼ x≼x b₂≼b₁ = Eq.refl

trans-≼ : ∀ {B} → {b₁ b₂ b₃ : B⊥ B}
      → b₁ ≼ b₂
      → b₂ ≼ b₃
      → b₁ ≼ b₃

trans-≼ z≼n _ = z≼n
trans-≼ x≼x b₁≼b₃ = b₁≼b₃

flat-domain-pos B = record
                      { A = B⊥ B
                      ; R = _≼_ {B}
                      ; reflexive = x≼x
                      ; antisymmetric = antisym-≼
                      ; transitive = trans-≼
                      } 

record eventually-constant {P : poset} (c : chain P) : Set where
  field
    index : ℕ
    eventual-val : A P
    eventually-val : {m : ℕ} → index ≤ m → g c m ≡ eventual-val
open eventually-constant

constant-UP : {P : poset} {c : chain P} (ev-const ev-const′ : eventually-constant c) → eventual-val ev-const ≡ eventual-val ev-const′
constant-UP ev-const ev-const′ = Eq.trans
                                   (Eq.sym (eventually-val ev-const {max (index ev-const) (index ev-const′)} (a≤max-a-b (index ev-const))))
                                   (eventually-val ev-const′ (b≤max-a-b {index ev-const} (index ev-const′)))

constant-UP-useful : {P : poset} {c : chain P} {ev-const : eventually-constant c} {eventual-val′ : A P} {index′ : ℕ} → ({m : ℕ} → index′ ≤ m → g c m ≡ eventual-val′) → eventual-val′ ≡ (eventual-val ev-const)

constant-UP-useful {ev-const = ev-const} {eventual-val′} {index′} eventually-val′ = constant-UP (record
  { index = index′
  ; eventual-val = eventual-val′
  ; eventually-val = eventually-val′
  }
  ) ev-const


postulate flat-domain-chain-eventually-constant : ∀ {B} → (c : chain (flat-domain-pos B)) → eventually-constant c
chain-complete-flat-domain : {A : Set} → (c : chain (flat-domain-pos A)) → lub c
⊔ (chain-complete-flat-domain c) = eventual-val (flat-domain-chain-eventually-constant c)

lub1 (chain-complete-flat-domain {A} c) {n} with ≤-dichotomy {n} {index (flat-domain-chain-eventually-constant c)}
...                                     | inj₁ n≤index = a≤b≡c→a≤c′
                                                           {B⊥ A} {R (flat-domain-pos A)}
                                                           (mon c n≤index)
                                                           (eventually-val (flat-domain-chain-eventually-constant c) (refl-≤))
...                                     | inj₂ index≤n = a≡b→a≤b
                                                           {flat-domain-pos A}
                                                           (eventually-val (flat-domain-chain-eventually-constant c) index≤n)

lub2 (chain-complete-flat-domain {A} c) {d′} x = a≡b≤c→a≤c
                                                   {B⊥ A}
                                                   {R (flat-domain-pos A)}
                                                   {eventual-val (flat-domain-chain-eventually-constant c)}
                                                   {g c (index (flat-domain-chain-eventually-constant c))} {d′}
                                                   (Eq.sym (eventually-val (flat-domain-chain-eventually-constant c) refl-≤))
                                                   x

flat-domain A = record { pos = flat-domain-pos A
                       ; chain-complete = chain-complete-flat-domain {A}
                       ; bottom = record { ⊥ = ⊥₁
                                         ; ⊥-is-bottom = z≼n
                                         }
                       }


chain-map-preserves-constancy : {P₁ P₂ : poset} →  {c : chain P₁} → (c′ : eventually-constant c) → (f : monotone-fun P₁ P₂) → eventually-constant (chain-map c f)

chain-map-preserves-constancy c′ f = record
                                  { index = index c′
                                  ; eventual-val = g f (eventual-val c′)
                                  ; eventually-val = λ {m} index≤m → cong (g f) (eventually-val c′ index≤m)
                                  }

tarski-fix : ∀ (P : domain) →  (cont-fun : cont-fun P P) → least-pre-fixed (pos P) (g (mon cont-fun))

tarski-fⁿ⊥ : ∀ (P : domain) (f : A (pos P) → A (pos P)) → ℕ → A (pos P)

tarski-fⁿ⊥ P f n = iterate n f (⊥ (bottom P))

tarski-fⁿ⊥⊑fⁿ⁺¹⊥ : (P : domain) (cont-fun : cont-fun P P) → {a a′ : ℕ} → a ≤ a′ → (R (pos P)) ((tarski-fⁿ⊥ P (g (mon cont-fun))) a) ((tarski-fⁿ⊥ P (g (mon cont-fun))) a′)
 
tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun _≤_.z≤n = ⊥-is-bottom (bottom P)
tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun (_≤_.s≤s m≤n) = (mon (mon cont-fun)) (tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun m≤n)


tarski-fⁿ⊥-mon : (P : domain) (cont-fun : cont-fun P P) → monotone-fun nats (pos P)

tarski-fⁿ⊥-mon P cont-fun = record { g = tarski-fⁿ⊥ P (g (mon cont-fun))
                                   ; mon = λ a≤a′ → tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun a≤a′
                                   }

tarski-chain-of-fⁿ⊥ : (P : domain) (cont-fun : cont-fun P P) → chain (pos P)

tarski-chain-of-fⁿ⊥ P cont-fun = tarski-fⁿ⊥-mon P cont-fun

tarski-lfp1 :
  ∀ (P : domain) (cont-fun : cont-fun P P)
  → let ⋃ = (chain-complete P) in
    let fⁿ⊥ = (tarski-chain-of-fⁿ⊥ P cont-fun) in
    (g (mon cont-fun)) (⊔ (⋃ fⁿ⊥)) ≡ ⊔ (⋃ fⁿ⊥)


lubs-shift-invariant :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → g c n ≡ g c′ (k + n)) →
    let ⋃ = (chain-complete P) in
      ⊔ (⋃ c) ≡ ⊔ (⋃ c′)


lubs-shift-invariant-1 :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → g c n ≡ g c′ (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in 
    ⊔ (⋃ c) ⊑ ⊔ (⋃ c′)


lubs-shift-invariant-2 :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → g c n ≡ g c′ (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in
    ⊔ (⋃ c′) ⊑ ⊔ (⋃ c)


lubs-shift-invariant-1 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c) (λ {n} → a≡b≤c→a≤c {_⊑_ = R (pos P)} (x {n}) (lub1 (⋃ c′) {k + n}))

lubs-shift-invariant-2 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c′) λ {n} → a≤b≡c≤d→a≤d (pos P) (mon c′ (n≤k+n n k)) (x {n}) (lub1 (⋃ c))

lubs-shift-invariant P c c′ k x =
  let ⋃c⊑⋃c′ = (lubs-shift-invariant-1 P c c′ k x) in
  let ⋃c′⊑⋃c = (lubs-shift-invariant-2 P c c′ k x) in
    (antisymmetric (pos P)) ⋃c⊑⋃c′ ⋃c′⊑⋃c  

tarski-lfp1 P cont-fun =
  let ⋃ = (chain-complete P) in
  let f = (g (mon cont-fun)) in
  let fⁿ⊥ = (tarski-chain-of-fⁿ⊥ P cont-fun) in
  let ffⁿ⊥ = (chain-map (fⁿ⊥) (mon cont-fun)) in
  let ⊔fⁿ⊥ = (⊔ (⋃ fⁿ⊥)) in
  let ⊔ffⁿ⊥ = (⊔ (⋃ ffⁿ⊥)) in
    begin
      f(⊔fⁿ⊥)
    ≡⟨ lub-preserve cont-fun fⁿ⊥ ⟩
      ⊔ffⁿ⊥
    ≡⟨ lubs-shift-invariant P (ffⁿ⊥) (fⁿ⊥) 1 (λ {n} → Eq.refl) ⟩
      ⊔fⁿ⊥
    ∎

tarski-lfp2 :
  ∀ (P : domain) (mon-f : monotone-fun (pos P) (pos P)) (d : A (pos P))
    → (R (pos P)) ((g mon-f) d) d
    → (n : ℕ)
    → (R (pos P)) (iterate n (g mon-f) (⊥ (bottom P))) d

tarski-lfp2 P mon-f d fd⊑d zero = ⊥-is-bottom (bottom P)
tarski-lfp2 P mon-f d fd⊑d (suc n) = transitive (pos P) (mon mon-f (tarski-lfp2 P mon-f d fd⊑d n)) fd⊑d

tarski-fix P cont-fun =
  let ⋃ = (chain-complete P) in
  let fⁿ⊥ = (tarski-chain-of-fⁿ⊥ P cont-fun) in
    record { lfp1 = record { d = ⊔ (⋃ fⁿ⊥)
                           ; pre-fix = a≡b→a≤b {pos P} (tarski-lfp1 P cont-fun)
                           }
           ; lfp2 = λ {d} fd⊑d → lub2 (⋃ fⁿ⊥) {d} λ {n} → tarski-lfp2 P (mon (cont-fun)) d fd⊑d n
           }

------------------------------------------------------------------------------------------------------------------------------------------------------------

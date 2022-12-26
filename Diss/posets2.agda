module posets2 where
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_)

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Product

refl-≤ : ∀ {n : ℕ} → n ≤ n
antisym-≤ : ∀ {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
trans-≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

refl-≤ {zero} = _≤_.z≤n
refl-≤ {suc n} = _≤_.s≤s (refl-≤ {n})

antisym-≤ _≤_.z≤n _≤_.z≤n = Eq.refl
antisym-≤ (_≤_.s≤s n≤m) (_≤_.s≤s m≤n) = Eq.cong suc (antisym-≤ n≤m m≤n)

trans-≤ _≤_.z≤n _≤_.z≤n = _≤_.z≤n
trans-≤ _≤_.z≤n (_≤_.s≤s n≤p) = _≤_.z≤n
trans-≤ (_≤_.s≤s m≤n) (_≤_.s≤s n≤p) = _≤_.s≤s (trans-≤ m≤n n≤p)

record poset2 : Set₁ where
  field
    A : Set
    R : A → A → Set
    reflexive     : ∀ {a : A} → R a a 
    antisymmetric : ∀ {a b : A} → (R a b) → (R b a) → a ≡ b
    transitive    : ∀ {a b c : A} → (R a b) → (R b c) → (R a c)
open poset2

nats2 : poset2
nats2 = record
          { R = _≤_
          ; reflexive = refl-≤
          ; antisymmetric = antisym-≤
          ; transitive = trans-≤ }

iterate : {D : Set} (n : ℕ) → (D → D) → (D → D)
iterate 0 f d = d 
iterate (suc n) f d = f ((iterate n f) d) 

record monotone-fun-2 (P≤ : poset2) (Q≤ : poset2) : Set where
  field
    g : A P≤ → A Q≤
    mon : ∀ {a a′ : A P≤} → (R P≤) a a′ → (R Q≤) (g a) (g a′)
open monotone-fun-2
        
record chain-2 (P≤ : poset2) : Set where
  field
    monotone : monotone-fun-2 nats2 P≤
open monotone-fun-2

record lub-2 {P≤ : poset2} (c : chain-2 P≤) : Set where
  P : Set
  P = (A P≤)
  _⊑_ : P → P → Set
  _⊑_ = R (P≤)
  f : ℕ → P
  f = g (chain-2.monotone c)
  field
    ⊔ : P
    lub1 : ∀ {n : ℕ} → f n ⊑ ⊔
    lub2 : ∀ {d′ : P} → (∀ {n : ℕ} → f n ⊑ d′) → ⊔ ⊑ d′
open lub-2


chain-map-2 : ∀ (P≤ : poset2) (Q≤ : poset2) (chain-P : chain-2 P≤) → (monotone-fun-2 P≤ Q≤) → (chain-2 Q≤) 

chain-map-2 P≤ Q≤ chain-P monotone-f = record { monotone =
                                              record { g = λ n → g monotone-f (g (chain-2.monotone chain-P) n)
                                                     ; mon = λ a≤a′ → mon monotone-f (mon (chain-2.monotone chain-P) a≤a′)
                                                     }
                                              }

record continuous-fun-2 (P≤ : poset2) (Q≤ : poset2) : Set where
  field
    mon : monotone-fun-2 P≤ Q≤ 
    lub-preserve : ∀ (c : chain-2 P≤) (⋃₁ : lub-2 c) (⋃₂ : lub-2 (chain-map-2 P≤ Q≤ c mon)) → (g mon) (⊔ ⋃₁) ≡ ⊔ ⋃₂
open continuous-fun-2

record least-element-2 (P≤ : poset2) : Set where
  field
    ⊥ : A P≤
    ⊥-is-bottom : ∀ {a : A P≤} → (R P≤) ⊥ a
open least-element-2

record domain-2 : Set₁ where
  field
    pos : poset2
    chain-complete : ∀ (c : chain-2 pos) → lub-2 c
    bottom : least-element-2 pos
open domain-2


record pre-fixed-2 (P≤ : poset2) (f : A P≤ → A P≤) : Set where
  field
    d : A P≤
    pre-fix : (R P≤) (f d) d
open pre-fixed-2

record least-pre-fixed-2 (P≤ : poset2) (f : A P≤ → A P≤) : Set where
  field
    lfp1 : pre-fixed-2 P≤ f
    lfp2 : ∀ {d′ : A P≤} → (R P≤) (f d′) d′ → (R P≤) (d lfp1) d′
open least-pre-fixed-2

tarski-2 : ∀ (P : domain-2) (cont-fun : continuous-fun-2 (pos P) (pos P)) → least-pre-fixed-2 (domain-2.pos P) (g (mon cont-fun))

tarski-chain-fun-2 : ∀ (P : domain-2) (f : A (pos P) → A (pos P)) → ℕ → A (pos P)

tarski-chain-fun-2 P f n = iterate n f (⊥ (bottom P))

tarski-chain-fun-monotonic-2 : (P : domain-2) (cont-fun : continuous-fun-2 (pos P) (pos P)) → {a a′ : ℕ} → a ≤ a′ → (R (pos P)) ((tarski-chain-fun-2 P (g (mon cont-fun))) a) ((tarski-chain-fun-2 P (g (mon cont-fun))) a′)
 
tarski-chain-fun-monotonic-2 P cont-fun _≤_.z≤n = ⊥-is-bottom (bottom P)
tarski-chain-fun-monotonic-2 P cont-fun (_≤_.s≤s m≤n) = {!(mon (mon cont-fun)) (tarski-chain-fun-monotonic-2 P cont-fun m≤n)!}

tarski-chain-fun-mon-2 : (P : domain-2) (cont-fun : continuous-fun-2 (pos P) (pos P)) → monotone-fun-2 nats2 (pos P)

tarski-chain-fun-mon-2 P cont-fun =  record { g = tarski-chain-fun-2 P (g (mon cont-fun))
                                            ; mon = λ a≤a′ → tarski-chain-fun-monotonic-2 P cont-fun a≤a′
                                            }


tarski-chain-2 : (P : domain-2) (cont-fun : continuous-fun-2 (pos P) (pos P)) → chain-2 (pos P)

tarski-chain-2 P cont-fun = record { monotone = tarski-chain-fun-mon-2 P cont-fun }

tarski-lfp-1-2 :
  ∀ (P : domain-2) (cont-fun : continuous-fun-2 (pos P) (pos P))
  → let ⋃ = (chain-complete P) in
    let fⁿ⊥ = (tarski-chain-2 P cont-fun) in
    (g (mon cont-fun)) (⊔ (⋃ fⁿ⊥)) ≡ ⊔ (⋃ fⁿ⊥)


lubs-shift-invariant :
  ∀ (P : domain-2) (c c′ : chain-2 (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (chain-2.monotone c)) n ≡ (g (chain-2.monotone c′)) (k + n)) → let ⋃ = (chain-complete P) in ⊔ (⋃ c) ≡ ⊔ (⋃ c′)


lubs-shift-invariant-1-2 :
  ∀ (P : domain-2) (c c′ : chain-2 (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (chain-2.monotone c)) n ≡ (g (chain-2.monotone c′)) (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in 
    ⊔ (⋃ c) ⊑ ⊔ (⋃ c′)


lubs-shift-invariant-2-2 :
  ∀ (P : domain-2) (c c′ : chain-2 (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (chain-2.monotone c)) n ≡ (g (chain-2.monotone c′)) (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in
    ⊔ (⋃ c′) ⊑ ⊔ (⋃ c)

a≡b≤c→a≤c : ∀ {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ≡ b → b ⊑ c → a ⊑ c

a≡b≤c→a≤c Eq.refl b≤c = b≤c

lubs-shift-invariant-1-2 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c) (λ {n} → a≡b≤c→a≤c {_⊑_ = R (pos P)} (x {n}) (lub1 (⋃ c′) {k + n}))

n≤sucn : ∀ (n : ℕ) → n ≤ suc n
n≤sucn zero = _≤_.z≤n
n≤sucn (suc n) = _≤_.s≤s (n≤sucn n)

n≤k+n : ∀ (n k : ℕ) → n ≤ k + n
n≤k+n zero _ = _≤_.z≤n
n≤k+n (suc n) zero = _≤_.s≤s (n≤k+n n zero)
n≤k+n (suc n) (suc k) = _≤_.s≤s (trans-≤ (n≤sucn n) (n≤k+n (suc n) k))


a≤b≡c≤d→a≤d : ∀ (P : poset2) {a b c d : (A P)} → (R P) a b → c ≡ b → (R P) c d → (R P) a d
a≤b≡c≤d→a≤d P a⊑b Eq.refl c⊑d = (transitive P) a⊑b c⊑d


lubs-shift-invariant-2-2 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c′) λ {n} → a≤b≡c≤d→a≤d (pos P) (mon (chain-2.monotone c′) (n≤k+n n k)) (x {n}) (lub1 (⋃ c))

lubs-shift-invariant P c c′ k x =
  let ⋃c⊑⋃c′ = (lubs-shift-invariant-1-2 P c c′ k x) in
  let ⋃c′⊑⋃c = (lubs-shift-invariant-2-2 P c c′ k x) in
    (antisymmetric (pos P)) ⋃c⊑⋃c′ ⋃c′⊑⋃c  

tarski-lfp-1-2 P cont-fun =
  let ⋃ = (chain-complete P) in
  let fⁿ⊥ = (tarski-chain-2 P cont-fun) in
  let ffⁿ⊥ = (chain-map-2 (pos P) (pos P) (fⁿ⊥) (mon cont-fun)) in
  let ⊔fⁿ⊥ = (⊔ (⋃ fⁿ⊥)) in
  let ⊔ffⁿ⊥ = (⊔ (⋃ ffⁿ⊥)) in
    begin
      (g (mon cont-fun)) ⊔fⁿ⊥
--    ≡⟨ (lub-preserve cont-fun) (fⁿ⊥) (⋃ (fⁿ⊥)) (⋃ ffⁿ⊥) ⟩ 
    ≡⟨ lub-preserve cont-fun fⁿ⊥ (⋃ fⁿ⊥) (⋃ ffⁿ⊥) ⟩ 
      ⊔ffⁿ⊥
--    ≡⟨(lubs-shift-invariant P (ffⁿ⊥) (fⁿ⊥) 1 Eq.refl) ⟩
    ≡⟨ lubs-shift-invariant P (ffⁿ⊥) (fⁿ⊥) 1 {!λ {n} → Eq.refl!} ⟩
      ⊔fⁿ⊥
    ∎

tarski-lfp2-2 :
  ∀ (P : domain-2) (mon-f : monotone-fun-2 (pos P) (pos P)) (d : A (pos P))
    → (R (pos P)) ((g mon-f) d) d
    → (n : ℕ)
    → (R (pos P)) (iterate n (g mon-f) (⊥ (bottom P))) d

tarski-lfp2-2 P mon-f d fd⊑d zero = ⊥-is-bottom (bottom P)
tarski-lfp2-2 P mon-f d fd⊑d (suc n) = transitive (pos P) (mon mon-f (tarski-lfp2-2 P mon-f d fd⊑d n)) fd⊑d


≡→⊑ : ∀ (P : poset2) {a b : (A P)} → (a ≡ b) → ((R P) a b)
≡→⊑ P Eq.refl = reflexive P


tarski-2 P cont-fun =
  let ⋃ = (chain-complete P) in
  let fⁿ⊥ = (tarski-chain-2 P cont-fun) in
    record { lfp1 = record
                           { d = ⊔ (⋃ fⁿ⊥)
                           ; pre-fix = ≡→⊑ (pos P) (tarski-lfp-1-2 P cont-fun)
                           }
             ; lfp2 = {!!}
--            ; lfp2 = λ {d} fd⊑d → lub2 (⋃ fⁿ⊥) {d} λ {n} → {!!}
--
            }


--lfp2 = λ {d} fd⊑d → lub2 (⋃ fⁿ⊥) {d} (λ {n} → (tarski-lfp2 P′ f (mon cont-fun) d fd⊑d) n)



function-domain : (P : domain-2) (P′ : domain-2) → domain-2

function-⊑ : (P : domain-2) (P′ : domain-2) (f : continuous-fun-2 (pos P) (pos P′)) → (f′ : continuous-fun-2 (pos P) (pos P′)) → Set

function-⊑ P P′ f f′ = ∀ {x : A (pos P)} → (R (pos P′)) ((g (mon f)) x) ((g (mon f′)) x)

function-⊑-antisymmetry : (P : domain-2) (P′ : domain-2) (f : continuous-fun-2 (pos P) (pos P′)) (f′ : continuous-fun-2 (pos P) (pos P′)) → function-⊑ P P′ f f′ → function-⊑ P P′ f′ f → f ≡ f′

function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f = {!!}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

function-domain P  P′ = record { pos = record
                                              { A = continuous-fun-2 (pos P) (pos P′)
                                              ; R = function-⊑ P P′
                                              ; reflexive = λ {a} {x} → reflexive (pos P′)
                                              ; antisymmetric = λ {f} {f′} f⊑f′ f′⊑f → function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f
                                              ; transitive = λ {a} {b} {c} f⊑f′ f′⊑f″ → λ {x} → transitive (pos P′) (f⊑f′ {x}) (f′⊑f″ {x})
                                              }
                               ; chain-complete = λ c → record { ⊔ = record
                                                                            { mon = record
                                                                                           { g = let ⋃ = (chain-complete P′) in
                                                                                             λ d → {!!}
                                                                                           ; mon = {!!}
                                                                                           }
                                                                            ; lub-preserve = {!!}
                                                                            }
                                                               ; lub1 = {!!}
                                                               ; lub2 = {!!}
                                                               }
                               ; bottom = record
                                                 { ⊥ = record
                                                              { mon = record
                                                                             { g = λ x → ⊥ (bottom P′)
                                                                             ; mon = λ a≤a′ → ≡→⊑ ((pos P′)) Eq.refl
                                                                             }
                                                              ; lub-preserve = λ c ⋃₁ ⋃₂ → {!!}
                                                              }
                                                 ; ⊥-is-bottom = {!!}
                                                 }
                               }

tarski-continuous : ∀ (P : domain-2) → continuous-fun-2 (pos P) (pos P) → continuous-fun-2 (pos (function-domain P P)) (pos P)


tarski-mon : ∀ (P : domain-2) → continuous-fun-2 (pos P) (pos P) → monotone-fun-2 (pos (function-domain P P)) (pos P)

tarski-lub-preserve : ∀ (P : domain-2) → (cont-fun : continuous-fun-2 (pos P) (pos P)) → (c : chain-2 (pos (function-domain P P))) → (⋃₁ : lub-2 c) → (⋃₂ : lub-2 (chain-map-2 (pos (function-domain P P)) (pos P) c (tarski-mon P cont-fun))) → g (tarski-mon P cont-fun) (⊔ ⋃₁) ≡ ⊔ ⋃₂ 

fix-f′-is-pre-fixed : ∀ (P : domain-2) → (f : continuous-fun-2 (pos P) (pos P)) → (f′ : continuous-fun-2 (pos P) (pos P)) → (f⊑f′ : function-⊑ P P f f′) → R (pos P) (g (mon f) (⊔ (chain-complete P (tarski-chain-2 P f′)))) (⊔ (chain-complete P (tarski-chain-2 P f′)))

fix-f′-is-pre-fixed P f f′ f⊑f′ = transitive (pos P) (f⊑f′ {d (lfp1 (tarski-2 P f′))}) (pre-fix (lfp1 (tarski-2 P f′)))


tarski-mon P cont-fun = record { g = λ (cont-fun : continuous-fun-2 (pos P) (pos P)) → d (lfp1 (tarski-2 P cont-fun))
                               ; mon = λ {f} {f′} f⊑f′ → lfp2 (tarski-2 P f) (fix-f′-is-pre-fixed P f f′ f⊑f′)
                               }

tarski-lub-preserve P₁ cont-fun c ⋃₁ ⋃₂ = {!!}


tarski-continuous P cont-fun = record { mon = tarski-mon P cont-fun
                                      ; lub-preserve = tarski-lub-preserve P cont-fun
                                      }

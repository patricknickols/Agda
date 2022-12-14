module posets where
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_)

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Product

record poset (A : Set) (⊑ : A → A → Set) : Set where
  field
    reflexive     : ∀ {a : A} → ⊑ a a 
    antisymmetric : ∀ {a b : A} → (⊑ a b) → (⊑ b a) → a ≡ b
    transitive    : ∀ {a b c : A} → (⊑ a b) → (⊑ b c) → (⊑ a c)
open poset

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

nats : poset (ℕ) (Data.Nat._≤_)
nats = record { reflexive = refl-≤
              ; antisymmetric = antisym-≤ 
              ; transitive = trans-≤ 
              }

record monotone {A B : Set} {_⊑₁_ : A → A → Set} {_⊑₂_ : B → B → Set} (P₁ : poset A _⊑₁_) (P₂ : poset B _⊑₂_) : Set where
  field
    mon-fun : A → B
    mon : ∀ {a a′ : A} → a ⊑₁ a′ → (mon-fun a) ⊑₂ (mon-fun a′)
open monotone

record monotone-fun {A B : Set} {_⊑₁_ : A → A → Set} {_⊑₂_ : B → B → Set} (P₁ : poset A _⊑₁_) (P₂ : poset B _⊑₂_) (f : A → B) : Set where
  field
    mon : ∀ {a a′ : A} → a ⊑₁ a′ → (f a) ⊑₂ (f a′)
open monotone-fun

mon-succ : monotone nats nats

mon-succ = record { mon-fun = suc
                  ; mon = _≤_.s≤s
                  }

record least-element {A : Set} {_⊑_ : A → A → Set} (P : poset A _⊑_)  (⊥ : A) : Set where
  field
    ⊥-is-bottom : ∀ {a : A} → ⊥ ⊑ a
open least-element

zero-least : least-element nats (0)
zero-least = record {⊥-is-bottom = _≤_.z≤n
                    }

record pre-fixed {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (f : D → D) (d : D) : Set where
  field
    pre-fix : (f d) ⊑ d
open pre-fixed

unique-least : {A : Set} → {_⊑_ : A → A → Set} → (P : poset A _⊑_) → (a : A) → (a′ : A) → least-element P a → least-element P a′ → a ≡ a′
unique-least P a a′ least-a least-a′ = antisymmetric P (⊥-is-bottom least-a) (⊥-is-bottom least-a′)


record least-pre-fixed {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (f : D → D) : Set where
  field
    fixf : D
    lfp1 : pre-fixed P f fixf
    lfp2 : ∀ {d : D} → (f d) ⊑ d → fixf ⊑ d
open least-pre-fixed


least-pre-fixed-is-fixed : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {f : D → D} (x : least-pre-fixed P f) (mon-f : monotone-fun P P f) → f (fixf x) ≡ fixf x 

least-pre-fixed-is-fixed {P = P} x mon-f = (antisymmetric P) (pre-fix (lfp1 x)) ((lfp2 x) ((mon mon-f) (pre-fix (lfp1 x))))

record chain {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) : Set where
  field
    chain-fun : ℕ → D
    mon : monotone-fun nats P chain-fun
open chain

record lub {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (c : chain P) : Set where
  field
    lub-element : D
    lub1 : ∀ {n : ℕ} →  (chain-fun c) n ⊑ lub-element
    lub2 : ∀ {d′ : D} → ((∀ {n : ℕ} → (chain-fun c) n ⊑ d′) → lub-element ⊑ d′)
open lub

chain-map : ∀ {A B : Set} {_⊑_ : A → A → Set} {P : poset A _⊑_ } {_⊑_′ : B → B → Set} {P′ : poset B _⊑_′} (chain-A : chain P) → (f : A → B) → (monotone-fun P P′ f) → (chain P′) 

chain-map chain-A f mon-f = record { chain-fun = λ n → f ((chain-fun chain-A) n)
                             ; mon = record { mon = λ a≤a′ → (mon mon-f) ((mon (mon chain-A)) a≤a′) }
                             }

lub-from-chain : {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (c : chain P) → lub c

least-pre-fixed-of : {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (f : D → D) → least-pre-fixed P f 

record continuous-fun {A B : Set} {_⊑₁_ : A → A → Set} {_⊑₂_ : B → B → Set} (P₁ : poset A _⊑₁_) (P₂ : poset B _⊑₂_) (f : A → B) : Set where
  field
    mon : monotone-fun P₁ P₂ f
    lub-preserve : ∀ (c : chain P₁) (⋃₁ : lub c) (⋃₂ : lub (chain-map c f mon)) → f (lub-element ⋃₁) ≡ lub-element ⋃₂
open continuous-fun

--least-pre-fixed-is-cont : ∀ {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (P′ : poset (P → P)  → continuous-fun (least-pre-fixed-of () P)

record cpo {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) : Set where
  field
    chain-complete : ∀ (c : chain P) → lub c 
open cpo

record domain {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (⊥ : D) : Set where
  field
    chain-complete : ∀ (c : chain P) → lub c
    bottom : least-element P ⊥
open domain

record const-chain {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) : Set where
  field
    carrier-chain : chain P
    const-value : D
    constant : ∀ (n : ℕ) → chain-fun carrier-chain n ≡ const-value
open const-chain
  
const-chain-has-lub : ∀ {D : Set} {_⊑_ : D → D → Set} {f : ℕ → D} (P : poset D _⊑_) (x : const-chain P) → lub (carrier-chain x)

equality-implies-relation : ∀ {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (d d′ : D) → d ≡ d′ → d ⊑ d′ 

equality-implies-relation p d d′ Eq.refl = (reflexive p) {d}

aRb∧a≡c-implies-cRb : ∀ {D : Set} {_⊑_ : D → D → Set} (a b c : D) → a ⊑ b → a ≡ c → c ⊑ b
aRb∧a≡c-implies-cRb a b c a⊑b Eq.refl = a⊑b

--const-chain-has-lub-lemma-1 : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {c : chain P} (const-c : const-chain P c) → {n : ℕ} → (f c) n ⊑ const-value


--const-chain-has-lub-lemma-2 : {d′ : D} → ({n : ℕ} → f n ⊑ d′) → const-value ⊑ d′


--const-chain-has-lub P chain = record { lub-element = const-value chain
--                                     ; lub1 = λ {n} → equality-implies-relation P (chain-fun (carrier-chain chain) n ) (const-value chain) (constant chain n)
--                                     ; lub2 = λ {d′} x → aRb∧a≡c-implies-cRb (const-value chain) d′ (const-value chain)
--                                     ((aRb∧a≡c-implies-cRb ((chain-fun (carrier-chain chain)) 0) d′ (const-value chain) (x {0})))
--                                     Eq.refl
--                                 }

a≡b≤c→a≤c : ∀ {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ≡ b → b ⊑ c → a ⊑ c

a≡b≤c→a≤c Eq.refl b≤c = b≤c

lubs-shift-invariant : ∀ {D : Set} {_⊑_ : D → D → Set}  {P : poset D _⊑_} {⊥ : D} {P′ : domain P ⊥}  (c c′ : chain P) → (k : ℕ) → (∀ {n : ℕ} → (chain-fun c) n ≡ (chain-fun c′) (k + n)) → lub-element (((lub-from-chain)) c) ≡ lub-element (((lub-from-chain)) c′)


--(antisymmetric P) (lub2 (lub-of-chain c) λ {n} → a≡b≤c→a≤c {_⊑_ = _⊑_} (x {n}) ((lub1 (lub-of-chain c′)) {k + n})) ((lub2 (lub-of-chain c′) λ {n} → a≡b≤c→a≤c {_⊑_ = _⊑_} (x {n}) ((lub1 (lub-of-chain c)) {k + n})))

lubs-shift-invariant-1 : ∀ {D : Set} {_⊑_ : D → D → Set}  {P : poset D _⊑_} {⊥ : D} {P′ : domain P ⊥} (c c′ : chain P) → (k : ℕ) → (∀ {n : ℕ} → (chain-fun c) n ≡ (chain-fun c′) (k + n)) → lub-element (((lub-from-chain)) c) ⊑ lub-element (((lub-from-chain)) c′)

lubs-shift-invariant-2 : ∀ {D : Set} {_⊑_ : D → D → Set}  {P : poset D _⊑_} {⊥ : D} {P′ : domain P ⊥} (c c′ : chain P) → (k : ℕ) → (∀ {n : ℕ} → (chain-fun c) n ≡ (chain-fun c′) (k + n)) → lub-element (((lub-from-chain)) c′) ⊑ lub-element (((lub-from-chain)) c)


lubs-shift-invariant-1 {_⊑_ = ≤} {P′ = P′} c c′ k x = lub2 (((lub-from-chain)) c) (λ {n} → a≡b≤c→a≤c {_⊑_ = ≤} (x {n}) (lub1 (((lub-from-chain)) c′) {k + n}))


n≤n+k : ∀ (n k : ℕ) → n ≤ k + n
--FILL OUT


a≤b≡c≤d→a≤d : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {a b c d : D} → a ⊑ b → c ≡ b → c ⊑ d → a ⊑ d
a≤b≡c≤d→a≤d {P = P} a⊑b Eq.refl c⊑d = (transitive P) a⊑b c⊑d


lubs-shift-invariant-2 {_⊑_ = ≤} {P = P} {P′ = P′} c c′ k x = lub2 (((lub-from-chain)) c′) λ {n} → a≤b≡c≤d→a≤d {_⊑_ = ≤} {P = P} (mon (mon c′) (n≤n+k (n) (k))) (x {n}) (lub1 (((lub-from-chain)) c)) 

lubs-shift-invariant {_⊑_ = _⊑_} {P = P} {⊥ = ⊥} {P′ = P′} c c′ k x = (antisymmetric P) (lubs-shift-invariant-1 {⊥ = ⊥} {P′ = P′} c c′ k x) (lubs-shift-invariant-2 {⊥ = ⊥} {P′ = P′} c c′ k x)  




tarski : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (⊥ : D) (P′ : domain P ⊥) (f : D → D) (cont-fun : continuous-fun P P f) → least-pre-fixed P f

tarski-chain-fun : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (⊥ : D) (f : D → D) (P′ : domain P ⊥) → ℕ → D

iterate : {D : Set} (n : ℕ) → (D → D) → (D → D)
iterate 0 f d = d 
iterate (suc n) f d = f ((iterate n f) d) 

tarski-chain-fun ⊥ f P′ n = iterate n f ⊥  

tarski-chain-fun-mon : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (⊥ : D) (f : D → D) (P′ : domain P ⊥) (cont-fun : continuous-fun P P f) → monotone-fun nats P (tarski-chain-fun ⊥ f P′)


tarski-chain-fun-monotonic : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (⊥ : D) (f : D → D) (P′ : domain P ⊥) (cont-fun : continuous-fun P P f) → {a a′ : ℕ} → a ≤ a′ → (tarski-chain-fun ⊥ f P′) a ⊑ (tarski-chain-fun ⊥ f P′) a′
 
tarski-chain-fun-monotonic ⊥ f P′ cont-fun _≤_.z≤n = ⊥-is-bottom (bottom P′)
tarski-chain-fun-monotonic ⊥ f P′ cont-fun (_≤_.s≤s m≤n) = mon (mon cont-fun) (tarski-chain-fun-monotonic ⊥ f P′ cont-fun m≤n)

tarski-chain-fun-mon ⊥ f P′ cont-fun = record { mon = λ a≤a′ → tarski-chain-fun-monotonic ⊥ f P′ cont-fun a≤a′ }

tarski-chain : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} (⊥ : D) (f : D → D) (P′ : domain P ⊥) (cont-fun : continuous-fun P P f) → chain P

tarski-chain ⊥ f P′ cont-fun = record { chain-fun = tarski-chain-fun ⊥ f P′
                                      ; mon = tarski-chain-fun-mon ⊥ f P′ cont-fun
                                      }



tarski-lfp-1 : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {⊥ : D} {P′ : domain P ⊥} (f : D → D) (cont-fun : continuous-fun P P f) → f (lub-element (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun))) ≡ lub-element (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun))

tarski-lfp-1 {⊥ = ⊥} {P′ = P′} f cont-fun =
  begin
    f (lub-element (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun)))
  ≡⟨ (lub-preserve cont-fun) (tarski-chain ⊥ f P′ cont-fun) (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun)) (((lub-from-chain)) (chain-map (tarski-chain ⊥ f P′ cont-fun) f (mon cont-fun))) ⟩ 
    lub-element (((lub-from-chain)) (chain-map (tarski-chain ⊥ f P′ cont-fun) f (mon cont-fun)))
  ≡⟨(lubs-shift-invariant {⊥ = ⊥} {P′ = P′} (chain-map (tarski-chain ⊥ f P′ cont-fun) f (mon cont-fun)) (tarski-chain ⊥ f P′ cont-fun) 1 Eq.refl) ⟩
  lub-element (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun))
  ∎

tarski-lfp2 : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {⊥ : D} (P′ : domain P ⊥) (f : D → D) (mon-f : monotone-fun P P f) → (d : D) → f d ⊑ d → (n : ℕ) → (iterate n f) ⊥ ⊑ d

tarski-lfp2 P′ f mon-f d fd⊑d zero = ⊥-is-bottom (bottom P′) 
tarski-lfp2 {P = P} P′ f mon-f d fd⊑d (suc n) = transitive P ((mon mon-f) (tarski-lfp2 P′ f mon-f d fd⊑d n)) (fd⊑d)

≡→⊑ : ∀ {D : Set} {_⊑_ : D → D → Set} {P : poset D _⊑_} {a b : D} → (a ≡ b) → (a ⊑ b)
≡→⊑ {P = P} {a = a} {b = a} Eq.refl = reflexive P


tarski {_⊑_ = ≤} {P = P} ⊥ P′ f cont-fun = record { fixf = lub-element (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun))
                                ; lfp1 = record { pre-fix =  ≡→⊑ {_⊑_ = ≤} {P = P} (tarski-lfp-1 {⊥ = ⊥} {P′ = P′} f cont-fun) }
                                ; lfp2 = λ {d} fd⊑d → lub2 (((lub-from-chain)) (tarski-chain ⊥ f P′ cont-fun)) {d} (λ {n} → (tarski-lfp2 P′ f (mon cont-fun) d fd⊑d) n)
                                }
                            

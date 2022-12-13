module posets where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
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

--record continuous-fun {A B : Set} {_⊑₁_ : A → A → Set} {_⊑₂_ : B → B → Set} (P₁ : poset A _⊑₁_) (P₂ : poset B _⊑₂_) (f : A → B) : Set where
--  field
--    mon : monotone-fun P₁ P₂ f
--    lub-preserve : ∀ {c : chain P₁} (⋃ : lub c) → f (lub-element ⋃) ≡ lub (chain-map c f mon)

record cpo {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) : Set where
  field
    chain-complete : ∀ {c : chain P} → lub c 
open cpo

record domain {D : Set} {_⊑_ : D → D → Set} (P : poset D _⊑_) (⊥ : D) : Set where
  field
    chain-complete : cpo P
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

--lubs-shift-invariant : ∀ {D : Set} {_⊑_ : D → D → Set} (f f′ : ℕ → D) {P :  poset D _⊑_} (c : chain P f) (c′ : chain P f′) → ∃[ k ] (∀ (n : ℕ) f n ≡ f′ (k + n)) → ∃[ d ] (lub c d) × (lub c′ d))


--tarski : ∀ {D : Set} {_⊑_ : D → D → Set} {f : D → D} {P : poset D _⊑_} → ∃[ d ] ((least-pre-fixed P f d) × (f d ≡ d))

--tarski 

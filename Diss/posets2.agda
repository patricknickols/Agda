module posets2 where
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq using (_≡_)

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

refl-≤ : ∀ {n : ℕ} → n ≤ n
antisym-≤ : ∀ {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
trans-≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

refl-≤ {zero} = z≤n
refl-≤ {suc n} = s≤s (refl-≤ {n})

antisym-≤ z≤n z≤n = Eq.refl
antisym-≤ (s≤s n≤m) (s≤s m≤n) = Eq.cong suc (antisym-≤ n≤m m≤n)

trans-≤ z≤n z≤n = z≤n
trans-≤ z≤n (s≤s n≤p) = z≤n
trans-≤ (s≤s m≤n) (s≤s n≤p) = s≤s (trans-≤ m≤n n≤p)

record poset : Set₁ where
  field
    A : Set
    R : A → A → Set
    reflexive     : ∀ {a : A} → R a a 
    antisymmetric : ∀ {a b : A} → (R a b) → (R b a) → a ≡ b
    transitive    : ∀ {a b c : A} → (R a b) → (R b c) → (R a c)
open poset

nats : poset
nats = record
         { A = ℕ
         ; R = _≤_
         ; reflexive = refl-≤
         ; antisymmetric = antisym-≤
         ; transitive = trans-≤
         }

iterate : {D : Set} (n : ℕ) → (D → D) → (D → D)
iterate 0 f d = d 
iterate (suc n) f d = f ((iterate n f) d) 

record monotone-fun (P⊆ : poset) (Q⊑ : poset) : Set where
  private P : Set
  P = A P⊆
  private Q : Set
  Q = A Q⊑
  private _⊆_ : P → P → Set
  _⊆_ = R P⊆
  private _⊑_ : Q → Q → Set
  _⊑_ = R Q⊑
  field
    g : P → Q
    mon : ∀ {a a′ : P} → a ⊆ a′ → (g a) ⊑ (g a′)
open monotone-fun
        
record chain (P≤ : poset) : Set where
  field
    monotone : monotone-fun nats P≤
open chain

record lub {P⊑ : poset} (c : chain P⊑) : Set where
  private P : Set
  P = A P⊑
  private _⊑_ : P → P → Set
  _⊑_ = R P⊑
  private f : ℕ → P
  f = g (monotone c)
  field
    ⊔ : P
    lub1 : ∀ {n : ℕ} → f n ⊑ ⊔
    lub2 : ∀ {d′ : P} → (∀ {n : ℕ} → f n ⊑ d′) → ⊔ ⊑ d′
open lub


chain-map : {P≤ : poset} {Q≤ : poset} (c : chain P≤) → (monotone-fun P≤ Q≤) → (chain Q≤) 

chain-map c f = record { monotone = 
                                    record { g = λ n → let dₙ = (g (monotone c) n) in
                                             g f dₙ
                                           ; mon = λ a≤a′ → mon f (mon (monotone c) a≤a′)
                                           }
                       }
                                              
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


product-equality : {A : Set} {a a′ b b′ : A} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
product-equality {a} {a′} {b} {b′} Eq.refl Eq.refl = Eq.refl

domain-product : domain → domain → domain

product-R : {D₁ D₂ : domain} → (pair₁ pair₂ : (A (pos D₁)) × (A (pos D₂))) → Set
product-R {D₁} {D₂} (d₁ , d₂) (d₁′ , d₂′) = ((R (pos D₁)) d₁ d₁′) × ((R (pos D₂)) d₂ d₂′)

product-R-refl : {D₁ D₂ : domain} → {pair₁ : (A (pos D₁)) × (A (pos D₂))} → product-R {D₁} {D₂} pair₁ pair₁
product-R-refl {D₁} {D₂} = reflexive (pos D₁) , reflexive (pos D₂)

product-R-antisym : {D₁ D₂ : domain} → {pair₁ pair₂ : (A (pos D₁)) × (A (pos D₂))} → product-R {D₁} {D₂} pair₁ pair₂ → product-R {D₁} {D₂} pair₂ pair₁ → pair₁ ≡ pair₂
product-R-antisym {D₁} {D₂} {d₁ , d₂} {d₁′ , d₂′} (d₁≤d₁′ , d₂≤d₂′) (d₁′≤d₁ , d₂′≤d₂) = {!product-equality ((antisymmetric (pos D₁)) d₁≤d₁′ d₁′≤d₁)  ?!}

product-R-trans : {D₁ D₂ : domain} → {pair₁ pair₂ pair₃ : (A (pos D₁)) × (A (pos D₂))} → product-R {D₁} {D₂} pair₁ pair₂ → product-R {D₁} {D₂} pair₂ pair₃ → product-R {D₁} {D₂} pair₁ pair₃
product-R-trans {D₁} {D₂} (d₁≤d₁′ , d₂≤d₂′) (d₁′≤d₁″ , d₂′≤d₂″) = transitive (pos D₁) d₁≤d₁′ d₁′≤d₁″ , transitive (pos D₂) d₂≤d₂′ d₂′≤d₂″

product-pos : domain → domain → poset
product-pos D₁ D₂ = record
                      { A = A (pos D₁) × A (pos D₂)
                      ; R = product-R {D₁} {D₂}
                      ; reflexive = product-R-refl {D₁} {D₂}
                      ; antisymmetric = product-R-antisym {D₁} {D₂}
                      ; transitive = product-R-trans {D₁} {D₂}
                      }

proj₁-chain : {D₁ D₂ : domain} → chain (product-pos D₁ D₂) → chain (pos D₁)
proj₁-chain c = record { monotone = record { g = λ n → proj₁ ((g (monotone c)) n)
                                           ; mon = λ x → proj₁ (mon (monotone c) x)
                                           }
                       }

proj₂-chain : {D₁ D₂ : domain} → chain (product-pos D₁ D₂) → chain (pos D₂)
proj₂-chain c = record { monotone = record { g = λ n → proj₂ ((g (monotone c)) n)
                                           ; mon = λ x → proj₂ (mon (monotone c) x)
                                           }
                       }


domain-product D₁ D₂ = record { pos = product-pos D₁ D₂
                              ; chain-complete = λ c → record
                                { ⊔ = ⊔ ((chain-complete D₁) (proj₁-chain {D₁} {D₂} c)) , ⊔ ((chain-complete D₂) (proj₂-chain {D₁} {D₂} c))
                                ; lub1 = lub1 ((chain-complete D₁) (proj₁-chain {D₁} {D₂} c)) , lub1 ((chain-complete D₂) (proj₂-chain {D₁} {D₂} c))
                                ; lub2 = λ x → (lub2 (chain-complete D₁ (proj₁-chain {D₁} {D₂} c)) λ {n} → proj₁ (x {n})) , (lub2 (chain-complete D₂ (proj₂-chain {D₁} {D₂} c)) λ {n} → proj₂ (x {n}))
                                }
                              ; bottom = record { ⊥ = ⊥ (bottom D₁) , ⊥ (bottom D₂)
                                                ; ⊥-is-bottom = (⊥-is-bottom (bottom D₁)) , (⊥-is-bottom (bottom D₂))
                                                }
                              }


domain-dependent-product : (I : Set) → (I → domain) → domain
domain-dependent-product-pos : (I : Set) → (I → domain) → poset
domain-dependent-R : (I : Set) → (f : I → domain) → ((i : I) → (A (pos (f i))))  → ((i : I) → (A (pos (f i)))) → Set
domain-dependent-R I f p₁ p₂ = (i : I) → R (pos (f i)) (p₁ i) (p₂ i)

domain-dependent-refl : (I : Set) → (f : I → domain) → {p : (i : I) → (A (pos (f i)))} → domain-dependent-R I f p p
domain-dependent-refl I f i = reflexive (pos (f i))


postulate
  function-extensionality : ∀ {A B : Set} {f f′ : A → B}
    → (∀ (x : A) → f x ≡ f′ x)
      -----------------------
    → f ≡ f′

postulate
  dependent-function-extensionality : {I : Set} {D : I → Set} {p p′ : (i : I) → (D i) }
    → (∀ (i : I) → p i ≡ p′ i)
    → p ≡ p′

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
chain-of-functions I f c i = record { monotone = record
                                      { g = λ n → g (monotone c) n i
                                      ; mon = λ a≤a′ → (mon (monotone c) a≤a′) i
                                      }
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
                      
postulate chain-complete-flat-domain-pos-B : ∀ {B} → (c : chain (flat-domain-pos B)) → lub c
--EDIT

flat-domain A = record { pos = flat-domain-pos A
                       ; chain-complete = chain-complete-flat-domain-pos-B
                       ; bottom = record
                         { ⊥ = ⊥₁
                         ; ⊥-is-bottom = z≼n
                         }
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

tarski-fix : ∀ (P : domain) →  (cont-fun : cont-fun P P) → least-pre-fixed (pos P) (g (mon cont-fun))

tarski-fⁿ⊥ : ∀ (P : domain) (f : A (pos P) → A (pos P)) → ℕ → A (pos P)

tarski-fⁿ⊥ P f n = iterate n f (⊥ (bottom P))

tarski-fⁿ⊥⊑fⁿ⁺¹⊥ : (P : domain) (cont-fun : cont-fun P P) → {a a′ : ℕ} → a ≤ a′ → (R (pos P)) ((tarski-fⁿ⊥ P (g (mon cont-fun))) a) ((tarski-fⁿ⊥ P (g (mon cont-fun))) a′)
 
tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun _≤_.z≤n = ⊥-is-bottom (bottom P)
tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun (_≤_.s≤s m≤n) = (mon (mon cont-fun)) (tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun m≤n)


tarski-fⁿ⊥-mon : (P : domain) (cont-fun : cont-fun P P) → monotone-fun nats (pos P)

tarski-fⁿ⊥-mon P cont-fun =  record { g = tarski-fⁿ⊥ P (g (mon cont-fun))
                                    ; mon = λ a≤a′ → tarski-fⁿ⊥⊑fⁿ⁺¹⊥ P cont-fun a≤a′
                                    }

tarski-chain-of-fⁿ⊥ : (P : domain) (cont-fun : cont-fun P P) → chain (pos P)

tarski-chain-of-fⁿ⊥ P cont-fun = record { monotone = tarski-fⁿ⊥-mon P cont-fun }

tarski-lfp1 :
  ∀ (P : domain) (cont-fun : cont-fun P P)
  → let ⋃ = (chain-complete P) in
    let fⁿ⊥ = (tarski-chain-of-fⁿ⊥ P cont-fun) in
    (g (mon cont-fun)) (⊔ (⋃ fⁿ⊥)) ≡ ⊔ (⋃ fⁿ⊥)


lubs-shift-invariant :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (monotone c)) n ≡ (g (monotone c′)) (k + n)) →
    let ⋃ = (chain-complete P) in
      ⊔ (⋃ c) ≡ ⊔ (⋃ c′)


lubs-shift-invariant-1 :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (monotone c)) n ≡ (g (monotone c′)) (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in 
    ⊔ (⋃ c) ⊑ ⊔ (⋃ c′)


lubs-shift-invariant-2 :
  ∀ (P : domain) (c c′ : chain (pos P)) → (k : ℕ) → (∀ {n : ℕ} → (g (monotone c)) n ≡ (g (monotone c′)) (k + n)) →
  let ⋃ = (chain-complete P) in
  let _⊑_ = (R (pos P)) in
    ⊔ (⋃ c′) ⊑ ⊔ (⋃ c)

a≡b≤c→a≤c : ∀ {D : Set} {_⊑_ : D → D → Set} {a b c : D} → a ≡ b → b ⊑ c → a ⊑ c

a≡b≤c→a≤c Eq.refl b≤c = b≤c

lubs-shift-invariant-1 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c) (λ {n} → a≡b≤c→a≤c {_⊑_ = R (pos P)} (x {n}) (lub1 (⋃ c′) {k + n}))

n≤sucn : ∀ (n : ℕ) → n ≤ suc n
n≤sucn zero = _≤_.z≤n
n≤sucn (suc n) = _≤_.s≤s (n≤sucn n)

n≤k+n : ∀ (n k : ℕ) → n ≤ k + n
n≤k+n zero _ = _≤_.z≤n
n≤k+n (suc n) zero = _≤_.s≤s (n≤k+n n zero)
n≤k+n (suc n) (suc k) = _≤_.s≤s (trans-≤ (n≤sucn n) (n≤k+n (suc n) k))


a≤b≡c≤d→a≤d : ∀ (P : poset) {a b c d : (A P)} → (R P) a b → c ≡ b → (R P) c d → (R P) a d
a≤b≡c≤d→a≤d P a⊑b Eq.refl c⊑d = (transitive P) a⊑b c⊑d


lubs-shift-invariant-2 P c c′ k x =
  let ⋃ = (chain-complete P) in
    lub2 (⋃ c′) λ {n} → a≤b≡c≤d→a≤d (pos P) (mon (monotone c′) (n≤k+n n k)) (x {n}) (lub1 (⋃ c))

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


≡→⊑ : ∀ (P : poset) {a b : (A P)} → (a ≡ b) → ((R P) a b)
≡→⊑ P Eq.refl = reflexive P


tarski-fix P cont-fun =
  let ⋃ = (chain-complete P) in
  let fⁿ⊥ = (tarski-chain-of-fⁿ⊥ P cont-fun) in
    record { lfp1 = record
                           { d = ⊔ (⋃ fⁿ⊥)
                           ; pre-fix = ≡→⊑ (pos P) (tarski-lfp1 P cont-fun)
                           }
             ; lfp2 = λ {d} fd⊑d → lub2 (⋃ fⁿ⊥) {d} λ {n} → tarski-lfp2 P (mon (cont-fun)) d fd⊑d n
            }

------------------------------------------------------------------------------------------------------------------------------------------------------------

function-domain : (P P′ : domain) → domain

function-⊑ : {P P′ : domain} (f : cont-fun P P′) → (f′ : cont-fun P P′) → Set

function-⊑ {P} {P′} f f′ = ∀ {x : A (pos P)} → (R (pos P′)) ((g (mon f)) x) ((g (mon f′)) x)

postulate
  cont-fun-extensionality : ∀ {P P′ : domain} {f f′ : cont-fun P P′}
    → (∀ (x : A (pos P)) → (g (mon f)) x ≡ (g (mon f′)) x)
      -----------------------
    → f ≡ f′


function-⊑-antisymmetry : (P P′ : domain) (f : cont-fun P P′) (f′ : cont-fun P P′) → function-⊑ f f′ → function-⊑ f′ f → f ≡ f′

function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f = cont-fun-extensionality (λ x → antisymmetric (pos P′) (f⊑f′ {x}) (f′⊑f {x}))

function-pos : (P P′ : domain) → poset

function-pos P P′ = record { A = cont-fun P P′
                           ; R = function-⊑
                           ; reflexive = λ {a} {x} → reflexive (pos P′)
                           ; antisymmetric = λ {f} {f′} f⊑f′ f′⊑f → function-⊑-antisymmetry P P′ f f′ f⊑f′ f′⊑f
                           ; transitive = λ {a} {b} {c} f⊑f′ f′⊑f″ → λ {x} → transitive (pos P′) (f⊑f′ {x}) (f′⊑f″ {x})
                           }

function-domain-chain-complete : (P P′ : domain) → ∀ (c : chain (function-pos P P′)) → lub c

function-domain-⊔ : (P P′ : domain) → ∀ (c : chain (function-pos P P′)) → cont-fun P P′   


chain-of-fₙ[d] : (P P′ : domain) → (chain-of-fₙ : chain (function-pos P P′)) → (d : A (pos P)) → chain (pos P′)

chain-of-fₙ[d] P P′ chain-of-fₙ d = record { monotone =
                                                        record { g = λ n → let fₙ = g (mon (g (monotone chain-of-fₙ) n)) in
                                                                     fₙ d
                                                               ; mon = λ a≤a′ → mon (monotone chain-of-fₙ) a≤a′
                                                               }
                                           }

⊔-chain-of-fₙ[d] : (P P′ : domain) → (chain-of-fₙ : chain (function-pos P P′)) → (d : A (pos P)) → A (pos P′)

⊔-chain-of-fₙ[d] P P′ chain-of-fₙ d = let ⋃ = chain-complete P′ in
  ⊔ (⋃ (chain-of-fₙ[d] P P′ chain-of-fₙ d))

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

chain-fₘₙ-with-m-fixed P double-index-fun = λ m → record { monotone = record { g = λ n → (g double-index-fun) (m , n)
                                                                                     ; mon = λ a≤a′ → mon (double-index-fun) (refl-≤ , a≤a′)
                                                                                     }
                                                                 }


chain-fₘₙ-with-n-fixed P double-index-fun = λ n → record { monotone = record { g = λ m → (g double-index-fun) (m , n)
                                                                                      ; mon = λ a≤a′ → mon (double-index-fun) (a≤a′ , refl-≤)
                                                                                      }
                                                                  }
chain-⊔fₙₖ-with-n-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (chain (pos P))
chain-⊔fₙₖ-with-n-fixed P double-index-fun = let ⋃ = chain-complete P in record
  { monotone = record { g = λ n → ⊔ (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n))
                      ; mon = λ {n} {n′} n≤n′ →
                          lub2
                           (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n)) λ {n₁} →
                            (transitive (pos P))
                             ((mon double-index-fun) (n≤n′ , refl-≤))
                             (lub1 (chain-complete P (chain-fₘₙ-with-m-fixed P double-index-fun n′)) {n₁})
                      }
  }


chain-⊔fₖₙ-with-n-fixed : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → (chain (pos P))
chain-⊔fₖₙ-with-n-fixed P double-index-fun = record
  { monotone = let ⋃ = chain-complete P in
               record
                      { g = λ m → ⊔ (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m))
                      ; mon = λ {m} {m′} m≤m′ →
                          lub2 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m)) λ {n} →
                            (transitive (pos P)) ((mon double-index-fun) (refl-≤ , m≤m′)) (lub1 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m′)) {n})
                      }
  }

fₖₖ-chain : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P)) → chain (pos P)
fₖₖ-chain P double-index-fun = record { monotone = record { g = λ x → (g double-index-fun) (x , x)
                                                          ; mon = λ a≤a′ → (mon double-index-fun) (a≤a′ , a≤a′)
                                                          }
                                      }

diagonalising-lemma-1 : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₙₖ-with-n-fixed P double-index-fun)) ≡ ⊔ ((chain-complete P) (fₖₖ-chain P double-index-fun))

diagonalising-lemma-2 : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₖₙ-with-n-fixed P double-index-fun)) ≡ ⊔ ((chain-complete P) (fₖₖ-chain P double-index-fun))

diagonalising-lemma : (P : domain) → (double-index-fun : monotone-fun nats²-pos (pos P))
  → ⊔ ((chain-complete P) (chain-⊔fₙₖ-with-n-fixed P double-index-fun)) ≡ ⊔ ((chain-complete P) (chain-⊔fₖₙ-with-n-fixed P double-index-fun))


swap-≡ : {A : Set} {a b : A} → a ≡ b → b ≡ a
swap-≡ Eq.refl = Eq.refl

max : ℕ → ℕ → ℕ
max zero b = b
max a zero = a
max (suc a) (suc b) = suc (max a b) 

max-sym : (a b : ℕ) → max a b ≡ max b a
max-sym zero zero = Eq.refl
max-sym zero (suc b) = Eq.refl
max-sym (suc a) zero = Eq.refl
max-sym (suc a) (suc b) = Eq.cong suc (max-sym a b)

a≤max-a-b : {b : ℕ} (a : ℕ) → a ≤ (max a b)
a≤max-a-b zero = _≤_.z≤n
a≤max-a-b {zero} (suc a) = refl-≤
a≤max-a-b {suc b} (suc a) = _≤_.s≤s (a≤max-a-b {b} a)

a≤b≡c→a≤c : {a b c : ℕ} → a ≤ b → b ≡ c → a ≤ c
a≤b≡c→a≤c a≤b Eq.refl = a≤b


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
    (lub2 (⋃ (fₖₖ-chain P double-index-fun)) λ {n} → transitive (pos P) (lub1 (⋃ (chain-fₘₙ-with-m-fixed P double-index-fun n)) {n}) (lub1 (⋃ (chain-⊔fₙₖ-with-n-fixed P double-index-fun)) {n}))


diagonalising-lemma-2 P double-index-fun = let ⋃ = chain-complete P in
  antisymmetric (pos P)
   (lub2
    (⋃ (chain-⊔fₖₙ-with-n-fixed P double-index-fun))
    (λ {m} → lub2 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun m)) (λ {n} → dₘₙ≤⊔dₖₖ P double-index-fun)))
   (lub2
    (⋃ (fₖₖ-chain P double-index-fun))
    (λ {n} → transitive (pos P) (lub1 (⋃ (chain-fₘₙ-with-n-fixed P double-index-fun n)) {n}) (lub1 (⋃ (chain-⊔fₖₙ-with-n-fixed P double-index-fun)))))

diagonalising-lemma P double-index-fun = Eq.trans (diagonalising-lemma-1 P double-index-fun) (swap-≡ (diagonalising-lemma-2 P double-index-fun))


lub-preserve-lemma : (P P′ : domain) → (c : chain (function-pos P P′)) → (c₁ : chain (pos P)) → (λ z → g (mon (g (monotone c) z)) (⊔ (chain-complete P c₁))) ≡ (λ z → ⊔ (chain-complete P′ (chain-map c₁ (mon (g (monotone c) z)))))

lub-preserve-lemma P P′ c c₁ = function-extensionality ((λ (n : ℕ) → (lub-preserve (g (monotone c) n) c₁)))

same-f-same-lub : (P : domain) (c c′ : chain (pos P)) → g (monotone c) ≡ g (monotone c′) → ⊔ (chain-complete P c) ≡ ⊔ (chain-complete P c′)

same-f-same-lub P c c′ Eq.refl = let ⋃ = chain-complete P in
  antisymmetric (pos P)
   (lub2 (⋃ c) (lub1 (⋃ c′)))
   (lub2 (⋃ c′) (lub1 (⋃ c)))


same-f-same-lub-≤ : (P : domain) (c c′ : chain (pos P)) → ((n : ℕ) → (R (pos P)) (g (monotone c) n) (g (monotone c′) n)) → (R (pos P)) (⊔ (chain-complete P c)) (⊔ (chain-complete P c′))

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
              (mon (mon (g (monotone c) n)) d≤d′)
              (lub1 (⋃ (chain-of-fₙ[d] P P′ c d′)) {n}))
         }

function-domain-chain : (P P′ : domain) (c : chain (function-pos P P′)) → (c₁ : chain (pos P)) → chain (pos P′)
function-domain-chain P P′ c c₁ = let ⋃ = chain-complete P′ in record
  { monotone = record { g =  λ z → ⊔ (⋃ (chain-map c₁ (mon (g (monotone c) z))))

                      ; mon = λ {a} {a′} a≤a′ →
                         lub2
                          (⋃ (chain-map c₁ (mon (g (monotone c) a))))
                          λ {n} →
                           transitive (pos P′)
                            (mon (monotone c) a≤a′)
                            (lub1 (⋃ (chain-map c₁ (mon (g (monotone c) a′)))) {n})
                      }
  } 

function-domain-doubly-indexed-fun : (P P′ : domain) → (c : chain (function-pos P P′)) → (c₁ : chain (pos P)) → monotone-fun nats²-pos (pos P′)
function-domain-doubly-indexed-fun P P′ c c₁  =
  record { g = λ x → 
             let m = (Data.Product.proj₁ x) in
             let n = (Data.Product.proj₂ x) in
             let c₁-fun = g (monotone c₁) in
             let chain-of-funs = g (monotone c) in
             let fₘ = g (mon (chain-of-funs m))  in
             let dₙ = c₁-fun n in 
           fₘ dₙ
         ; mon = λ {m₁,n₁} {m₂,n₂} m₁,n₁≤m₂,n₂ →
             let m₂ = Data.Product.proj₁ m₂,n₂ in
             let m₁≤m₂ = Data.Product.proj₁ m₁,n₁≤m₂,n₂ in
             let n₁≤n₂ = Data.Product.proj₂ m₁,n₁≤m₂,n₂ in
             let fₘ₁dₙ₁≤fₘ₂dₙ₁ = mon (monotone c) m₁≤m₂ in
             let fₘ₂dₙ₁≤fₘ₂dₙ₂ = mon (mon (g (monotone c) m₂)) (mon (monotone c₁) n₁≤n₂) in
           transitive (pos P′) fₘ₁dₙ₁≤fₘ₂dₙ₁ fₘ₂dₙ₁≤fₘ₂dₙ₂
         }



function-domain-⊔-lemma-1 : (P P′ : domain) → (c : chain (function-pos P P′)) → (c₁ : chain (pos P))
  → ⊔
    (chain-complete P′
      (function-domain-chain P P′ c c₁)) ≡
      ⊔
      (chain-complete P′
       (chain-⊔fₙₖ-with-n-fixed P′
        (function-domain-doubly-indexed-fun P P′ c c₁)))

function-domain-⊔-lemma-1 P P′ c c₁ =
  same-f-same-lub P′
   (function-domain-chain P P′ c c₁)
   (chain-⊔fₙₖ-with-n-fixed P′
    (function-domain-doubly-indexed-fun P P′ c c₁)
   )
   (function-extensionality
    λ x → same-f-same-lub P′
           (chain-map c₁ (mon (g (monotone c) x)))
           (chain-fₘₙ-with-m-fixed P′
            (function-domain-doubly-indexed-fun P P′ c c₁)
            x
           )
           Eq.refl
   )


function-domain-⊔-lemma-2 : (P P′ : domain) → (c : chain (function-pos P P′)) → (c₁ : chain (pos P)) → 
    ⊔
      (chain-complete P′
       (chain-⊔fₖₙ-with-n-fixed P′
        (function-domain-doubly-indexed-fun P P′ c c₁)))
      ≡
      ⊔
      (chain-complete P′
       (chain-map c₁ (function-domain-⊔-mon P P′ c)))

function-domain-⊔-lemma-2 P P′ c c₁ =
  same-f-same-lub P′ (chain-⊔fₖₙ-with-n-fixed P′
   (function-domain-doubly-indexed-fun P P′ c c₁))
   (chain-map c₁ (function-domain-⊔-mon P P′ c))
   (function-extensionality
    (λ x → same-f-same-lub P′
     (chain-fₘₙ-with-n-fixed P′
      (function-domain-doubly-indexed-fun P P′ c c₁) x
     )
     (chain-of-fₙ[d] P P′ c (g (monotone c₁) x))
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
      ≡⟨ same-f-same-lub P′
          (chain-of-fₙ[d] P P′ c (⊔ (⋃ c₁)))
          (function-domain-chain P P′ c c₁)
          (function-extensionality
           (λ n → lub-preserve (g (monotone c) n )c₁)
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
                                         ; mon = λ a≤a′ → ≡→⊑ (pos P′) Eq.refl
                                         }


function-domain-⊥-function P P′ = record { mon = function-domain-⊥-func-mon P P′  
                                         ; lub-preserve = λ c → antisymmetric (pos P′)
                                           (⊥-is-bottom (bottom P′))
                                           (lub2 (chain-complete P′ (chain-map c (function-domain-⊥-func-mon P P′)))
                                             (λ {n} → ≡→⊑ (pos P′) Eq.refl))
                                         }
                                         
function-domain P  P′ = record
  { pos = function-pos P P′
  ; chain-complete = function-domain-chain-complete P P′
  ; bottom = record { ⊥ = function-domain-⊥-function P P′
                    ; ⊥-is-bottom = λ {a} {x} → ⊥-is-bottom (bottom P′)
                    }
  }

tarski-continuous : ∀ (P : domain) → cont-fun (function-domain P P) P


tarski-mon : ∀ (P : domain) → monotone-fun (pos (function-domain P P)) (pos P)

tarski-lub-preserve : ∀ (P : domain)
  → (c : chain (pos (function-domain P P)))
  → g (tarski-mon P) (⊔ (chain-complete (function-domain P P) c)) ≡ ⊔ (chain-complete P (chain-map c (tarski-mon P)))



fix-f′-is-pre-fixed : ∀ (P : domain) → (f : cont-fun P P) → (f′ : cont-fun P P) → (f⊑f′ : function-⊑ f f′) → R (pos P) (g (mon f) (⊔ (chain-complete P (tarski-chain-of-fⁿ⊥ P f′)))) (⊔ (chain-complete P (tarski-chain-of-fⁿ⊥ P f′)))

fix-f′-is-pre-fixed P f f′ f⊑f′ = transitive (pos P) ((f⊑f′ {d (lfp1 (tarski-fix P f′))})) (pre-fix (lfp1 (tarski-fix P f′)))


tarski-mon P = record { g =  λ (cont-fun : cont-fun P P) → d (lfp1 (tarski-fix P cont-fun))
                      ; mon = λ {f} {f′} f⊑f′ → lfp2 (tarski-fix P f) (fix-f′-is-pre-fixed P f f′ f⊑f′)
                      }


remark-237 : (P : domain) → (P′ : domain) → (c : chain (pos P)) → (f : monotone-fun (pos P) (pos P′))
  → (∀ (d : chain (pos P)) → (R (pos P′)) ((g f) (⊔ (chain-complete P d))) (⊔ (chain-complete P′ (chain-map d f))))
  → cont-fun P P′


unique-lub : ∀ (P : poset) → (c : chain P) → (a b : lub c) → ⊔ a ≡ ⊔ b
unique-lub P c a b = antisymmetric P (lub2 a (lub1 b)) (lub2 b (lub1 a))

remark-237 P P′ c f f⋃dₙ⊑⋃fdₙ = record { mon = f
                                       ; lub-preserve = λ c → antisymmetric (pos P′) (f⋃dₙ⊑⋃fdₙ c) (lub2 (chain-complete P′ (chain-map c f)) (λ {n} → mon f (lub1 (chain-complete P c))))
                                       }

fix⋃fₙ⊑⋃fixfₙ : (P : domain) → (c : chain (function-pos P P)) → (d : chain (function-pos P P))
  → R (pos P)
     (⊔
      (chain-complete P (tarski-chain-of-fⁿ⊥ P (function-domain-⊔ P P d))))
     (⊔
      (chain-complete P
       (chain-map d
        (tarski-mon P))))

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

chain-of-fₖ[fixfₖ] P d = record { monotone = record { g = λ k → g (mon (g (monotone d) k)) ((g (tarski-mon P)) (g (monotone d) k))
                                                             ; mon = λ {a} {a′} a≤a′ → transitive (pos P) (mon (monotone d) a≤a′) ((mon (mon (g (monotone d) a′)))(mon (tarski-mon P) (mon (monotone d) a≤a′)) )
                                                             }
                                           }

⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] : (P : domain) → (d : chain (function-pos P P)) →
  ⊔-chain-of-fₙ[d] P P d
   (⊔
    (chain-complete P
     (chain-map d
      (tarski-mon P))))
 ≡
  ⊔
   (chain-complete P
    (chain-of-fₖ[fixfₖ] P d))

m,n→fₘfixfₙ : (P : domain) → (c : chain (function-pos P P)) → monotone-fun nats²-pos (pos P)

m,n→fₘfixfₙ P c = record { g = λ m,n
                           → let m = Data.Product.proj₁ m,n in
                             let n = Data.Product.proj₂ m,n in
                             let f = g (monotone c) in 
                             let fixfₙ = d (lfp1 (tarski-fix P (f n))) in
                           g (mon (f m)) (fixfₙ)     
                         ; mon = λ {m,n} {m′,n′} m,n≤m′,n′
                           → let m≤m′ = Data.Product.proj₁ m,n≤m′,n′ in
                             let n≤n′ = Data.Product.proj₂ m,n≤m′,n′ in
                             let m′ = Data.Product.proj₁ m′,n′ in
                           transitive (pos P) (mon (monotone c) m≤m′) ((mon (mon (g (monotone c) m′))) (mon (tarski-mon P) (mon (monotone c) n≤n′)))
                         }

⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] P d =
  let ⋃ = chain-complete P in
  let [⋃fₘ][⋃fixfₙ] = ⊔-chain-of-fₙ[d] P P d (⊔ (⋃ (chain-map d (tarski-mon P)))) in
  begin
    [⋃fₘ][⋃fixfₙ]
  ≡⟨ same-f-same-lub P
      (chain-of-fₙ[d] P P d (⊔ (⋃(chain-map d (tarski-mon P)))))
      (chain-⊔fₙₖ-with-n-fixed P (m,n→fₘfixfₙ P d))
      (function-extensionality λ n →
       Eq.trans
       (lub-preserve (g (monotone d) n) (chain-map d (tarski-mon P)))
       (same-f-same-lub P
        (chain-map (chain-map d (tarski-mon P)) (mon (g (monotone d) n)))
        (chain-fₘₙ-with-m-fixed P (m,n→fₘfixfₙ P d) n)
        Eq.refl)) ⟩
    ⊔ (⋃ (chain-⊔fₙₖ-with-n-fixed P (m,n→fₘfixfₙ P d)))
  ≡⟨ diagonalising-lemma-1 P (m,n→fₘfixfₙ P d) ⟩
    ⊔ (⋃ (fₖₖ-chain P (m,n→fₘfixfₙ P d)))
  ≡⟨ same-f-same-lub P (fₖₖ-chain P (m,n→fₘfixfₙ P d)) (chain-of-fₖ[fixfₖ] P d) Eq.refl ⟩
    ⊔ (⋃ (chain-of-fₖ[fixfₖ] P d))
  ∎ 

⋃fixfₙ-is-pre-fix P c d = a≡b≤c→a≤c {A (pos P)} {R (pos P)} (⋃fₘ[⋃fixfₙ]=⋃[fₖfixfₖ] P d) (same-f-same-lub-≤ P (chain-of-fₖ[fixfₖ] P d) (chain-map d (tarski-mon P)) λ n → pre-fix (lfp1 (tarski-fix P (g (monotone d) n)))) 


fix⋃fₙ⊑⋃fixfₙ P c d = lfp2 (tarski-fix P (function-domain-⊔ P P d)) (⋃fixfₙ-is-pre-fix P c d)


tarski-lub-preserve P c = lub-preserve (remark-237 ((function-domain P P)) P c (tarski-mon P) (fix⋃fₙ⊑⋃fixfₙ P c)) c


tarski-continuous P = record { mon = tarski-mon P
                             ; lub-preserve = tarski-lub-preserve P
                             }


------------------------------------------------------------------------------------------------------------------------------------------------------------

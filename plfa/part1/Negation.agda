module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import plfa.part1.Relations using (_<_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
    ---
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬A A = ¬A A

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
    ---
  → A
    -----
  → ¬ ¬ A

¬¬-intro x ¬x = ¬x x

¬¬¬-elim : forall {A : Set}
    -------
  → ¬ ¬ ¬ A
    ---
  → ¬ A

¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
    -------
  → (A → B)
    -----------
  → (¬ B → ¬ A)

contraposition f ¬b a = ¬b (f a)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

suc≡→≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc≡→≡ {zero} {zero} sucm≡sucn = refl
suc≡→≡ {m} {m} refl = refl

¬≡→¬suc≡ : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n
¬≡→¬suc≡ m≢n sucm≡sucn = m≢n (suc≡→≡ sucm≡sucn)

<→¬> : ∀ {m n : ℕ} → m < n → ¬ (n < m)
<→¬> {suc m} {suc n} (_<_.s<s m<n) (_<_.s<s n<m) = <→¬> m<n n<m

≡→¬< : ∀ {m n : ℕ} → m ≡ n → ¬ (m < n)
≡→¬< {suc m} {suc n} sucm≡sucn (_<_.s<s m<n) = ≡→¬< (suc≡→≡ sucm≡sucn) m<n  

<→¬≡ : ∀ {m n : ℕ} → m < n → ¬ (m ≡ n)
<→¬≡ {zero} _<_.z<s = peano
<→¬≡ {suc m} {suc n} (_<_.s<s m<n) = ¬≡→¬suc≡ (<→¬≡ m<n) 

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive n n<n = <→¬> n<n n<n

trichotomy-m<n : ∀ {m n : ℕ}
    -----
  → m < n
    ---------------------
  → ¬ (m ≡ n) × ¬ (n < m)

trichotomy-m<n m<n = <→¬≡ m<n , <→¬> m<n

trichotomy-m≡n : ∀ {m n : ℕ}
    -----
  → m ≡ n
    ---------------------
  → ¬ (m < n) × ¬ (n < m)

trichotomy-m≡n m≡n =  ≡→¬< m≡n , ≡→¬< (sym m≡n)

trichotomy-m>n : ∀ {m n : ℕ}
    -----
  → n < m
    ---------------------
  → ¬ (n ≡ m) × ¬ (m < n)

trichotomy-m>n m>n = trichotomy-m<n m>n 

×-≡ : {A B : Set} {x₁ x₂ : A} {y₁ y₂ : B}
    -----------------
  → x₁ ≡ x₂ → y₁ ≡ y₂
    ---------------------
  → (x₁ , y₁) ≡ (x₂ , y₂)

×-≡ refl refl = refl

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record { to = λ ¬[x+y] → (λ x → ¬[x+y] (inj₁ x)) , (λ y → ¬[x+y] (inj₂ y)) 
         ; from = λ{(¬x , ¬y) (inj₁ x) → ¬x x
                   ;(¬x , ¬y) (inj₂ y) → ¬y y
                   }
         ; from∘to = λ ¬[x+y] → extensionality (λ { (inj₁ x) → refl ; (inj₂ y) → refl })
         ; to∘from = λ{(¬x , ¬y) → ×-≡ refl refl}
         }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{x → k (inj₁ x)})

em→double-negation : ∀ {A : Set}
    -------
  → A ⊎ ¬ A
    -----------
  → (¬ ¬ A → A)

em→double-negation (inj₁ a) _ = a
em→double-negation (inj₂ ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

em→peirce : ∀ {A B : Set}
    -----------------
  → A ⊎ ¬ A → B ⊎ ¬ B
    -------------------
  → (((A → B) → A) → A)

em→peirce (inj₁ a) _ _ = a
em→peirce (inj₂ ¬a) _ a→b→a = a→b→a (λ a → ⊥-elim (¬a a))

em→implication-disjunction : ∀ {A B : Set}
    -----------------
  → A ⊎ ¬ A → B ⊎ ¬ B
    -------------------
  → ((A → B) → ¬ A ⊎ B)

em→implication-disjunction (inj₁ a) _ a→b = inj₂ (a→b a)
em→implication-disjunction (inj₂ ¬a) _ _ = inj₁ ¬a

em→de-morgan : ∀ {A B : Set}
    -----------------
  → A ⊎ ¬ A → B ⊎ ¬ B
    -----------------------
  → (¬ (¬ A × ¬ B) → A ⊎ B)

em→de-morgan (inj₁ a) _ _ = inj₁ a
em→de-morgan (inj₂ ¬a) (inj₁ b) _ = inj₂ b
em→de-morgan (inj₂ ¬a) (inj₂ ¬b) ¬⟨¬a,¬b⟩ = ⊥-elim (¬⟨¬a,¬b⟩ ( ¬a , ¬b ))

de-morgan→em : (∀ {A B : Set}
    ----------------------
  → ¬ (¬ A × ¬ B) → A ⊎ B)
    ------------------- 
  → {A : Set} → A ⊎ ¬ A 

de-morgan→em dem = dem (λ{ (¬a , ¬¬a) → ¬¬a ¬a})


double-negation→em : (∀ {A : Set} 
    ------------
  → (¬ ¬ A → A))
    --------------------
  → {A : Set} →  A ⊎ ¬ A

double-negation→em dne = dne em-irrefutable 

peirce→em : (∀ {A B : Set}
    --------------------
  → (((A → B) → A) → A))
    -------------------
  → {A : Set} → A ⊎ ¬ A 

peirce→em peirce = peirce (λ [a+¬a] → ⊥-elim (em-irrefutable [a+¬a]))

implication-disjunction→em : (∀ {A B : Set}
    -------------------
  → ((A → B) → ¬ A ⊎ B))
    -------------------
  → {A : Set} → A ⊎ ¬ A

⊎-comm-implication : ∀ {A B : Set}
    -----
  → A ⊎ B
    -----
  → B ⊎ A

⊎-comm-implication (inj₁ a) = inj₂ a
⊎-comm-implication (inj₂ b) = inj₁ b 

implication-disjunction→em imp-dis = ⊎-comm-implication (imp-dis (λ x → x))

Stable : Set → Set
Stable A = ¬ ¬ A → A

Stable-¬ : ∀ {A : Set}
    ------------
  → Stable (¬ A)

Stable-¬ = ¬¬¬-elim

Stable-× : ∀ {A B : Set}
    -------------------
  → Stable A → Stable B
    --------------
  → Stable (A × B)


Stable-× StableA StableB ¬¬⟨a,b⟩ = (a , b)
  where
    a = StableA (λ ¬a → ¬¬⟨a,b⟩ (λ ⟨a,b⟩ → ¬a (proj₁ ⟨a,b⟩)))
    b = StableB (λ ¬b → ¬¬⟨a,b⟩ (λ ⟨a,b⟩ → ¬b (proj₂ ⟨a,b⟩)))

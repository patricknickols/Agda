module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
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


module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _∸_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; _∘_; extensionality)
open import plfa.part1.Induction using (+-comm)

∀-elim : ∀ {A : Set} {B : A → Set}
    ---------------------
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -------
  → B M

∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× = record { to      = λ f → ⟨ (λ x → proj₁ (f x))  , (λ x → proj₂ (f x)) ⟩
                     ; from    = λ f,g x → ⟨ proj₁ f,g x , proj₂ f,g x ⟩
                     ; from∘to = λ x → refl
                     ; to∘from = λ y → refl
                     }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ (inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) x = inj₂ (g x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  extensionality-variant : ∀ {A : Set} {B : A → Set}
    → {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -------------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set}
  → ((∀ (x : Tri) → B x) ≃ B aa × B bb × B cc)

∀-× = record { to      = λ f → ⟨ f aa , ⟨ f bb  , f cc ⟩ ⟩
             ; from    = λ Baa,Bbb,Bcc → λ{ aa → proj₁ Baa,Bbb,Bcc 
                                          ; bb → proj₁ (proj₂ Baa,Bbb,Bcc)
                                          ; cc → proj₂ (proj₂ Baa,Bbb,Bcc)
                                          }
             ; from∘to = λ f → extensionality-variant  λ{ aa → refl ; bb → refl ; cc → refl}
             ; to∘from = λ y → refl
             }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    --------------
  → C

∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)

∀∃-currying = record { to      = ∃-elim
                     ; from    = λ{ g → λ{ x → λ{y → g ⟨ x , y ⟩}}}
                     ; from∘to = λ f → refl
                     ; to∘from = λ g → extensionality λ{⟨ x , y ⟩ → refl}
                     }


∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ = record { to      = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
                                  ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ 
                                  } 
                     ; from    = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
                                  ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
                                  }
                     ; from∘to = λ{ ⟨ x , inj₁ Bx ⟩ → refl
                                  ; ⟨ x , inj₂ Cx ⟩ → refl
                                  }
                     ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩ ) → refl
                                  ; (inj₂ ⟨ x , Cx ⟩ ) → refl
                                  }
                     }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ = λ{⟨ x , ⟨ Bx , Cx ⟩ ⟩ → ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩}

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc odd-n) with odd-∃ odd-n
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc even-n) with even-∃ even-n
...                    | ⟨ m , refl ⟩ = ⟨ m , refl ⟩


x+0≡x : ∀ (n : ℕ) → n + 0 ≡ n
x+0≡x (zero) = refl
x+0≡x (suc n) = cong suc (x+0≡x n)

x∸x≡0 : ∀ (x : ℕ) → x ∸ x ≡ 0
x∸x≡0 zero = refl
x∸x≡0 (suc x) = x∸x≡0 x

suc-x≡x+1 : ∀ (x : ℕ) → x + 1 ≡ suc x
suc-x≡x+1 zero = refl
suc-x≡x+1 (suc x) rewrite +-comm x 1 = refl

∸then+ : ∀ (a b : ℕ) → b ≤ a → a ∸ b + b ≡ a
∸then+ a .0 _≤_.z≤n = x+0≡x a
∸then+ (suc a) (suc b) (_≤_.s≤s b≤a) rewrite +-comm (a ∸ b) (suc b) | +-comm b (a ∸ b)= cong suc (∸then+ a b b≤a)

∸then+′ : ∀ (y z : ℕ) → y ≤ z → z ∸ y + suc y ≡ suc z
∸then+′ y z y≤z rewrite +-comm (z ∸ y) (suc y) | +-comm y (z ∸ y) | ∸then+ z y y≤z = refl

∃-+-≤ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤ {y} {z} _≤_.z≤n = ⟨ z , x+0≡x z ⟩
∃-+-≤ {suc y} {suc z} (_≤_.s≤s y≤z) = ⟨ z ∸ y , ∸then+′ y z y≤z ⟩

≤-refl : ∀ (y : ℕ) → y ≤ y
≤-refl zero = _≤_.z≤n
≤-refl (suc y) = _≤_.s≤s (≤-refl y)

suc-x+y≡x+suc-y : ∀ (x y : ℕ) → suc x + y ≡ x + suc y
suc-x+y≡x+suc-y zero y = refl
suc-x+y≡x+suc-y x zero rewrite +-comm x zero | +-comm x 1 = refl 
suc-x+y≡x+suc-y x (suc y) rewrite +-comm x (suc y) | +-comm x (suc (suc y)) = refl

∃-+-≤′ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤′ {y} {z} ⟨ zero , refl ⟩ = ≤-refl y
∃-+-≤′ {zero} ⟨ suc x , refl ⟩ = _≤_.z≤n
∃-+-≤′ {suc y} ⟨ suc x , refl ⟩ = _≤_.s≤s (∃-+-≤′ ⟨ suc x , suc-x+y≡x+suc-y x y ⟩ )

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)

∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ a→Ba = ¬Ba (a→Ba a)

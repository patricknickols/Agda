module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
        A
      → B
        -----
      → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₂ : ∀ {A B : Set} → A × B → B
proj₁ ⟨ x , y ⟩ = x
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_ 

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩ ≡ w
η-×′ w = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    {  to      = λ{⟨ a , b ⟩ → ⟨ b , a ⟩}
    ;  from    = λ{⟨ b , a ⟩ → ⟨ a , b ⟩}
    ;  from∘to = λ{⟨ a , b ⟩ → refl}
    ;  to∘from = λ{⟨ b , a ⟩ → refl}
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    {  to      = λ{⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩}
    ;  from    = λ{⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩}
    ;  from∘to = λ{⟨ ⟨ a , b ⟩ , c ⟩ → refl} 
    ;  to∘from = λ{⟨ a , ⟨ b , c ⟩ ⟩ → refl} 
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    {  to      = λ{x → ⟨ _⇔_.to x , _⇔_.from x ⟩}
    ;  from    = λ{
      ⟨ to_ , from_ ⟩ → record
        { to = to_
        ; from = from_
        }
      }
    ;  from∘to = λ{ x → refl}
    ;  to∘from = λ{ ⟨ a→b , b→a ⟩ → refl}
    }

data ⊤ : Set where

  tt :
   ---
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    {  to      = λ{ ⟨ tt , a ⟩ → a }
    ;  from    = λ{ a → ⟨ tt , a ⟩}
    ;  from∘to = λ{ ⟨ tt , a ⟩ → refl}
    ;  to∘from = λ{ a → refl}
    }
T-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
T-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
       A
       -----
     → A ⊎ B

  inj₂ :
       B
       -----
     → A ⊎ B 

case-⊎ : ∀ {A B C : Set}
  → (A → C) → (B → C) → A ⊎ B
    -------------------------
  → C

case-⊎ A→C B→C (inj₁ x) = A→C x
case-⊎ A→C B→C (inj₂ x) = B→C x

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w

uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm {A} {B} =
  record
    {  to      = λ{ (inj₁ A) → inj₂ A
                  ; (inj₂ B) → inj₁ B
                  }
    ;  from    = λ{ (inj₁ B) → inj₂ B
                  ; (inj₂ A) → inj₁ A
                  }
    ;  from∘to = λ{ (inj₁ A) → refl
                  ; (inj₂ B) → refl
                  }
    ;  to∘from = λ{ (inj₁ B) → refl
                  ; (inj₂ A) → refl
                  }
    }

⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc =
  record
    {  to      = λ{ (inj₁ A)        → inj₁ (inj₁ A) 
                  ; (inj₂ (inj₁ B)) → inj₁ (inj₂ B)
                  ; (inj₂ (inj₂ C)) → inj₂ C
                  }
    ;  from    = λ{ (inj₁ (inj₁ A)) → inj₁ A
                  ; (inj₁ (inj₂ B)) → inj₂ (inj₁ B)
                  ; (inj₂ C)        → inj₂ (inj₂ C)
                  }
    ;  from∘to = λ{ (inj₁ A) → refl
                  ; (inj₂ (inj₁ B)) → refl
                  ; (inj₂ (inj₂ C)) → refl
                  }
    ;  to∘from = λ{ (inj₁ (inj₁ A)) → refl
                  ; (inj₁ (inj₂ B)) → refl
                  ; (inj₂ C)        → refl
                  }
    }

data ⊥ : Set where
  -- nothing here!

⊥-elim : ∀ {A : Set}
  → ⊥
   ---
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityˡ =
  record
    {  to      = λ{ (inj₁ a) → a
                  ; (inj₂ ())
                  }
    ;  from    = λ a → inj₁ a
    ;  from∘to = λ{ (inj₁ a) → refl
                  ; (inj₂ ())
                  }
    ;  to∘from = λ a → refl
    }

⊥-identityʳ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (⊥ ⊎ A)
  ≃⟨ ⊎-comm ⟩
    (A ⊎ ⊥)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

→-elim : ∀ {A B : Set}
  -------------
  → (A → B) → A
  ---
  → B

→-elim A→B A = A→B A

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    {  to      = λ f → λ { ⟨ x , y ⟩ → f x y}
    ;  from    = λ g → λ {a → λ {b → g ⟨ a , b ⟩}}
    ;  from∘to = λ f → refl
    ;  to∘from = λ g → extensionality λ { ⟨ x , y ⟩ → refl}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    {  to      = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ 
    ;  from    = λ {⟨ f , g ⟩ → λ { (inj₁ a) → f a
                                  ; (inj₂ b) → g b
                                  }
                   }
    ;  from∘to = λ f → extensionality λ { (inj₁ a) → refl
                                        ; (inj₂ b) → refl
                                        }
  
    ;  to∘from = λ {⟨ f , g ⟩ → refl}
    }

→-distrib-× : ∀ {A B C : Set} → (A → (B × C)) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    {  to      = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ;  from    = λ{ ⟨ g , h ⟩ → λ{ a → ⟨ g a , h a ⟩}} 
    ;  from∘to = λ f → extensionality λ {x → η-× (f x)}
    ;  to∘from = λ{ ⟨ g , h ⟩ → refl}
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    {  to      = λ{ ⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩
                  ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩
                  }
    ;  from    = λ{ (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
                  ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩ 
                  }
    ;  from∘to = λ{ ⟨ inj₁ a , c ⟩ → refl
                  ; ⟨ inj₂ b , c ⟩ → refl
                  }
    ;  to∘from = λ{ (inj₁ ⟨ a , c ⟩) → refl
                  ; (inj₂ ⟨ b , c ⟩) → refl 
                  }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record { to      = λ { (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩
                       ; (inj₂ c)         → ⟨ inj₂ c , inj₂ c ⟩
                       }
         ; from    = λ { ⟨ inj₁ a , inj₁ b ⟩   → inj₁ ⟨ a , b ⟩
                       ; ⟨ inj₁ a , inj₂ c ⟩   → inj₂ c
                       ; ⟨ inj₂ c , _ ⟩        → inj₂ c 
                       }
         ; from∘to = λ { (inj₁ ⟨ a , b ⟩) → refl
                       ; (inj₂ b)         → refl
                       }
         }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
-- converse does not hold, e.g. consider ⟨ inj₁ a , inj2 d ⟩. This cannot be mapped to
-- A×B or a C×D since we only have elements of type A and D. 

module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
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

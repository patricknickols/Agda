module posets where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

record poset (A : Set) : Set₂ where
  field
    operator      : A → A → Set
    reflexive     : ∀ (a : A) → operator a a
    antisymmetric : ∀ (a b : A) → (operator a b) → (operator b a) → a ≡ b
    transitive    : ∀ (a b c : A) → (operator a b) → (operator b c) → (operator a c)
open poset

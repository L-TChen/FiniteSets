{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Logic

module FiniteSets.Kuratowski.Decidable.Base where

open import Cubical.Core.Prelude 
open import Cubical.Core.PropositionalTruncation
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary 

open import FiniteSets.Kuratowski renaming ([_] to K[_])
open import FiniteSets.Kuratowski.Properties

module _ {A : Set}
  (_≟_ : [ ∀[ x ∶ A ] ∀[ y ∶ A ] Decₚ (x ≡ₚ y) ]) where
  
  _∈?_ : [ ∀[ a ] ∀[ x ∶ K A ] Decₚ (a ∈ x) ]
  _∈?_ a = elimKprop {P = λ y → [ Decₚ (a ∈ y) ]} (isPropDec sq) (no (a∉∅ a)) f g
    where
      f : [ ∀[ b ] Decₚ (a ∈ K[ b ]) ]
      f b with a ≟ b
      ... | yes a≡b = yes (substₚ (λ b → a ∈ K[ b ]) a≡b here)
      ... | no ¬a≡b = no λ a∈[b] → ¬a≡b (∈⇒∈ₚ a∈[b])

      g : [ ∀[ x ] ∀[ y ] Decₚ (a ∈ x) ⇒ Decₚ (a ∈ y) ⇒ Decₚ (a ∈ x ∪ y) ]
      g x y (yes p) (yes q) = yes (left p)
      g x y (yes p) (no ¬q) = yes (left p)
      g x y (no ¬p) (yes q) = yes (right q)
      g x y (no ¬p) (no ¬q) =
        no λ a∈x∪y → elimPropTrunc (λ _ → λ ())
          (elim-⊎ (λ a∈ₚx → ¬p (∈ₚ⇒∈ a∈ₚx)) λ a∈ₚy → ¬q (∈ₚ⇒∈ a∈ₚy)) (∈⇒∈ₚ a∈x∪y)

module _ {A : Set}
  (_∈?_ : [ ∀[ a ∶ A ] ∀[ x ] Decₚ (a ∈ x) ]) where
  _≟_   : [ ∀[ x ∶ A ] ∀[ y ∶ A ] Decₚ (x ≡ₚ y) ]
  a ≟ b with a ∈? K[ b ]
  ... | yes p = yes (∈⇒∈ₚ p)
  ... | no ¬p = no λ a≡b → ¬p (∈ₚ⇒∈ a≡b)

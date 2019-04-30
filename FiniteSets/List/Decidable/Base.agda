{-# OPTIONS --cubical --safe #-}



module FiniteSets.List.Decidable.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Relation.Nullary hiding (¬_)

open import FiniteSets.List renaming ([_] to L[_])
open import FiniteSets.List.Properties
import FiniteSets.Kuratowski as K

module _ {A : Set} (_≟_ : [ ∀[ x ∶ A ] ∀[ y ∶ A ] Decₚ (x ≡ₚ y) ]) where
  open import FiniteSets.Kuratowski.Decidable

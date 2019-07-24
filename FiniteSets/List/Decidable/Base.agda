{-# OPTIONS --cubical --safe #-}

module FiniteSets.List.Decidable.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Relation.Nullary hiding (¬_)

open import FiniteSets.List renaming ([_] to L[_])
open import FiniteSets.List.Properties
import FiniteSets.Kuratowski as K

module _ {A : Set} (_≟_ : [ ∀[ x ∶ A ] ∀[ y ∶ A ] Decₚ (x ≡ₚ y) ]) where
  delete : A → L A → L A
  delete x = recL trunc [] eq? dupEq? comEq?
    where
      eq? : A → L A → L A
      eq? y xs with x ≟ y
      ... | yes p = xs
      ... | no ¬p = y ∷ xs

      dupEq? : ∀ y xs → eq? y (eq? y xs) ≡ eq? y xs
      dupEq? y xs with x ≟ y
      ... | yes p = refl
      ... | no ¬p = dup y xs

      comEq? : ∀ y z xs → eq? y (eq? z xs) ≡ eq? z (eq? y xs)
      comEq? y z xs with x ≟ y | x ≟ z
      comEq? y z xs | yes p | yes q = refl
      comEq? y z xs | yes p | no ¬q = refl
      comEq? y z xs | no ¬p | yes q = refl
      comEq? y z xs | no ¬p | no ¬q = com y z xs

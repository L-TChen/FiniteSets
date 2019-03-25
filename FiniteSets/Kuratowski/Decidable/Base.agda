{-# OPTIONS --cubical #-}

module FiniteSets.Kuratowski.Decidable.Base where

open import Cubical.Core.Prelude 
open import Cubical.Core.PropositionalTruncation
open import Cubical.Foundations.HLevels 
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

open import FiniteSets.Kuratowski
open import FiniteSets.Kuratowski.Properties

private
  variable
    ℓ   : Level

module DecMembership (A : Set ℓ) (_≟_ : (x y : A) → Dec ∥ x ≡ y ∥) where
  _∈?_ : (a : A) → (x : K A) → Dec ∥ a ∈ x ∥
  _∈?_ a = elimKprop (isPropDec squash)
    (no (elimPropTrunc (λ _ → isProp⊥) (a∉∅ _)))
    base step
    where
      base : (b : A) → Dec ∥ a ∈ [ b ] ∥
      base b with a ≟ b
      ... | yes p = elimPropTrunc (λ _ → isPropDec squash) (λ p → yes ∣ here p ∣) p
      ... | no  p = no {! !}
      step : ∀ x y → Dec ∥ a ∈ x ∥ → Dec ∥ a ∈ y ∥ → Dec ∥ a ∈ x ∪ y ∥
      step _ _ (yes p) (yes q) =
        yes (elimPropTrunc (λ _ → propTruncIsProp) (λ p → ∣ left p ∣ ) p)
      step _ _ (yes p) (no ¬q) =
        yes (elimPropTrunc (λ _ → propTruncIsProp) (λ p → ∣ left p ∣ ) p)
      step _ _ (no ¬p) (yes q) =
        yes (elimPropTrunc (λ _ → propTruncIsProp) (λ q → ∣ right q ∣) q)
      step _ _ (no ¬p) (no ¬q) = no  {!!}

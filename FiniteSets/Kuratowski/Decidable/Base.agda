{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Logic

module FiniteSets.Kuratowski.Decidable.Base
  {A : Set}
  (_≟_ : [ ∀[ x ∶ A ] ∀[ y ∶ A ] Decₚ (x ≡ₘ y) ]) where

open import Cubical.Core.Prelude 
open import Cubical.Core.PropositionalTruncation
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary 

open import FiniteSets.Kuratowski renaming ([_] to K[_])
open import FiniteSets.Kuratowski.Properties

_∈?_ : [ ∀[ a ∶ A ] ∀[ x ∶ K A ] Decₚ (a ∈ x) ]
a ∈? x = elimKprop {P = λ y → [ Decₚ (a ∈ y) ]} (isPropDec (snd (a ∈ _)))
  (no (a∉∅ a)) f g x
  where
    f : [ ∀[ b ] Decₚ (a ∈ K[ b ]) ]
    f b with a ≟ b
    ... | yes a≡b = yes (substₘ (λ b → a ∈ K[ b ]) a≡b here)
    ... | no ¬a≡b = no λ a∈[b] → ¬a≡b (∈⇒∈ₚ a∈[b])

    g : [ ∀[ x ] ∀[ y ] Decₚ (a ∈ x) ⇒ Decₚ (a ∈ y) ⇒ Decₚ (a ∈ x ∪ y) ]
    g x y (yes p) (yes q) = yes (left p)
    g x y (yes p) (no ¬q) = yes (left p)
    g x y (no ¬p) (yes q) = yes (right q)
    g x y (no ¬p) (no ¬q) =
      no λ a∈x∪y → elimPropTrunc (λ _ → λ ())
        (elim-⊎ (λ a∈ₚx → ¬p (∈ₚ⇒∈ a∈ₚx)) λ a∈ₚy → ¬q (∈ₚ⇒∈ a∈ₚy)) (∈⇒∈ₚ a∈x∪y)

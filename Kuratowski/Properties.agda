{-# OPTIONS --safe --cubical #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Prelude
open import Cubical.Foundations.HLevels
open import Level

open import FiniteSets.Kuratowski.Base

private
  variable
    ℓ  : Level
    A : Set ℓ

∪-idem : (x : K A) → x ∪ x ≡ x
∪-idem {A = A} = elimKprop (trunc _ _) (nl ∅) idem λ x y x∪x=x y∪y=y → 
    x ∪ y ∪ (x ∪ y) ≡⟨ assoc (x ∪ y) x y ⟩
    x ∪ y ∪ x ∪ y   ≡⟨ cong (_∪ y) (cong (_∪ x) (com x y)) ⟩
    y ∪ x ∪ x ∪ y   ≡⟨ cong (_∪ y) (sym (assoc y x x)) ⟩
    y ∪ (x ∪ x) ∪ y ≡⟨ cong (_∪ y) (cong (y ∪_) x∪x=x) ⟩
    y ∪ x ∪ y       ≡⟨ cong (_∪ y) (com y x) ⟩
    x ∪ y ∪ y       ≡⟨ sym (assoc x y y) ⟩
    x ∪ (y ∪ y)       ≡⟨ cong (x ∪_) y∪y=y ⟩
    x ∪ y             ∎

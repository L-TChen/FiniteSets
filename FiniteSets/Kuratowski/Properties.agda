{-# OPTIONS --cubical --allow-unsolved-metas #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

open import FiniteSets.Kuratowski.Base

--open import Cubical.Instance
open import Cubical.Instance.Algebra.Semilattice
open import Cubical.Instance.Algebra.Semilattice.Properties 

private
  variable
    ℓ     : Level
    A B X : Set ℓ

KA-is-free : ∀ ⊥ _⊔_ ⦃ _ : IsSemilattice B _⊔_ ⊥ ⦄
           → (X → B) → K X → B
KA-is-free ⊥ _⊔_ f = recK AisSet ⊥ f _⊔_
  ⊔-identityˡ ⊔-identityʳ (λ _ → ⊔-idem _) ⊔-assoc ⊔-comm

[a]≢∅ : {a : A} → ¬ [ a ] ≡ ∅
[a]≢∅ p = true≢false (cong (KA-is-free false _or_ (λ _ → true)) p)
  where open Semilattice Bool.Or-Semilattice

module _ {A : Set ℓ} where
  open Order (KFreeSemilattice A)

--------------------------------------------------------------------------------
-- a ∉ ∅

  a∉∅ : (a : A) → a ∉ ∅
  a∉∅ a = lem refl
    where
      lem : ∀ {x} → x ≡ ∅ → a ∉ x
      lem p here        = [a]≢∅ p
      lem p (left a∈x)  = lem (⊔-conicalˡ _ _ p) a∈x
      lem p (right a∈x) = lem (⊔-conicalʳ _ _ p) a∈x
      lem p (sq a∈x a∈x₁ i) =
        toPathP {A = λ _ → ⊥} (isProp⊥ (transp (λ i → ⊥) i0 (g a∈x)) (g a∈x₁)) i
          where g = lem p
        
  a∈x⇒[x]∪x≡x : ∀ (a : A) x → a ∈ x → [ a ] ∪ x ≡ x
  a∈x⇒[x]∪x≡x a = elim∈prop (trunc _ _) (idem a)
    (λ x y a∈x a∪x≡x →
      [ a ] ∪ x ∪ y   ≡⟨ assoc _ _ _ ⟩
      ([ a ] ∪ x) ∪ y ≡⟨ cong (_∪ y) a∪x≡x ⟩
      x ∪ y           ∎)
    (λ x y a∈y a∪y≡y →
      [ a ] ∪ x ∪ y   ≡⟨ cong ([ a ] ∪_) (com _ _) ⟩
      [ a ] ∪ y ∪ x   ≡⟨ assoc _ _ _ ⟩
      ([ a ] ∪ y) ∪ x ≡⟨ cong (_∪ x) a∪y≡y ⟩
      y ∪ x           ≡⟨ com _ _ ⟩
      x ∪ y           ∎)

  y⊆x⇒y∪x≡x  : ∀ {x : K A} y → (y ⊆ x) → (y ∪ x) ≡ x
  y⊆x⇒y∪x≡x {x = x} = elimKprop (λ p q → funExt λ f → trunc _ _ (p f) (q f))
    (λ _ → nl _)
    (λ a p → a∈x⇒[x]∪x≡x a _ (p a here) )
    λ z y px py f →
     (z ∪ y) ∪ x ≡⟨ sym (assoc _ _ _) ⟩
     z ∪ y ∪ x   ≡⟨ cong (z ∪_) (py λ a a∈y → f a (right a∈y)) ⟩
     z ∪ x       ≡⟨ px (λ a a∈z → f a (left a∈z) )  ⟩
     x           ∎

  y∪x≡x∧x∪y≡y : {x y : K A} → (y ∪ x ≡ x) × (x ∪ y ≡ y) → x ≡ y
  y∪x≡x∧x∪y≡y (y∪x≡x , x∪y≡y) = ≤-antisym _ _ x∪y≡y y∪x≡x

{-
extensionality : {A : Set ℓ} {x y : K A}
                 → (x ≡ y) ≃ ∀ (a : A) → a ∈ x ≡ a ∈ y
extensionality {A = A} {x} {y} = {!!}
-}

module Decidable (_≟_ : (x y : A) → Dec ∥ x ≡ y ∥) where
 
  []-injective : {a b : A} → [ a ] ≡ [ b ] → ∥ a ≡ b ∥
  []-injective {a} {b} eq = {!!}

  a∈[b]⇒a≡b : ∀ {a b : A} x → a ∈ x → x ≡ [ b ] → ∥ a ≡ b ∥
  a∈[b]⇒a≡b = elim∈prop (propPi λ _ → propTruncIsProp) {!!} {!!} {!!}

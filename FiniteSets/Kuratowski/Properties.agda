{-# OPTIONS --cubical --allow-unsolved-metas #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything hiding (_∨_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

--open import Cubical.Instance
open import Cubical.Instance.Algebra.Semilattice

open import FiniteSets.Kuratowski.Base

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : Set ℓ'

KA-is-free : ∀ ⊥ _∨_ ⦃ _ : IsSemilattice B _∨_ ⊥ ⦄
           → (A → B) → K A → B
KA-is-free ⊥ _∨_ f = recK Aset ⊥ f _∨_
  identityˡ identityʳ (λ _ → idempotency _) associativity commutativity

[a]≢∅ : {a : A} → ¬ [ a ] ≡ ∅
[a]≢∅ p = true≢false (cong (KA-is-free false _or_ (λ _ → true)) p)

--------------------------------------------------------------------------------
-- ≤ is a partial order
-- ≤ coincides with the algebraic ordering with respect to the monoid structure.

≤-refl : (x : K A) → x ≤ x
≤-refl = idempotency

≤-antisym : (x y : K A) → x ≤ y → y ≤ x → x ≡ y
≤-antisym x y x≤y y≤x =
  x     ≡⟨ sym y≤x ⟩
  y ∪ x ≡⟨ com _ _ ⟩
  x ∪ y ≡⟨ x≤y ⟩
  y     ∎

≤-trans : (x y z : K A) → x ≤ y → y ≤ z → x ≤ z
≤-trans x y z x≤y y≤z = 
  x ∪ z       ≡⟨ cong (x ∪_) (sym y≤z) ⟩
  x ∪ y ∪ z   ≡⟨ assoc _ _ _ ⟩
  (x ∪ y) ∪ z ≡⟨ cong (_∪ z) x≤y ⟩
  y ∪ z       ≡⟨ y≤z ⟩
  z           ∎

∅-minimum : (x : K A) → ∅ ≤ x
∅-minimum = nl

≤-isAlgOrder : (x y z : K A) → x ∪ z ≡ y → x ≤ y
≤-isAlgOrder x y z p =
  x ∪ y       ≡⟨ cong (x ∪_) (sym p) ⟩
  x ∪ x ∪ z   ≡⟨ assoc _ _ _ ⟩
  (x ∪ x) ∪ z ≡⟨ cong (_∪ z) (idempotency _) ⟩
  x ∪ z       ≡⟨ p ⟩
  y           ∎
  
--------------------------------------------------------------------------------
-- (K A , ≤) is an order-theoretic lattice

∪-sup₁ : (x y : K A) → x ≤ x ∪ y
∪-sup₁ x y =
  x ∪ x ∪ y   ≡⟨ assoc _ _ _ ⟩
  (x ∪ x) ∪ y ≡⟨ cong (_∪ y) (idempotency _) ⟩
  x ∪ y       ∎ 

∪-sup₂ : (x y z : K A) → x ≤ z → y ≤ z → x ∪ y ≤ z
∪-sup₂ x y z x≤z y≤z =
  (x ∪ y) ∪ z ≡⟨ sym (assoc _ _ _) ⟩
  x ∪ y ∪ z   ≡⟨ cong (x ∪_) y≤z ⟩
  x ∪ z       ≡⟨ x≤z ⟩
  z           ∎ 

∪-∅-injective : (x y : K A) → x ∪ ∅ ≡ y ∪ ∅ → x ≡ y
∪-∅-injective x y p =
  x     ≡⟨ sym (nr x) ⟩
  x ∪ ∅ ≡⟨ p ⟩
  y ∪ ∅ ≡⟨ nr y ⟩
  y     ∎ 

∪-conicalˡ : (x y : K A) → x ∪ y ≡ ∅ → x ≡ ∅
∪-conicalˡ x y x∪y≡∅ =
  ≤-antisym x ∅ (≤-isAlgOrder _ _ y x∪y≡∅) (identityˡ x)

∪-conicalʳ : (x y : K A) → x ∪ y ≡ ∅ → y ≡ ∅
∪-conicalʳ x y x∪y≡∅ =
  ≤-antisym _ _ (≤-isAlgOrder y ∅ x (subst (_≡ ∅) (com x y) x∪y≡∅)) (identityˡ y ) 

--------------------------------------------------------------------------------
-- a ∉ ∅

a∉∅ : (a : A) → a ∉ ∅
a∉∅ a = lem refl
  where
    lem : ∀ {x} → x ≡ ∅ → a ∉ x
    lem p here        = [a]≢∅ p
    lem p (left a∈x)  = lem (∪-conicalˡ _ _ p) a∈x
    lem p (right a∈x) = lem (∪-conicalʳ _ _ p) a∈x
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

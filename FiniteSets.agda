{-# OPTIONS --safe --cubical #-}

module FiniteSets.FiniteSets where

open import Cubical.Core.Everything hiding (_∨_; _∧_)
open import Cubical.Foundations.HLevels hiding (hProp)
open import Cubical.Data.Everything

open import Level

open import FiniteSets.Kuratowski

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''

infixr 5 _∨_

record IsProp (A : Set ℓ) : Set ℓ where
  field
    pf : isProp A
open IsProp ⦃...⦄

IsPropIsProp : isProp (IsProp A)
IsPropIsProp x y i =
  record { pf = isPropIsProp (pf ⦃ x ⦄) (pf ⦃ y ⦄) i  }
  
hProp : (ℓ : Level) → Set (ℓ-suc ℓ)
hProp ℓ = Σ (Set ℓ) IsProp

it : ∀ {a} {A : Set a} ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x

instance 
  _ : IsProp ∥ A ∥
  _ = record { pf = propTruncIsProp }

  _ : IsProp ⊥
  _ = record { pf = isProp⊥ }

Σ-equiv : {B : A → Set ℓ'} {x y : Σ A B}
          → (p : fst x ≡ fst y)
          → PathP (λ i → B (p i)) (snd x) (snd y)
          → x ≡ y
Σ-equiv p q i = p i , q i

_∨_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A ∨ B = ∥ A ⊎ B ∥

∨-comm : A ∨ B ≡ B ∨ A
∨-comm ={!!}

∨-assoc : A ∨ (B ∨ C) ≡ (A ∨ B) ∨ C
∨-assoc = {!!}

∨-idem : A ∨ A ≡ A
∨-idem = {!!}

∨-identityˡ : ⊥ ∨ A ≡ A
∨-identityˡ = {!!}

∨-identityʳ : A ∨ ⊥ ≡ A
∨-identityʳ = {!!}

hPropIsSet : isSet (hProp ℓ)
hPropIsSet (A , Aprop) (B , Bprop) p q = {!!}

∈-IsProp : {A : Set} → A → K A → hProp 0ℓ
∈-IsProp a = elimK hPropIsSet
  (⊥ , it)
  (λ b → ∥ a ≡ b ∥ , it)
  (λ {_ _ (a∈x , _) (a∈y , _) → a∈x ∨ a∈y , it})
  (λ { _ (A , PA) → Σ-equiv ∨-identityˡ (toPathP (IsPropIsProp _ PA))})
  (λ { _ (A , PA) → Σ-equiv ∨-identityʳ (toPathP (IsPropIsProp _ PA))})
  (λ _ → Σ-equiv ∨-idem (toPathP (IsPropIsProp _ _)))
  (λ {_ _ _ (A , PA) (B , PB) (C  , PC) → Σ-equiv ∨-assoc (toPathP (IsPropIsProp _ _))})
  λ {_ _ (A , PA) (B , PB) → Σ-equiv ∨-comm (toPathP (IsPropIsProp _ _))}

_∈_ : {A : Set} → A → K A → Set
a ∈ x = fst (∈-IsProp a x)

_⊆_ : {A : Set} → K A → K A → Set
_⊆_ {A = A} x y = ∀ (a : A) → a ∈ x → a ∈ y

infix 5 _⊆_

{-# OPTIONS --cubical --allow-unsolved-metas #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

import Cubical.Foundations.Logic as L
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Empty 
open import Cubical.Relation.Nullary

open import FiniteSets.Kuratowski.Base

open import FiniteSets.Semilattice

private
  variable
    ℓ     : Level
    A B X : Set ℓ

K-Semilattice : Set ℓ → Semilattice ℓ
K-Semilattice A = record
  { A = K A
  ; _⊔_ = _∪_ 
  ; ⊥ = ∅
  ; isSemilattice = record
    { AisSet      = trunc
    ; ⊔-identityˡ = nl
    ; ⊔-identityʳ = nr
    ; ⊔-idem      = ∪-idem
    ; ⊔-assoc     = assoc
    ; ⊔-comm      = com }
  }
  where
    ∪-idem = elimKprop (trunc _ _) (nl ∅) idem λ x y x∪x=x y∪y=y → 
      (x ∪ y) ∪ x ∪ y   ≡⟨ assoc (x ∪ y) x y ⟩
      ((x ∪ y) ∪ x) ∪ y ≡⟨ cong (_∪ y) (cong (_∪ x) (com x y)) ⟩
      ((y ∪ x) ∪ x) ∪ y ≡⟨ cong (_∪ y) (sym (assoc y x x)) ⟩
      (y ∪ x ∪ x) ∪ y   ≡⟨ cong (_∪ y) (cong (y ∪_) x∪x=x) ⟩
      (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (com y x) ⟩
      (x ∪ y) ∪ y       ≡⟨ sym (assoc x y y) ⟩
      x ∪ y ∪ y         ≡⟨ cong (x ∪_) y∪y=y ⟩
      x ∪ y             ∎

KIsFree : ∀ (L : Semilattice ℓ)
           → (X → Semilattice.A L) → K X → (Semilattice.A L)
KIsFree L f = recK AisSet (Semilattice.⊥ L) f _⊔_
  ⊔-identityˡ ⊔-identityʳ (λ _ → ⊔-idem _) ⊔-assoc ⊔-comm
  where open Semilattice L

KPropRec : {X : Set} → (X → hProp) → (a : K X) → hProp
KPropRec f = KIsFree hProp-Semilattice f
  where open hProp

[a]≢∅ : {A : Set} {a : A} → ¬ [ a ] ≡ ∅
[a]≢∅ p = subst (fst ∘ KPropRec (λ a → ([ a ] ≡ ∅) , trunc _ _)) p p

[]-injective : {A : Set} {a b : A} → [ a ] ≡ [ b ] → ∥ a ≡ b ∥
[]-injective {a = a} eq = subst (fst ∘ KPropRec (λ b → a L.≡ₘ b)) eq ∣ refl ∣   

-- module _ {A : Set} where
--   open Properties 

-- --------------------------------------------------------------------------------
-- -- a ∉ ∅

--   a∉∅ : (a : A) → a ∉ ∅
--   a∉∅ a = lem refl
--     where
--       lem : ∀ {x} → x ≡ ∅ → a ∉ x
--       lem p here        = [a]≢∅ p
--       lem p (left a∈x)  = lem (⊔-conicalˡ _ _ p) a∈x
--       lem p (right a∈x) = lem (⊔-conicalʳ _ _ p) a∈x
--       lem p (sq a∈x a∈x₁ i) =
--         toPathP (isProp⊥ (transp (λ i → ⊥) i0 (g a∈x)) (g a∈x₁)) i
--           where g = lem p
        
--   a∈x⇒[x]∪x≡x : ∀ (a : A) x → a ∈ x → [ a ] ∪ x ≡ x
--   a∈x⇒[x]∪x≡x a = elim∈prop (trunc _ _) (idem a)
--     (λ x y a∈x a∪x≡x →
--       [ a ] ∪ x ∪ y   ≡⟨ assoc _ _ _ ⟩
--       ([ a ] ∪ x) ∪ y ≡⟨ cong (_∪ y) a∪x≡x ⟩
--       x ∪ y           ∎)
--     (λ x y a∈y a∪y≡y →
--       [ a ] ∪ x ∪ y   ≡⟨ cong ([ a ] ∪_) (com _ _) ⟩
--       [ a ] ∪ y ∪ x   ≡⟨ assoc _ _ _ ⟩
--       ([ a ] ∪ y) ∪ x ≡⟨ cong (_∪ x) a∪y≡y ⟩
--       y ∪ x           ≡⟨ com _ _ ⟩
--       x ∪ y           ∎)

--   y⊆x⇒y∪x≡x  : ∀ {x : K A} y → (y ⊆ x) → (y ∪ x) ≡ x
--   y⊆x⇒y∪x≡x {x = x} = elimKprop (λ p q → funExt λ f → trunc _ _ (p f) (q f))
--     (λ _ → nl _)
--     (λ a p → a∈x⇒[x]∪x≡x a _ (p a here) )
--     λ z y px py f →
--      (z ∪ y) ∪ x ≡⟨ sym (assoc _ _ _) ⟩
--      z ∪ y ∪ x   ≡⟨ cong (z ∪_) (py λ a a∈y → f a (right a∈y)) ⟩
--      z ∪ x       ≡⟨ px (λ a a∈z → f a (left a∈z) )  ⟩
--      x           ∎

--   y∪x≡x∧x∪y≡y : {x y : K A} → (y ∪ x ≡ x) × (x ∪ y ≡ y) → x ≡ y
--   y∪x≡x∧x∪y≡y (y∪x≡x , x∪y≡y) = ≤-antisym _ _ x∪y≡y y∪x≡x

-- setExt : {A : Set} {x y : K A}
--                 → Iso (x ≡ y) (∀ (a : A) → a ∈ x ≡ a ∈ y)
-- setExt {A = A} {x} {y} = {!!}

-- module Decidable (A : Set)(_≟_ : {A : Set} (x y : A) → Dec ∥ x ≡ y ∥) where

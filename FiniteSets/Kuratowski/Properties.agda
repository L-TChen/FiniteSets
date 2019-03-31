{-# OPTIONS --cubical --allow-unsolved-metas #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

import Cubical.Foundations.Logic as L hiding (⊔-idem)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Empty 

open import FiniteSets.Kuratowski.Base renaming ([_] to K[_])

open import FiniteSets.Semilattice

private
  variable
    ℓ     : Level
    A B X : Set ℓ

KAisSet : isSet (K X)
KAisSet = trunc

module Lattice where
  ∪-idem : (x : K X) → x ∪ x ≡ x
  ∪-idem = elimKprop (trunc _ _) (nl ∅) idem λ x y x∪x=x y∪y=y → 
    (x ∪ y) ∪ x ∪ y   ≡⟨ assoc (x ∪ y) x y ⟩
    ((x ∪ y) ∪ x) ∪ y ≡⟨ cong (_∪ y) (cong (_∪ x) (com x y)) ⟩
    ((y ∪ x) ∪ x) ∪ y ≡⟨ cong (_∪ y) (sym (assoc y x x)) ⟩
    (y ∪ x ∪ x) ∪ y   ≡⟨ cong (_∪ y) (cong (y ∪_) x∪x=x) ⟩
    (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (com y x) ⟩
    (x ∪ y) ∪ y       ≡⟨ sym (assoc x y y) ⟩
    x ∪ y ∪ y         ≡⟨ cong (x ∪_) y∪y=y ⟩
    x ∪ y             ∎

  KSemilattice : Set ℓ → Semilattice ℓ
  KSemilattice X = record
    { A = K X
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
open Lattice using (KSemilattice)

KIsFree : (L : Semilattice ℓ) → (X → Semilattice.A L) → K X → (Semilattice.A L)
KIsFree L f = recK AisSet (Semilattice.⊥ L) f _⊔_
  ⊔-identityˡ ⊔-identityʳ (λ _ → ⊔-idem _) ⊔-assoc ⊔-comm
  where open Semilattice L

KPropRec : (X → hProp) → (a : K X) → hProp
KPropRec f = KIsFree hProp-Semilattice f
  where open hProp

module _ {A : Set} where
  open L
  [a]≢∅ : {a : A} → [ K.[ a ] ≢ₖ ∅ ]
  [a]≢∅ p = subst (fst ∘ KPropRec (λ a → (K.[ a ] ≡ ∅) , trunc _ _)) p p

  []-injective : {A : Set} {a b : A} → K.[ a ] ≡ₖ K.[ b ] ≡ a ≡ₘ b 
  []-injective {a = a} {b} =
    ⇒∶ (λ eq → subst (fst ∘ KPropRec (λ b → a L.≡ₘ b)) eq ∣ refl ∣)
    ⇐∶ elimPropTrunc (λ _ → trunc K[ a ] K[ b ]) (cong K[_])

  open Properties (KSemilattice A)

--------------------------------------------------------------------------------
-- a ∉ ∅

  a∉∅ : (a : A) → a ∉′ ∅
  a∉∅ a = lem refl 
    where
      lem : ∀ {a x} → x ≡ ∅ → a ∉′ x 
      lem x≡∅ here = [a]≢∅ x≡∅
      lem x≡∅ (left a∈x)  = lem (⊔-conicalˡ _ _ x≡∅) a∈x
      lem x≡∅ (right a∈x) = lem (⊔-conicalʳ _ _ x≡∅) a∈x
      lem {x} x≡∅ (sq a∈x a∈x₁ i) =
        toPathP (isProp⊥ (transp (λ i → Cubical.Data.Empty.⊥) i0 (g a∈x)) (g a∈x₁)) i
          where g = lem x≡∅
          
  a∈x⇒[x]∪x≡x : ∀ (a : A) x → [ a ∈ x ] → [ (K.[ a ] ∪ x) ≡ₖ x ]
  a∈x⇒[x]∪x≡x a = elim∈prop (trunc _ _) (idem a)
    (λ x y a∈x a∪x≡x →
      K.[ a ] ∪ x ∪ y   ≡⟨ assoc _ _ _ ⟩
      (K.[ a ] ∪ x) ∪ y ≡⟨ cong (_∪ y) a∪x≡x ⟩
      x ∪ y             ∎)
    (λ x y a∈y a∪y≡y →
      K.[ a ] ∪ x ∪ y   ≡⟨ cong (K.[ a ] ∪_) (com _ _) ⟩
      K.[ a ] ∪ y ∪ x   ≡⟨ assoc _ _ _ ⟩
      (K.[ a ] ∪ y) ∪ x ≡⟨ cong (_∪ x) a∪y≡y ⟩
      y ∪ x             ≡⟨ com _ _ ⟩
      x ∪ y             ∎)

  y⊆x⇒y∪x≡x  : ∀ {x y : K A} → (y ⊆ x) ≡ (y ∪ x) ≡ₖ x
  y⊆x⇒y∪x≡x {x = x} {y} =
    ⇒∶ elimKprop {P = λ z → [ z ⊆ x ⇒ (z ∪ x ≡ₖ x) ]} (λ p q → funExt λ f → trunc _ _ (p f ) (q f))
    (λ _ → nl _)
    (λ a p → a∈x⇒[x]∪x≡x a x (p a here))
    (λ u v pu pv f →
      (u ∪ v) ∪ x ≡⟨ sym (assoc _ _ _) ⟩
      u ∪ (v ∪ x) ≡⟨ cong (u ∪_) (pv (λ x z → f x (right z))) ⟩
      u ∪ x       ≡⟨ pu (λ x z → f x (left z)) ⟩
      x           ∎) y
    ⇐∶ λ y∪x≡x a a∈y → subst (λ z → [ a ∈ z ]) y∪x≡x (left a∈y) 

  y∪x≡x∧x∪y≡y : {x y : K A} → (y ∪ x ≡ₖ x) ⊓ (x ∪ y ≡ₖ y) ≡ x ≡ₖ y
  y∪x≡x∧x∪y≡y {x} {y} =
    ⇒∶ (λ { (y≤x , x≤y) → ≤-antisym x≤y y≤x })
    ⇐∶ λ x≡y → sym (cong (_∪ x) x≡y) ∙ ⊔-idem _  , cong (_∪ y) x≡y ∙ ⊔-idem _
    where open Semilattice (KSemilattice A)

  setExt : {x y : K A} → (x ≡ₖ y) ≡ (∀[ a ∶ A ] a ∈ y ⇔ a ∈ x)
  setExt {x} {y} =
    x ≡ₖ y                      ≡⟨ sym (y∪x≡x∧x∪y≡y) ⟩
    (y ∪ x ≡ₖ x) ⊓ (x ∪ y ≡ₖ y) ≡⟨ cong₂ (_⊓_) (sym y⊆x⇒y∪x≡x) (sym y⊆x⇒y∪x≡x)  ⟩
    (y ⊆ x) ⊓ (x ⊆ y)           ≡⟨ cong₂ (_⊓_) (hProp≡ refl) (hProp≡ refl) ⟩ 
    (∀[ a ∶ A ] a ∈ y ⇒ a ∈ x) ⊓ (∀[ a ∶ A ] a ∈ x ⇒ a ∈ y)
      ≡⟨ ⊓-∀-comm (λ a → a ∈ y ⇒ a ∈ x) (λ a → a ∈ x ⇒ a ∈ y) ⟩
    (∀[ a ∶ A ] (a ∈ y ⇒ a ∈ x) ⊓ (a ∈ x ⇒ a ∈ y)) ≡⟨ hProp≡ refl ⟩ 
    (∀[ a ∶ A ] (a ∈ y ⇔ a ∈ x))                   ∎ 

-- module Decidable (A : Set)(_≟_ : {A : Set} (x y : A) → Dec ∥ x ≡ y ∥) where

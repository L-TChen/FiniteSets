{-# OPTIONS --cubical --safe #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Logic as L hiding (⊔-idem)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Empty 

open import Cubical.Relation.Nullary

open import FiniteSets.Kuratowski.Base renaming ([_] to K[_])

open import FiniteSets.Semilattice

private
  variable
    ℓ : Level
--------------------------------------------------------------------------------
-- K A is a ∪-semilattice.

module Lattice where
  variable
    A : Set ℓ
  ∪-idem : (x : K A) → x ∪ x ≡ x
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
  KSemilattice A = record
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
open Lattice using (KSemilattice)

module _ {A : Set}where    
  open Properties (KSemilattice A)

  -- Two definitions of membership relations are the same. 
  ∈⇒∈ₚ : ∀ {a : A} {x} → [ a ∈ x ⇒ a ∈ₚ x ]
  ∈⇒∈ₚ {a = a} {x = x} a∈x = elim∈prop {P = λ {y} _ → [ a ∈ₚ y ]}
    (λ {y} → snd (a ∈ₚ y)) ∣ refl ∣
    (λ _ _ _ → L.inl) (λ _ _ _ → L.inr) x a∈x
    
  ∈ₚ⇒∈ : ∀ {a} {x : K A} → [ a ∈ₚ x ⇒ a ∈ x ]
  ∈ₚ⇒∈ {a} {x} a∈x = elimKprop {P = λ y → [ (a ∈ₚ y) ⇒ a ∈ y ]} (propPi λ _ → snd (a ∈ _))
    (λ ()) (λ b a≡b → substₚ (λ c → a ∈ K[ c ]) a≡b here)
    (λ y z py pz pyz → elimPropTrunc (λ _ → sq)
      (elim-⊎ (λ a∈y → left (py a∈y)) λ a∈z → right (pz a∈z)) pyz) x a∈x

  ∈≡∈ₚ : ∀ {a : A}{x : K A} → a ∈ x ≡ a ∈ₚ x
  ∈≡∈ₚ = ⇔toPath ∈⇒∈ₚ ∈ₚ⇒∈

  [a]≢∅ : {a : A} → [ K.[ a ] ≢ₖ ∅ ]
  [a]≢∅ p = subst (fst ∘ KPropRec (λ a → (K.[ a ] ≡ ∅) , trunc _ _)) p p

  -- not used 
  []-injective : {A : Set} {a b : A} → K.[ a ] ≡ₖ K.[ b ] ≡ a ≡ₚ b 
  []-injective {a = a} {b} =
    ⇒∶ (λ eq → subst (fst ∘ a ∈ₚ_) eq ∣ refl ∣)
    ⇐∶ elimPropTrunc (λ _ → trunc K[ a ] K[ b ]) (cong K[_])
--------------------------------------------------------------------------------
-- a ∉ ∅

  a∉∅ : (a : A) → [ a ∉ ∅ ]
  a∉∅ a = lem refl 
    where
      lem : ∀ {a x} → x ≡ ∅ → [ a ∉ x ]
      lem {a} {x} x≡∅ a∈x = elim∈prop {P = λ {y} b∈y → y ≡ ∅ → [ a ∉ y ]}
        (propPi (λ _ → snd (a ∉ _))) (λ [a]≡∅ _ → [a]≢∅ [a]≡∅)
        (λ _ _ a∈y h y∪z≡∅ _ → h (⊔-conicalˡ _ _ y∪z≡∅) a∈y)
        (λ _ _ a∈z h y∪z≡∅ _ → h (⊔-conicalʳ _ _ y∪z≡∅) a∈z) x a∈x x≡∅ a∈x
          
  a∈x⇒[a]∪x≡x : ∀ (a : A) x → [ a ∈ x ] → K.[ a ] ∪ x ≡ x
  a∈x⇒[a]∪x≡x a = elim∈prop (trunc _ _) (idem a)
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
    ⇒∶ elimKprop {P = λ z → [ z ⊆ x ⇒ (z ∪ x ≡ₖ x) ]}
    (λ p q → funExt λ f → trunc _ _ (p f ) (q f))
    (λ _ → nl _)
    (λ a p → a∈x⇒[a]∪x≡x a x (p a here))
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
    x ≡ₖ y
      ≡⟨ sym (y∪x≡x∧x∪y≡y) ⟩
    (y ∪ x ≡ₖ x) ⊓ (x ∪ y ≡ₖ y)
      ≡⟨ cong₂ (_⊓_) (sym y⊆x⇒y∪x≡x) (sym y⊆x⇒y∪x≡x)  ⟩
    (y ⊆ x) ⊓ (x ⊆ y)
      ≡⟨ cong₂ {y = ∀[ a ∶ A ] a ∈ y ⇒ a ∈ x} _⊓_ refl {v = ∀[ a ∶ A ] a ∈ x ⇒ a ∈ y} refl ⟩
    (∀[ a ∶ A ] a ∈ y ⇒ a ∈ x) ⊓ (∀[ a ∶ A ] a ∈ x ⇒ a ∈ y)
      ≡⟨ ⊓-∀-distrib (λ a → a ∈ y ⇒ a ∈ x) (λ a → a ∈ x ⇒ a ∈ y) ⟩
    (∀[ a ∶ A ] (a ∈ y ⇔ a ∈ x))                   ∎


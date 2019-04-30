{-# OPTIONS --safe --cubical #-}

module FiniteSets.Semilattice where
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

record IsSemilattice (A : Set ℓ) (_⊔_ : A → A → A) (⊥ : A) : Set ℓ where
  field
    AisSet      : isSet A
    ⊔-identityˡ : ∀ x → ⊥ ⊔ x ≡ x
    ⊔-identityʳ : ∀ x → x ⊔ ⊥ ≡ x
    ⊔-idem      : ∀ x → x ⊔ x ≡ x
    ⊔-assoc     : ∀ x y z → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
    ⊔-comm      : ∀ x y → x ⊔ y ≡ y ⊔ x

record Semilattice (ℓ : Level) : Set (ℓ-suc ℓ) where
  field
    A             : Set ℓ
    _⊔_           : A → A → A
    ⊥             : A
    isSemilattice : IsSemilattice A _⊔_ ⊥
  open IsSemilattice isSemilattice public
      
  _≤_ : A → A → Set ℓ
  x ≤ y = x ⊔ y ≡ y
  infixr 7 _⊔_
  infix  5 _≤_

module Bool where
  open import Cubical.Data.Bool
  
  Or-Semilattice : Semilattice ℓ-zero
  Or-Semilattice = record
    { A   = Bool
    ; _⊔_ = _or_
    ; ⊥ = false
    ; isSemilattice = record
      { AisSet      = isSetBool
      ; ⊔-identityˡ = or-identityˡ
      ; ⊔-identityʳ = or-identityʳ
      ; ⊔-idem      = or-idem 
      ; ⊔-assoc     = or-assoc
      ; ⊔-comm      = or-comm
      }
    }

module hProp where
  import Cubical.Foundations.Logic as L
  import Cubical.Foundations.HLevels as L
  
  hProp-Semilattice : Semilattice _
  hProp-Semilattice = record
    { A   = L.hProp
    ; _⊔_ = L._⊔_
    ; ⊥   = L.⊥
    ; isSemilattice = record
      { AisSet      = L.isSetHProp
      ; ⊔-identityˡ = L.⊔-identityˡ
      ; ⊔-identityʳ = L.⊔-identityʳ
      ; ⊔-idem      = L.⊔-idem
      ; ⊔-assoc     = L.⊔-assoc
      ; ⊔-comm      = L.⊔-comm
      }
    }

module Properties {ℓ} (L : Semilattice ℓ) where
  open Semilattice L
  
  ≤-refl : (x : A) → x ≤ x
  ≤-refl = ⊔-idem

  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym {x = x} {y} x≤y y≤x =
    x     ≡⟨ sym y≤x ⟩
    y ⊔ x ≡⟨ ⊔-comm _ _ ⟩
    x ⊔ y ≡⟨ x≤y ⟩
    y     ∎

  ≤-trans : (x y z : A) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z x≤y y≤z = 
    x ⊔ z       ≡⟨ cong (x ⊔_) (sym y≤z) ⟩
    x ⊔ y ⊔ z   ≡⟨ ⊔-assoc _ _ _ ⟩
    (x ⊔ y) ⊔ z ≡⟨ cong (_⊔ z) x≤y ⟩
    y ⊔ z       ≡⟨ y≤z ⟩
    z           ∎

  ⊥-minimum : (x : A) → ⊥ ≤ x
  ⊥-minimum = ⊔-identityˡ

  ≤-isAlgOrder : (x y z : A) → x ⊔ z ≡ y → x ≤ y
  ≤-isAlgOrder x y z p =
    x ⊔ y       ≡⟨ cong (x ⊔_) (sym p) ⟩
    x ⊔ x ⊔ z   ≡⟨ ⊔-assoc _ _ _ ⟩
    (x ⊔ x) ⊔ z ≡⟨ cong (_⊔ z) (⊔-idem _) ⟩
    x ⊔ z       ≡⟨ p ⟩
    y           ∎
--------------------------------------------------------------------------------
-- (A , ≤) is an order-theoretic lattice

  ⊔-sup₁ : (x y : A) → x ≤ x ⊔ y
  ⊔-sup₁ x y =
    x ⊔ x ⊔ y   ≡⟨ ⊔-assoc _ _ _ ⟩
    (x ⊔ x) ⊔ y ≡⟨ cong (_⊔ y) (⊔-idem _) ⟩
    x ⊔ y       ∎ 

  ⊔-sup₂ : (x y z : A) → x ≤ z → y ≤ z → x ⊔ y ≤ z
  ⊔-sup₂ x y z x≤z y≤z =
    (x ⊔ y) ⊔ z ≡⟨ sym (⊔-assoc _ _ _) ⟩
    x ⊔ y ⊔ z   ≡⟨ cong (x ⊔_) y≤z ⟩
    x ⊔ z       ≡⟨ x≤z ⟩
    z           ∎ 

  ⊔-∅-injective : (x y : A) → x ⊔ ⊥ ≡ y ⊔ ⊥ → x ≡ y
  ⊔-∅-injective x y p =
    x     ≡⟨ sym (⊔-identityʳ _) ⟩
    x ⊔ ⊥ ≡⟨ p ⟩
    y ⊔ ⊥ ≡⟨ ⊔-identityʳ _ ⟩
    y     ∎ 

  ⊔-conicalˡ : (x y : A) → x ⊔ y ≡ ⊥ → x ≡ ⊥
  ⊔-conicalˡ x y x⊔y≡⊥ =
    ≤-antisym (≤-isAlgOrder _ _ y x⊔y≡⊥) (⊔-identityˡ x)

  ⊔-conicalʳ : (x y : A) → x ⊔ y ≡ ⊥ → y ≡ ⊥
  ⊔-conicalʳ x y x⊔y≡⊥ = ⊔-conicalˡ y x (subst (λ z → z ≡ ⊥) (⊔-comm x y) x⊔y≡⊥)

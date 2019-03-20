{-# OPTIONS --safe --cubical #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary

open import FiniteSets.Kuratowski.Base

private
  variable
    ℓ  : Level
    A : Set ℓ

[a]≢∅ : {a : A} → ¬ [ a ] ≡ ∅
[a]≢∅ p = true≢false (cong nontrivial p)
  where
    nontrivial : K A → Bool
    nontrivial = elimK BoolIsSet false (λ _ → true) (λ _ _ → _or_)
      (λ _ → or-identityˡ)
      (λ _ → or-identityʳ)
      (λ _ → or-idem _)
      (λ _ _ _ → or-assoc)
      (λ _ _ → or-comm)

{-
[]-injective : (a b : A) → [ a ] ≡ [ b ] → a ≡ b
[]-injective a b = {!!}
-}

∪-idem : (x : K A) → x ∪ x ≡ x
∪-idem {A = A} = elimKprop (trunc _ _) (nl ∅) idem λ x y x∪x=x y∪y=y → 
    (x ∪ y) ∪ x ∪ y ≡⟨ assoc (x ∪ y) x y ⟩
    ((x ∪ y) ∪ x) ∪ y   ≡⟨ cong (_∪ y) (cong (_∪ x) (com x y)) ⟩
    ((y ∪ x) ∪ x) ∪ y   ≡⟨ cong (_∪ y) (sym (assoc y x x)) ⟩
    (y ∪ x ∪ x) ∪ y ≡⟨ cong (_∪ y) (cong (y ∪_) x∪x=x) ⟩
    (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (com y x) ⟩
    (x ∪ y) ∪ y       ≡⟨ sym (assoc x y y) ⟩
    x ∪ y ∪ y     ≡⟨ cong (x ∪_) y∪y=y ⟩
    x ∪ y           ∎

--------------------------------------------------------------------------------
-- ≤ is a partial order
-- ≤ coincides with the algebraic ordering with respect to the monoid structure.

≤-refl : (x : K A) → x ≤ x
≤-refl = ∪-idem

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
  (x ∪ x) ∪ z ≡⟨ cong (_∪ z) (∪-idem _) ⟩
  x ∪ z       ≡⟨ p ⟩
  y           ∎
  
--------------------------------------------------------------------------------
-- (K A , ≤) is an order-theoretic lattice

∪-sup₁ : (x y : K A) → x ≤ x ∪ y
∪-sup₁ x y =
  x ∪ x ∪ y   ≡⟨ assoc _ _ _ ⟩
  (x ∪ x) ∪ y ≡⟨ cong (_∪ y) (∪-idem _) ⟩
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

x∪y≡∅ˡ : (x y : K A) → x ∪ y ≡ ∅ → x ≡ ∅
x∪y≡∅ˡ x y x∪y≡∅ =
  ≤-antisym x ∅ (≤-isAlgOrder _ _ y x∪y≡∅) (nl x)

x∪y≡∅ʳ : (x y : K A) → x ∪ y ≡ ∅ → y ≡ ∅
x∪y≡∅ʳ x y x∪y≡∅ = x∪y≡∅ˡ y x (subst (λ x → x ≡ ∅) (com _ _) x∪y≡∅)

--------------------------------------------------------------------------------
-- a ∉ ∅

a∉∅ : (a : A) → a ∉ ∅
a∉∅ a = lem a refl
  where
    lem : ∀ (a : A) {x} → x ≡ ∅ → a ∉ x
    lem a p (here a≡b)  = [a]≢∅ p
    lem a p (left a∈x)  = lem a (x∪y≡∅ˡ _ _ p) a∈x
    lem a p (right a∈x) = lem a (x∪y≡∅ʳ _ _ p) a∈x

a∈x⇒[x]∪x≡x : ∀ (a : A) x → ∥ a ∈ x ∥ → [ a ] ∪ x ≡ x
a∈x⇒[x]∪x≡x a _ ∣ here {b = b} p ∣ =
   [ a ] ∪ [ b ]  ≡⟨ cong (λ a → [ a ] ∪ [ b ]) p ⟩
   [ b ] ∪ [ b ] ≡⟨ idem b ⟩
   [ b ]          ∎
a∈x⇒[x]∪x≡x a _ ∣ left {x} {y} a∈x ∣ =
  [ a ] ∪ x ∪ y   ≡⟨ assoc _ x y ⟩
  ([ a ] ∪ x) ∪ y ≡⟨ cong (_∪ y) (a∈x⇒[x]∪x≡x a x ∣ a∈x ∣) ⟩
  x ∪ y           ∎
a∈x⇒[x]∪x≡x a _ ∣ right {x} {y} a∈y ∣ =
   [ a ] ∪ x ∪ y ≡⟨ cong ([ a ] ∪_) (com _ _) ⟩
   [ a ] ∪ y ∪ x ≡⟨ assoc _ _ _ ⟩
   ([ a ] ∪ y) ∪ x   ≡⟨ cong (_∪ x) (a∈x⇒[x]∪x≡x a y ∣ a∈y ∣) ⟩
   y ∪ x           ≡⟨ com _ _ ⟩
   x ∪ y           ∎
a∈x⇒[x]∪x≡x a x (squash a∈x a∈x₁ i) = trunc _ _ (a∈x⇒[x]∪x≡x a x a∈x) (a∈x⇒[x]∪x≡x a x a∈x₁) i

y⊆x⇒y∪x≡x  : ∀ {x : K A} y → (y ⊆ x) → (y ∪ x) ≡ x
y⊆x⇒y∪x≡x {x = x} = elimKprop (λ p q → funExt λ f → trunc _ _ (p f) (q f))
  (λ _ → nl _)
  (λ a p → a∈x⇒[x]∪x≡x a _ ∣ p a (here refl) ∣ )
  λ z y px py f →
   (z ∪ y) ∪ x ≡⟨ sym (assoc _ _ _) ⟩
   z ∪ y ∪ x   ≡⟨ cong (z ∪_) (py λ a a∈y → f a (right a∈y)) ⟩
   z ∪ x       ≡⟨  px (λ a a∈z → f a (left a∈z) )  ⟩
   x           ∎

y∪x≡x∧x∪y≡y : {x y : K A} → (y ∪ x ≡ x) × (x ∪ y ≡ y) → x ≡ y
y∪x≡x∧x∪y≡y {x = x} {y} (y∪x≡x , x∪y≡y) =
  x     ≡⟨ sym y∪x≡x ⟩
  y ∪ x ≡⟨ com _ _ ⟩
  x ∪ y ≡⟨ x∪y≡y ⟩
  y     ∎ 

{-
extensionality : {A : Set ℓ} {x y : K A}
                 → Lift _ (x ≡ y) ≡ ∀ (a : A) → a ∈ x ≡ a ∈ y
extensionality {A = A} {x} {y} = 
  Lift _ (x ≡ y)                     ≡⟨ cong (Lift _) {!!} ⟩
  Lift _ ((y ∪ x ≡ x) × (x ∪ y ≡ y)) ≡⟨ {!!} ⟩
  (∀ (a : A) → a ∈ x ≡ a ∈ y)        ∎ 
-}

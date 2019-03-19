{-# OPTIONS --safe --cubical #-}

module FiniteSets.Kuratowski.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
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

a∈x⇒[x]∪x≡x : ∀ (a : A) x → ∥ a ∈ x ∥ → [ a ] ∪ x ≡ x
a∈x⇒[x]∪x≡x a _ ∣ here {b = b} p ∣ =
   [ a ] ∪ [ b ]  ≡⟨ cong (λ a → [ a ] ∪ [ b ]) p ⟩
   [ b ] ∪ [ b ] ≡⟨ idem b ⟩
   [ b ]          ∎
a∈x⇒[x]∪x≡x a _ ∣ left {x} {y} a∈x ∣ =
  [ a ] ∪ (x ∪ y) ≡⟨ assoc _ x y ⟩
  [ a ] ∪ x ∪ y   ≡⟨ cong (_∪ y) (a∈x⇒[x]∪x≡x a x ∣ a∈x ∣) ⟩
  x ∪ y           ∎
a∈x⇒[x]∪x≡x a _ ∣ right {x} {y} a∈y ∣ =
   [ a ] ∪ (x ∪ y) ≡⟨ cong ([ a ] ∪_) (com _ _) ⟩
   [ a ] ∪ (y ∪ x) ≡⟨ assoc _ _ _ ⟩
   [ a ] ∪ y ∪ x   ≡⟨ cong (_∪ x) (a∈x⇒[x]∪x≡x a y ∣ a∈y ∣) ⟩
   y ∪ x           ≡⟨ com _ _ ⟩
   x ∪ y           ∎
a∈x⇒[x]∪x≡x a x (squash a∈x a∈x₁ i) = trunc _ _ (a∈x⇒[x]∪x≡x a x a∈x) (a∈x⇒[x]∪x≡x a x a∈x₁) i

y⊆x⇒y∪x≡x  : ∀ {x : K A} y → (y ⊆ x) → (y ∪ x) ≡ x
y⊆x⇒y∪x≡x {x = x} = elimKprop (λ p q → funExt λ f → trunc _ _ (p f) (q f))
  (λ _ → nl _)
  (λ a p → a∈x⇒[x]∪x≡x a _ (p a ∣ here refl ∣))
  λ z y px py f →
   z ∪ y ∪ x   ≡⟨ sym (assoc _ _ _) ⟩
   z ∪ (y ∪ x) ≡⟨ cong (z ∪_) (py λ a → elimPropTrunc (λ _ → propTruncIsProp) λ a∈y → f a ∣ right a∈y ∣) ⟩
   z ∪ x       ≡⟨  px (λ a → elimPropTrunc (λ _ → propTruncIsProp) λ a∈z → f a ∣ left a∈z ∣)  ⟩
   x           ∎

y∪x≡x∧x∪y≡y : {x y : K A} → y ∪ x ≡ x → x ∪ y ≡ y → x ≡ y
y∪x≡x∧x∪y≡y {x = x} {y} y∪x≡x x∪y≡y =
  x     ≡⟨ sym y∪x≡x ⟩
  y ∪ x ≡⟨ com _ _ ⟩
  x ∪ y ≡⟨ x∪y≡y ⟩
  y     ∎ 

extensionality : {A : Set ℓ} {x y : K A}
                 → Lift _ (x ≡ y) ≡ ∀ (a : A) → a ∈ x ≡ a ∈ y
extensionality {A = A} {x} {y} = 
  Lift _ (x ≡ y)                     ≡⟨ cong (Lift _) {!!} ⟩
  Lift _ ((y ∪ x ≡ x) × (x ∪ y ≡ y)) ≡⟨ {!!} ⟩
  (∀ (a : A) → a ∈ x ≡ a ∈ y)        ∎ 

{-# OPTIONS --safe --cubical #-}

module FiniteSets.List.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Level

import FiniteSets.Kuratowski as K
open import FiniteSets.List

private
  variable
    ℓ  : Level
    A  : Set ℓ
    
++-identityˡ : (xs : L A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : (xs : L A) → xs ++ [] ≡ xs
++-identityʳ = elimLprop (truncl _ _) refl (λ a _ p → (cong (a ∷_) p))

++-assoc : (ys zs xs : L A)
          → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
++-assoc ys zs = elimLprop (truncl _ _) refl λ a xs p → cong (a ∷_) p 

++-idem : (x : A) → [ x ] ++ [ x ] ≡ [ x ]
++-idem x = dupl x []

[a]++xs≡xs++[a] : ∀ xs (a : A) → a ∷ xs ≡ xs ++ [ a ]
[a]++xs≡xs++[a] = elimLprop (propPi (λ _ → truncl _ _)) (λ _ → refl) λ a xs pxs b →
  b ∷ a ∷ xs        ≡⟨ coml _ _ _ ⟩
  a ∷ b ∷ xs        ≡⟨ cong (a ∷_) (pxs b) ⟩
  a ∷ (xs ++ [ b ]) ≡⟨ refl ⟩
  a ∷ xs ++ [ b ]   ∎
  
++-comm : ∀ xs → (ys : L A) → xs ++ ys ≡ ys ++ xs
++-comm = elimLprop (propPi (λ _ → truncl _ _)) (λ ys → sym (++-identityʳ ys)) λ a xs pxs ys →
  a ∷ (xs ++ ys)      ≡⟨ cong (a ∷_) (pxs ys) ⟩
  a ∷ (ys ++ xs)      ≡⟨ [a]++xs≡xs++[a] (ys ++ xs) a ⟩
  (ys ++ xs) ++ [ a ] ≡⟨ sym (++-assoc _ _ ys) ⟩
  ys ++ xs ++ [ a ]   ≡⟨ cong (ys ++_) (sym ([a]++xs≡xs++[a] _ _)) ⟩
  ys ++ a ∷ xs        ∎
  
-- K≃L : K A ≃ L A
-- K≃L = {!!}
--   where
--     f : K A → L A
--     f = {!!}
--     g : L A → K A
--     g = {!!}
--     h : L A → K A
--     h = {!!}

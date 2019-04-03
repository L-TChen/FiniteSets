{-# OPTIONS --safe --cubical #-}

module FiniteSets.List.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import FiniteSets.Semilattice
open import FiniteSets.List
open import FiniteSets.Kuratowski as K renaming ([_] to K[_] ; trunc to trunck ; com to comk)

private
  variable
    ℓ  : Level
    A  : Set ℓ

module Lattice where 
  ++-identityʳ : (xs : L A) → xs ++ [] ≡ xs
  ++-identityʳ = elimLprop (trunc _ _) refl (λ a _ p → (cong (a ∷_) p))

  ++-assoc : (ys zs xs : L A)
            → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
  ++-assoc ys zs = elimLprop (trunc _ _) refl λ a xs p → cong (a ∷_) p 

  [a]++xs≡xs++[a] : ∀ xs (a : A) → a ∷ xs ≡ xs ++ [ a ]
  [a]++xs≡xs++[a] = elimLprop (propPi (λ _ → trunc _ _)) (λ _ → refl) λ a xs pxs b →
    b ∷ a ∷ xs        ≡⟨ com _ _ _ ⟩
    a ∷ b ∷ xs        ≡⟨ cong (a ∷_) (pxs b) ⟩
    a ∷ (xs ++ [ b ]) ≡⟨ refl ⟩
    a ∷ xs ++ [ b ]   ∎

  ++-comm : ∀ xs → (ys : L A) → xs ++ ys ≡ ys ++ xs
  ++-comm = elimLprop (propPi (λ _ → trunc _ _)) (λ ys → sym (++-identityʳ ys)) λ a xs pxs ys →
    a ∷ (xs ++ ys)      ≡⟨ cong (a ∷_) (pxs ys) ⟩
    a ∷ (ys ++ xs)      ≡⟨ [a]++xs≡xs++[a] (ys ++ xs) a ⟩
    (ys ++ xs) ++ [ a ] ≡⟨ sym (++-assoc _ _ ys) ⟩
    ys ++ xs ++ [ a ]   ≡⟨ cong (ys ++_) (sym ([a]++xs≡xs++[a] _ _)) ⟩
    ys ++ a ∷ xs        ∎

  ++-idem : (xs : L A) → xs ++ xs ≡ xs
  ++-idem = elimLprop (trunc _ _) refl λ a xs pxs →
    (a ∷ xs) ++ a ∷ xs ≡⟨ refl ⟩
    a ∷ (xs ++ a ∷ xs) ≡⟨ cong (a ∷_) (++-comm xs (a ∷ xs)) ⟩
    a ∷ a ∷ (xs ++ xs) ≡⟨ dup a _ ⟩
    a ∷ xs ++ xs       ≡⟨ cong (a ∷_) pxs ⟩
    a ∷ xs             ∎

  L-Semilattice : Set ℓ → Semilattice ℓ 
  L-Semilattice A = record
    { A = L A
    ; _⊔_ = _++_
    ; ⊥ = []
    ; isSemilattice = record
      { AisSet = trunc
      ; ⊔-identityˡ = λ _ → refl
      ; ⊔-identityʳ = ++-identityʳ
      ; ⊔-idem = ++-idem
      ; ⊔-assoc = λ xs ys zs → ++-assoc ys zs xs
      ; ⊔-comm = ++-comm
      } }
open Lattice using (L-Semilattice)

K≡L : (A : Set ℓ) → K A ≡ L A
K≡L A = isoToPath (iso f g f∘g=id g∘f=id)
  where
    f : K A → L A
    f = recK trunc [] [_] _⊔_ ⊔-identityˡ ⊔-identityʳ (⊔-idem ∘ [_]) ⊔-assoc ⊔-comm
      where open Semilattice (L-Semilattice A)

    g : L A → K A
    g = recL trunck ∅ (λ a x → K[ a ] ∪ x)
      (λ a x   → assoc _ _ _ ∙ cong (_∪ x) (idem a))
      (λ a b x → assoc _ _ _ ∙ cong (_∪ x) (comk _ _) ∙ sym (assoc _ _ _))
 
    g-homo : ∀ xs ys → g (xs ++ ys) ≡ g xs ∪ g ys
    g-homo = elimLprop (propPi λ _ → trunck _ _) (λ ys → sym (nl (g ys)))
      λ a xs f ys →
        K[ a ] ∪ g (xs ++ ys)  ≡⟨ cong (K[ a ] ∪_) (f ys) ⟩
        K[ a ] ∪ (g xs ∪ g ys) ≡⟨ assoc _ _ _ ⟩
        g (a ∷ xs) ∪ g ys      ∎ 
      
    f∘g=id : section f g
    f∘g=id = elimLprop (trunc _ _) refl λ a xs → cong (a ∷_)
    
    g∘f=id : retract f g
    g∘f=id = elimKprop (trunck _ _) refl (λ _ → nr _)
      λ x y g∘fx≡x g∘fy≡y →
        g (f (x ∪ y))     ≡⟨ refl ⟩
        g (f x ++ f y)    ≡⟨ g-homo (f x) (f y) ⟩
        g (f x) ∪ g (f y) ≡⟨ cong₂ (_∪_) g∘fx≡x g∘fy≡y ⟩
        x ∪ y             ∎

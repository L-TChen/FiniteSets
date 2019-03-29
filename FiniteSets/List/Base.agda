{-# OPTIONS --safe --cubical #-}

module FiniteSets.List.Base where

open import Cubical.Core.Everything
open import Cubical.HITs.SetTruncation

open import Cubical.Relation.Nullary

private
  variable
    ℓ   : Level
    A B : Set ℓ

data L (A : Set ℓ) : Set ℓ where
  []    : L A
  _∷_   : A → L A → L A
  dup   : ∀ a xs   → a ∷ a ∷ xs ≡ a ∷ xs
  com   : ∀ a b xs → a ∷ b ∷ xs ≡ b ∷ a ∷ xs
  trunc : ∀ (xs ys : L A) → (p q : xs ≡ ys) → p ≡ q
infixr 10 _∷_

pattern [_] a = a ∷ []

elimL : ∀  {P : L A → Set ℓ}
           → (PSet : {xs : L A} → isSet (P xs))
           → (z : P [])
           → (f : ∀ a xs → P xs → P (a ∷ xs))
           → (∀ a xs pxs → PathP (λ i → P (dup a xs i))
             (f a (a ∷ xs) (f a xs pxs)) (f a xs pxs))
           → (∀ a b xs pxs → PathP (λ i → P (com a b xs i))
             (f a (b ∷ xs) (f b xs pxs)) (f b (a ∷ xs) (f a xs pxs)))
           → (xs : L A) → P xs
elimL PSet z f fdup fcom [] = z
elimL PSet z f fdup fcom (x ∷ xs) = f x xs (elimL PSet z f fdup fcom xs)
elimL {P = P} PSet z f fdup fcom (dup a xs i)  = fdup a xs (elimL PSet z f fdup fcom xs) i 
elimL PSet z f fdup fcom (com a b xs i)        = fcom a b xs (elimL PSet z f fdup fcom xs) i
elimL {A = A} PSet z f fdup fcom (trunc xs ys p q i j) =
  elimSquash₀ {A = L A} (\ xs → PSet {xs}) (trunc xs ys p q) (g xs) (g ys) (cong g p) (cong g q) i j
  where g = elimL PSet z f fdup fcom

elimLprop : ∀  {P : L A → Set ℓ}
           → (PSet : {xs : L A} → isProp (P xs))
           → (z : P [])
           → (f : ∀ a xs → P xs → P (a ∷ xs))
           → (xs : L A) → P xs
elimLprop {P = P} Pprop z f = elimL (isProp→isSet Pprop) z f
  (λ a xs pxs → toPathP (Pprop (transp (λ i → P (dup a xs i)) i0 (f a (a ∷ xs) (f a xs pxs))) (f a xs pxs)))
  λ a b xs pxs → toPathP (Pprop (transp (λ i → P (com a b xs i)) i0
      (f a (b ∷ xs) (f b xs pxs))) (f b (a ∷ xs) (f a xs pxs))) 

recL : isSet B 
     → (z : B)
     → (f : A → B → B)
     → (∀ a p → f a (f a p) ≡ f a p)
     → (∀ a b p → f a (f b p) ≡ f b (f a p))
     → L A → B
recL BSet z f dupᴮ comᴮ =
  elimL BSet z (λ a _ b → f a b)
    (λ a _ pxs → dupᴮ a pxs) (λ a b _ pb → comᴮ a b pb)

infixr 5 _++_
_++_ : L A → L A → L A
_++_ xs ys = recL trunc ys (λ x xs++ys → x ∷ xs++ys) dup com xs

data _∈_ {A : Set ℓ} (a : A) : L A → Set ℓ where
  here  : ∀ {xs}            → a ∈ a ∷ xs
  there : ∀ {xs b} → a ∈ xs → a ∈ b ∷ xs

_∉_ : {A : Set ℓ} → A → L A → Set ℓ
a ∉ xs = ¬ (a ∈ xs)

infix 5 _∈_
infix 5 _∉_

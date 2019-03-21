{-# OPTIONS --safe --cubical #-}

module FiniteSets.List.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

private
  variable
    ℓ   : Level
    A B : Set ℓ



elimTrunc : ∀ {P : A → Set ℓ}
           → (PSet : (x : A) → isSet (P x))
           → ∀ {x y} {p q : x ≡ y} (sq : p ≡ q)
           → ∀ Px Py Pp Pq → PathP (λ i → PathP (λ j → P (sq i j)) Px Py) Pp Pq
elimTrunc {P = P} PSet {x} {p = p} =
  J (λ q sq → ∀ Px Py Pp Pq → PathP (λ i → PathP (λ j → P (sq i j)) Px Py) Pp Pq)
    (J (λ y (p : x ≡ y) → ∀ Px Py → (Pp Pq : PathP (λ i → P (p i)) Px Py) → Pp ≡ Pq) (PSet x) p)

data L (A : Set ℓ) : Set ℓ where
  []    : L A
  _∷_   : A → L A → L A
  dupl   : ∀ a xs   → a ∷ a ∷ xs ≡ a ∷ xs
  coml   : ∀ a b xs → a ∷ b ∷ xs ≡ b ∷ a ∷ xs
  truncl : ∀ (xs ys : L A) → (p q : xs ≡ ys) → p ≡ q
infixr 10 _∷_

elimL : ∀  {P : L A → Set ℓ}
           → (PSet : {xs : L A} → isSet (P xs))
           → (z : P [])
           → (f : ∀ a xs → P xs → P (a ∷ xs))
           → (∀ a xs pxs → PathP (λ i → P (dupl a xs i))
             (f a (a ∷ xs) (f a xs pxs)) (f a xs pxs))
           → (∀ a b xs pxs → PathP (λ i → P (coml a b xs i))
             (f a (b ∷ xs) (f b xs pxs)) (f b (a ∷ xs) (f a xs pxs)))
           → (xs : L A) → P xs
elimL PSet z f fdupl fcoml [] = z
elimL PSet z f fdupl fcoml (x ∷ xs) = f x xs (elimL PSet z f fdupl fcoml xs)
elimL {P = P} PSet z f fdupl fcoml (dupl a xs i)  = fdupl a xs (elimL PSet z f fdupl fcoml xs) i 
elimL PSet z f fdupl fcoml (coml a b xs i)        = fcoml a b xs (elimL PSet z f fdupl fcoml xs) i
elimL {A = A} PSet z f fdupl fcoml (truncl xs ys p q i j) =
  elimTrunc {A = L A} (\ xs → PSet {xs}) (truncl xs ys p q) (g xs) (g ys) (cong g p) (cong g q) i j
  where g = elimL PSet z f fdupl fcoml

elimLprop : ∀  {P : L A → Set ℓ}
           → (PSet : {xs : L A} → isProp (P xs))
           → (z : P [])
           → (f : ∀ a xs → P xs → P (a ∷ xs))
           → (xs : L A) → P xs
elimLprop {P = P} Pprop z f = elimL (isProp→isSet Pprop) z f
  (λ a xs pxs → toPathP (Pprop (transp (λ i → P (dupl a xs i)) i0 (f a (a ∷ xs) (f a xs pxs))) (f a xs pxs)))
  λ a b xs pxs → toPathP (Pprop (transp (λ i → P (coml a b xs i)) i0
      (f a (b ∷ xs) (f b xs pxs))) (f b (a ∷ xs) (f a xs pxs))) 

recL : isSet B 
     → (z : B)
     → (f : A → B → B)
     → (∀ a p → f a (f a p) ≡ f a p)
     → (∀ a b p → f a (f b p) ≡ f b (f a p))
     → L A → B
recL BSet z f duplᴮ comlᴮ =
  elimL BSet z (λ a _ b → f a b)
    (λ a _ pxs → duplᴮ a pxs) (λ a b _ pb → comlᴮ a b pb)

infixr 5 _++_
_++_ : L A → L A → L A
_++_ xs ys = recL truncl ys (λ x xs++ys → x ∷ xs++ys) dupl coml xs

[_] : A → L A
[ a ] = a ∷ [] 

{-# OPTIONS --safe --cubical  --without-K #-}

module FiniteSets.Kuratowski.Base where

open import Cubical.Core.Prelude 
open import Cubical.Core.PropositionalTruncation
open import Cubical.Foundations.HLevels 

open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ''  : Level
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''


infix 5 _∈_
infix 5 _∉_
infix 5 _⊆_
infix 5 _≤_

-- TODO: move this to SetTruncation module? 
elimTrunc : ∀ {P : A → Set ℓ}
           → (PSet : (x : A) → isSet (P x))
           → ∀ {x y} {p q : x ≡ y} (sq : p ≡ q)
           → ∀ Pxs Pys Pp Pq → PathP (λ i → PathP (λ j → P (sq i j)) Pxs Pys) Pp Pq
elimTrunc {P = P} PSet {xs} {p = p} =
  J (λ q sq → ∀ Pxs Pys Pp Pq → PathP (λ i → PathP (λ j → P (sq i j)) Pxs Pys) Pp Pq)
    (J (λ ys (p : xs ≡ ys) → ∀ Pxs Pys → (Pp Pq : PathP (λ i → P (p i)) Pxs Pys) → Pp ≡ Pq) (PSet xs) p)

data K (A : Set ℓ) : Set ℓ where
  ∅     : K A
  [_]   : A → K A
  _∪_   : K A → K A → K A
  nl    : ∀ x → ∅ ∪ x ≡ x
  nr    : ∀ x → x ∪ ∅ ≡ x
  idem  : ∀ a → [ a ] ∪ [ a ] ≡ [ a ]
  assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  com   : ∀ x y → x ∪ y ≡ y ∪ x
  trunc : (x y : K A) → (p q : x ≡ y) → p ≡ q
infixr 10 _∪_

elimK : ∀ {P : K A → Set ℓ}
      → (PSet : {x : K A} → isSet (P x))
      → (z    : P ∅)
      → (s    : (a : A) → P [ a ])
      → (f : (x y : K A) → P x → P y → P (x ∪ y))
      → (∀ x px → PathP (λ i → P (nl x i)) (f ∅ x z px) px)
      → (∀ x px → PathP (λ i → P (nr x i)) (f x ∅ px z) px)
      → (∀ a → PathP (λ i → P (idem a i)) (f [ a ] [ a ] (s a) (s a)) (s a))
      → (∀ x y z Px Py Pz →
        PathP (λ i → P (assoc x y z i))
          (f x (y ∪ z) Px (f y z Py Pz)) (f (x ∪ y) z (f x y Px Py) Pz))
      → (∀ x y Px Py → PathP (λ i → P (com x y i)) (f x y Px Py) (f y x Py Px))
      → (x : K A) → P x
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ ∅ = z
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ [ x ] = s x
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (x ∪ y) = f x y (g x) (g y)
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (nl x i) = nlᴾ x (g x) i
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (nr x i) = nrᴾ x (g x) i
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (idem a i) = idemᴾ a i
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (assoc x y k i) = assocᴾ x y k (g x) (g y) (g k) i
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (com x y i) = comᴾ x y  (g x) (g y) i
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ
elimK {A = A} PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ (trunc x y p q i j) =
  elimTrunc {A = K A} (λ x → PSet {x}) (trunc x y p q) (g x) (g y) (cong g p) (cong g q) i j
  where g = elimK PSet z s f nlᴾ nrᴾ idemᴾ assocᴾ comᴾ

elimKprop : ∀ {P : K A → Set ℓ}
      → (PProp : {x : K A} → isProp (P x))
      → (z    : P ∅)
      → (s    : (a : A) → P [ a ])
      → (f : (x y : K A) → P x → P y → P (x ∪ y))
      → (x : K A) → P x
elimKprop {P = P} PProp z s f = elimK (isProp→isSet PProp) z s f
  (λ x px → toPathP (PProp (transp (λ i → P (nl x i)) i0 (f ∅ x z px)) px))
  (λ x px → toPathP (PProp (transp (λ i → P (nr x i)) i0 (f x ∅ px z)) px))
  (λ a → toPathP (PProp (transp (λ i → P (idem a i)) i0 (f [ a ] [ a ] (s a) (s a))) (s a)))
  (λ x y z Px Py Pz → toPathP (PProp (transp (λ i → P (assoc x y z i)) i0
      (f x (y ∪ z) Px (f y z Py Pz)))
      (f (x ∪ y) z (f x y Px Py) Pz)))
  λ x y Px Py → toPathP (PProp (transp (λ i → P (com x y i)) i0 (f x y Px Py)) (f y x Py Px))

recK : isSet B
     → (z   : B)
     → (ins : A → B)
     → (f : B → B → B)
     → (∀ x → f z x ≡ x)
     → (∀ x → f x z ≡ x)
     → (∀ a → f (ins a) (ins a) ≡ ins a)
     → (∀ x y z → f x (f y z) ≡ f (f x y) z)
     → (∀ x y → f x y ≡ f y x)
     → K A → B  
recK Bset z ins f nlᴮ nrᴮ idemᴮ assocᴮ comᴮ = elimK Bset z ins
  (λ _ _ → f) (λ _ → nlᴮ) (λ _ → nrᴮ) idemᴮ  (λ _ _ _ → assocᴮ) λ _ _ → comᴮ             

--------------------------------------------------------------------------------
-- Membership relation

data _∈_ {A : Set ℓ} (a : A) : K A → Set ℓ where
  here  : ∀ {b}   → (a≡b : a ≡ b) → a ∈ [ b ]
  left  : ∀ {x y} → (a∈x : a ∈ x) → a ∈ x ∪ y
  right : ∀ {x y} → (a∈y : a ∈ y) → a ∈ x ∪ y

_∉_ : {A : Set ℓ} → A → K A → Set ℓ
a ∉ x = ¬ (a ∈ x)

_⊆_ : {A : Set ℓ} → K A → K A → Set ℓ
_⊆_ {A = A} x y = ∀ (a : A) → a ∈ x → a ∈ y

_≤_ : {A : Set ℓ} → K A → K A → Set ℓ
x ≤ y = x ∪ y ≡ y

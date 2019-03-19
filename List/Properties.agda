{-# OPTIONS --safe --cubical #-}

module FiniteSets.List.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Level

open import FiniteSets.Kuratowski
open import FiniteSets.List

private
  variable
    ℓ  : Level
    A : Set ℓ

K≃L : K A ≃ L A
K≃L = {!!}
  where
    f : K A → L A
    f = {!!}
    g : L A → K A
    g = {!!}
    h : L A → K A
    h = {!!}

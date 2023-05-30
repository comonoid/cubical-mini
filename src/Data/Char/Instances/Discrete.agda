{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Discrete

open import Data.Nat.Instances.Discrete
open import Data.Id

open import Data.Char.Properties

instance
  Discrete-char : Discrete Char
  Discrete-char .Discrete._≟_ =
    is-discreteⁱ→is-discrete char-is-discreteⁱ
    where
    char-is-discreteⁱ : is-discreteⁱ Char
    char-is-discreteⁱ x y with to-ℕ x ≟ to-ℕ y
    ... | yes p = yes $ char-to-nat-injectiveⁱ _ _ ((Id≃path ₑ⁻¹) .fst p)
    ... | no ¬p = no λ p → ¬p (ap to-ℕ (Id≃path .fst p))
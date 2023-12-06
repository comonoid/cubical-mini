{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Finite where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Finite.Bishop

open import Data.Nat.Base
open import Data.Fin.Computational.Path
open import Data.List.Base

open import Truncation.Propositional.Base

private variable n : ℕ

instance
  fin-is-bishop-finite : is-bishop-finite (Fin n)
  fin-is-bishop-finite = fin₁ ∣ idₑ ∣₁

  decomp-fin-fin : goal-decomposition (quote is-bishop-finite) (Fin n)
  decomp-fin-fin = decomp (quote fin-is-bishop-finite) []

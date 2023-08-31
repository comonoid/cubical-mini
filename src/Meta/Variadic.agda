{-# OPTIONS --safe #-}
module Meta.Variadic where

open import Foundations.Base

open import Meta.Reflection

open import Correspondences.Base
open import Correspondences.Decidable

open import Data.List.Base

-- TODO it can be automated!
-- need to define a mask for vector and bulk update operation

pattern carrierⁿ n t =
  def (quote Carrierⁿ) (unknown h∷ lit (nat n) h∷ unknown h∷ unknown h∷ unknown h∷ t v∷ [])
macro
  Carrier! : Term → Term → TC ⊤
  Carrier! t hole = do
    ty ← inferType t >>= normalise
    let arity = arity-ty ty
    unify hole $ carrierⁿ arity t

  syntax Carrier! C = ⌞ C ⌟ⁿ


pattern quantⁿ q n t =
  def q (lit (nat n) h∷ unknown h∷ unknown h∷ unknown h∷ t v∷ [])

Quantifier : Name → Term → Term → TC ⊤
Quantifier nam t hole = do
  ty ← inferType t >>= normalise
  let arity = arity-ty ty
  unify hole $ quantⁿ nam arity t

infix 10 Existential! Existential₁! Universal! IUniversal!
macro
  Existential! : Term → Term → TC ⊤
  Existential! = Quantifier (quote Existentialⁿ)
  syntax Existential! P = Σ[ P ]

  Existential₁! : Term → Term → TC ⊤
  Existential₁! = Quantifier (quote Existential₁ⁿ)
  syntax Existential₁! P = ∃[ P ]

  Universal! : Term → Term → TC ⊤
  Universal! = Quantifier (quote Universalⁿ)
  syntax Universal! P = Π[ P ]

  IUniversal! : Term → Term → TC ⊤
  IUniversal! = Quantifier (quote IUniversalⁿ)
  syntax IUniversal! P = ∀[ P ]

pattern implⁿ n p q =
  def (quote Implⁿ) (lit (nat n) h∷ unknown h∷ unknown h∷ p v∷ q v∷ [])
macro
  Impl! : Term → Term → Term → TC ⊤
  Impl! p q hole = do
    pty ← inferType p >>= normalise
    qty ← inferType q >>= normalise
    let arity = arity-ty pty
    unify hole $ implⁿ arity p q

  syntax Impl! P Q = P ⇒ Q



pattern decidableⁿ n t = def (quote Decidableⁿ) (unknown h∷ lit (nat n) v∷ unknown h∷ unknown h∷ t v∷ [])
macro
  Decidable : Term → Term → TC ⊤
  Decidable t hole = do
    ty ← inferType t >>= normalise
    let arity = arity-ty ty
    unify hole $ decidableⁿ arity t

pattern reflectsⁿ n c d = def (quote Reflectsⁿ) (unknown h∷ lit (nat n) v∷ unknown h∷ unknown h∷ c v∷ d v∷ [])
macro
  Reflects : Term → Term → Term → TC ⊤
  Reflects c d hole = do
    cty ← inferType c >>= normalise
    let arity = arity-ty cty
    unify hole $ reflectsⁿ arity c d

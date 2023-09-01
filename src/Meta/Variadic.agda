{-# OPTIONS --safe #-}
module Meta.Variadic where

open import Foundations.Base

open import Meta.Reflection

open import Correspondences.Base
open import Correspondences.Decidable

open import Data.Fin.Instances.FromNat
open import Data.List.Base
open import Data.Vec.Operations.Inductive

-- TODO I know it's horrible and can be automated more!
-- need to define a mask for vector and bulk update operation

macro
  Carrier! : Term → Term → TC ⊤
  Carrier! t hole = do
    ty ← inferType t >>= normalise
    let arity = arity-ty ty
    nty ← getType (quote Carrierⁿ)
    as ← (pure $ make-spine nty) >>= args-ensure-length 6
    let as = as & arg-replace 1 (lit (nat arity))
                & arg-replace 5 t
    unify hole $ def (quote Carrierⁿ) $ fst $ vec→list as

  syntax Carrier! C = ⌞ C ⌟ⁿ


Quantifier : Name → Term → Term → TC ⊤
Quantifier nam t hole = do
  ty ← inferType t >>= normalise
  let arity = arity-ty ty
  qty ← getType nam
  as ← (pure $ make-spine qty) >>= args-ensure-length 5
  let as = as & arg-replace 0 (lit (nat arity))
              & arg-replace 4 t
  unify hole $ def nam $ fst $ vec→list as

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


macro
  Impl! : Term → Term → Term → TC ⊤
  Impl! p q hole = do
    pty ← inferType p >>= normalise
    qty ← inferType q >>= normalise
    let arity = arity-ty pty
    nty ← getType (quote Implⁿ)
    as ← (pure $ make-spine nty) >>= args-ensure-length 5
    let as = as & arg-replace 0 (lit (nat arity))
                & arg-replace 3 p & arg-replace 4 q
    unify hole $ def (quote Implⁿ) $ fst $ vec→list as

  syntax Impl! P Q = P ⇒ Q


macro
  Decidable : Term → Term → TC ⊤
  Decidable t hole = do
    nty ← getType (quote Decidableⁿ) >>= normalise
    as ← (pure $ make-spine nty) >>= args-ensure-length 5
    let as = as & arg-replace 4 t
    0 ← wait-for-type t >>= arity-term where -- AAAAAAAA!!!!!!
      arity → do
        let as = as & arg-replace 1 (lit (nat arity))
        unify hole $ def (quote Decidableⁿ) $ fst $ vec→list as
    ty ← (wait-for-type t >>= inferType) >>= normalise
    let arity = arity-ty ty
    let as = as & arg-replace 1 (lit (nat arity))
    unify hole $ def (quote Decidableⁿ) $ fst $ vec→list as

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  x : A
  @0 n : ℕ
  @0 xs : Vec A n

macro
  Reflects : Term → Term → Term → TC ⊤
  Reflects c d hole = do
    cty ← inferType c >>= normalise
    let arity = arity-ty cty
    nty ← getType (quote Reflectsⁿ)
    as ← (pure $ make-spine nty) >>= args-ensure-length 6
    let as = as & arg-replace 1 (lit (nat arity))
                & arg-replace 4 c & arg-replace 5 d
    unify hole $ def (quote Reflectsⁿ) $ fst $ vec→list as

{-# OPTIONS --safe #-}
module Cubical.Truncation.Propositional.Instances where

open import Cubical.Foundations.Prelude

open import Cubical.Truncation.Propositional.Base
open import Cubical.Truncation.Propositional.Properties

open import Cubical.Instances.DecEq
open import Cubical.Instances.HLevels
open import Cubical.Instances.Show

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  DecEqPropTrunc : DecEq ∥ A ∥₁
  DecEq._≟_ DecEqPropTrunc x y = yes (squash₁ x y)

instance
  IsPropPropTrunc : IsProp ∥ A ∥₁
  IsOfHLevel.iohl IsPropPropTrunc = squash₁

instance
  ShowPropTrunc : Show ∥ A ∥₁
  Show.show ShowPropTrunc _ = "∣?∣₁"
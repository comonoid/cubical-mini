{-# OPTIONS --safe #-}
module Correspondences.Decidable where

open import Foundations.Base

open import Correspondences.Base public
open import Correspondences.Classical

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Nat.Base

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = essentially-classical-η ∘ Dec.rec
  (λ a _ → a)
  (λ ¬a f → ⊥.rec (f ¬a))

decide : ⦃ d : Dec A ⦄ → Dec A
decide ⦃ d ⦄ = d

×-decision : Dec A → Dec B → Dec (A × B)
×-decision da db .does = da .does and db .does
×-decision (no ¬a) db .proof = ofⁿ $ ¬a ∘ fst
×-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ snd
×-decision (yes a) (yes b) .proof = ofʸ (a , b)

fun-decision : Dec A → Dec B → Dec (A → B)
fun-decision da db .does = not (da .does) or db .does
fun-decision (no ¬a) db .proof = ofʸ $ λ a → ⊥.rec (¬a a)
fun-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ (_$ a)
fun-decision (yes a) (yes b) .proof = ofʸ λ _ → b

¬-decision : Dec A → Dec (¬ A)
¬-decision da .does = not (da .does)
¬-decision (yes a) .proof = ofⁿ (_$ a)
¬-decision (no ¬a) .proof = ofʸ ¬a


-- Decidability of a correspondence
Decidableⁿ : (arity : ℕ) {ls : Levels arity} {As : Types arity ls} → Pred _ (Corr arity ℓ As)
Decidableⁿ arity P = Πⁿ[ mapⁿ _ Dec P ]


-- Decision procedure
DProc
  : (arity : ℕ)
    {ls : Levels arity} (As : Types _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5

-- Evidence of a correspondence `P` being reflected by a decision procedure
Reflectsⁿ : (arity : ℕ) {ls : Levels arity} {As : Types _ ls} → Corr _ ℓ As → DProc _ As → Type (ℓ ⊔ ℓsup _ ls)
Reflectsⁿ 0                           P d = Reflects⁰ P d
Reflectsⁿ 1             {As = A}      P d = Π[ x ꞉ A ] Reflectsⁿ _ (P x) (d x)
Reflectsⁿ (suc (suc _)) {As = A , As} P d = Π[ x ꞉ A ] Reflectsⁿ _ (P x) (d x)

reflects→decidable
  : {ls : Levels n} {As : Types n ls} {P : Corr n ℓ As} {d : DProc n As}
  → Reflectsⁿ n P d → Decidableⁿ _ P
reflects→decidable {n = 0}          {d} p   = d because p
reflects→decidable {n = 1}          {d} f x = d x because f x
reflects→decidable {n = suc (suc _)}    f x = reflects→decidable (f x)

------------------------------------------------------------------------
-- A variant of Coherently that is defined without the use of
-- coinduction
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coherently.Not-coinductive
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Container.Indexed equality-with-J
open import Container.Indexed.M.Function equality-with-J
open import H-level.Truncation.Propositional.One-step eq using (∥_∥¹)

private
  variable
    a b p : Level

-- A container that is used to define Coherently.

Coherently-container :
  {B : Type b}
  (P : {A : Type a} → (A → B) → Type p)
  (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B) →
  Container (∃ λ (A : Type a) → A → B) p lzero
Coherently-container P step = λ where
  .Shape (_ , f)               → P f
  .Position _                  → ⊤
  .index {o = A , f} {s = p} _ → ∥ A ∥¹ , step f p

-- A variant of Coherently, defined using an indexed container.

Coherently :
  {A : Type a} {B : Type b}
  (P : {A : Type a} → (A → B) → Type p)
  (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B) →
  (f : A → B) →
  Type (lsuc a ⊔ b ⊔ p)
Coherently P step f =
  M (Coherently-container P step) (_ , f)

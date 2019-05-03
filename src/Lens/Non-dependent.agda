------------------------------------------------------------------------
-- Representation-independent results for non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lens.Non-dependent where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J as Bij using (module _↔_)
open import Function-universe equality-with-J
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type, assuming that lenses with contractible domains have
-- contractible codomains.

no-first-projection-lens :
  ∀ {a b c}
  (Lens : Set (a ⊔ b) → Set a → Set c) →
  (∀ {A B} → Lens A B → Contractible A → Contractible B) →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens {b = b} _ contractible-to-contractible =
  ↑ _ Bool ,
  (λ b → ↑ _ (lower b ≡ true)) ,
  λ l →                                           $⟨ singleton-contractible _ ⟩
     Contractible (Singleton true)                ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (∃ λ b → ↑ _ (lower b ≡ true))  ↝⟨ contractible-to-contractible l ⟩
     Contractible (↑ _ Bool)                      ↝⟨ H-level.respects-surjection (_↔_.surjection Bij.↑↔) 0 ⟩
     Contractible Bool                            ↝⟨ mono₁ 0 ⟩
     Is-proposition Bool                          ↝⟨ ¬-Bool-propositional ⟩□
     ⊥                                            □
  where
  surj : Singleton true ↠ ∃ λ b → ↑ _ (lower b ≡ true)
  surj = record
    { logical-equivalence = record
      { to   = λ { (b , b≡true) → lift b , lift b≡true }
      ; from = λ { (lift b , lift b≡true) → b , b≡true }
      }
    ; right-inverse-of = λ _ → refl
    }

------------------------------------------------------------------------
-- Representation-independent results for non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent where

open import Equality.Propositional.Cubical
open import Prelude

open import Bijection equality-with-J as Bij using (module _↔_)
open import Erased.Cubical equality-with-paths
open import Function-universe equality-with-J
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b c : Level

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type, assuming that lenses with contractible domains have
-- contractible codomains.

no-first-projection-lens :
  (Lens : Set (a ⊔ b) → Set a → Set c) →
  @0 (∀ {A B} → Lens A B → Contractible A → Contractible B) →
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens {b = b} _ contractible-to-contractible =
  ↑ _ Bool ,
  (λ b → ↑ _ (lower b ≡ true)) ,
  λ l →                                           $⟨ singleton-contractible _ ⟩
     Contractible (Singleton true)                ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (∃ λ b → ↑ _ (lower b ≡ true))  ↝⟨ (λ hyp → [ contractible-to-contractible l hyp ]) ⟩
     Erased (Contractible (↑ _ Bool))             ↝⟨ Erased-cong (H-level.respects-surjection (_↔_.surjection Bij.↑↔) 0) ⟩
     Erased (Contractible Bool)                   ↝⟨ Erased-cong (mono₁ 0) ⟩
     Erased (Is-proposition Bool)                 ↝⟨ inverse-ext? ¬-Erased↔¬ _ ¬-Bool-propositional ⟩□
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

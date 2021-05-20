------------------------------------------------------------------------
-- Higher lenses, defined using the requirement that the remainder
-- function should be surjective
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Surjective-remainder
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (_∘_)
open import H-level.Truncation.Propositional eq

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher

private
  variable
    a b : Level
    A B : Type a

-- A variant of the lenses defined in Lens.Non-dependent.Higher. In
-- this definition the function called inhabited is replaced by a
-- requirement that the remainder function should be surjective.

record Lens (A : Type a) (B : Type b) : Type (lsuc (a ⊔ b)) where
  field
    -- Remainder type.
    R : Type (a ⊔ b)

    -- Equivalence.
    equiv : A ≃ (R × B)

  -- Remainder.

  remainder : A → R
  remainder a = proj₁ (_≃_.to equiv a)

  field
    -- The remainder function is surjective.
    remainder-surjective : Surjective remainder

  -- Getter.

  get : A → B
  get a = proj₂ (_≃_.to equiv a)

  -- Setter.

  set : A → B → A
  set a b = _≃_.from equiv (remainder a , b)

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens can be expressed as a nested Σ-type.

Lens-as-Σ :
  {A : Type a} {B : Type b} →
  Lens A B ≃
  ∃ λ (R : Type (a ⊔ b)) →
  ∃ λ (equiv : A ≃ (R × B)) →
    Surjective (proj₁ ∘ _≃_.to equiv)
Lens-as-Σ = Eq.↔→≃
  (λ l → R l , equiv l , remainder-surjective l)
  (λ (R , equiv , remainder-surjective) → record
     { R                    = R
     ; equiv                = equiv
     ; remainder-surjective = remainder-surjective
     })
  refl
  refl
  where
  open Lens

-- Higher.Lens A B is equivalent to Lens A B.

Higher-lens≃Lens : Higher.Lens A B ≃ Lens A B
Higher-lens≃Lens {A = A} {B = B} =
  Higher.Lens A B                              ↔⟨ Higher.Lens-as-Σ ⟩

  (∃ λ (R : Type _) →
     (A ≃ (R × B)) ×
     (R → ∥ B ∥))                              ↝⟨ (∃-cong λ _ → ∃-cong Higher.inhabited≃remainder-surjective) ⟩
  (∃ λ (R : Type _) →
   ∃ λ (equiv : A ≃ (R × B)) →
     Surjective (proj₁ ∘ _≃_.to equiv))        ↝⟨ inverse Lens-as-Σ ⟩□

  Lens A B                                     □

-- The equivalence preserves getters and setters.

Higher-lens≃Lens-preserves-getters-and-setters :
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence Higher-lens≃Lens)
Higher-lens≃Lens-preserves-getters-and-setters =
    (λ _ → refl _ , refl _)
  , (λ _ → refl _ , refl _)

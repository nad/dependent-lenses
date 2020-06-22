------------------------------------------------------------------------
-- "Lenses" defined using bijections
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Bijection
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent.Higher      eq as Higher
import Lens.Non-dependent.Traditional eq as Traditional

private
  variable
    a b : Level

-- A "naive" definition of lenses using a bijection.
--
-- This definition is not in general isomorphic to Higher.Lens A B,
-- not even if A and B are sets (consider the case in which A and B
-- are empty; see ¬Higher-lens↠Lens below).

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens {a = a} {b = b} A B =
  ∃ λ (R : Set (a ⊔ b)) → A ↔ (R × B)

-- Lens ⊥ ⊥ is isomorphic to Set something.

Lens-⊥-⊥↔Set :
  Lens (⊥ {ℓ = a}) (⊥ {ℓ = b}) ↔ Set (a ⊔ b)
Lens-⊥-⊥↔Set =
  Lens ⊥ ⊥               ↔⟨ (∃-cong λ _ → Eq.↔↔≃ ext (mono₁ 1 ⊥-propositional)) ⟩
  (∃ λ R → ⊥ ≃ (R × ⊥))  ↔⟨ (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id ×-right-zero) ⟩
  (∃ λ R → ⊥ ≃ ⊥₀)       ↔⟨ (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ R → ¬ ⊥)          ↔⟨ drop-⊤-right (λ _ → ¬⊥↔⊤ {k = bijection} ext) ⟩□
  Set _                  □

-- There is a split surjection from Lens A B to Higher.Lens A B
-- (assuming univalence).

Lens↠Higher-lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Lens A B ↠ Higher.Lens A B
Lens↠Higher-lens {A = A} {B} univ = record
  { logical-equivalence = record
    { to   = λ { (R , A↔R×B) → Higher.isomorphism-to-lens A↔R×B }
    ; from = λ { l → R l , _≃_.bijection (equiv l) }
    }
  ; right-inverse-of = λ { l →
      _↔_.from (Higher.equality-characterisation₂ univ)
        ( (R l × ∥ B ∥  ↔⟨ drop-⊤-right (λ r → inhabited⇒∥∥↔⊤ (inhabited l r)) ⟩□
           R l          □)
        , λ _ → refl _
        ) }
  }
  where
  open Higher.Lens

-- However, there is in general no split surjection in the other
-- direction, not even for sets (assuming univalence).

¬Higher-lens↠Lens :
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Is-set A → Is-set B →
     Higher.Lens A B ↠ Lens A B)
¬Higher-lens↠Lens univ surj =
  ⊥-elim (subst F.id ⊤≡⊥ _)
  where
  ⊥-is-set : ∀ {ℓ} → Is-set (⊥ {ℓ = ℓ})
  ⊥-is-set = mono₁ 1 ⊥-propositional

  ⊤↠Set =
    ⊤                ↔⟨ inverse $ Higher.lens-from-⊥↔⊤ univ ⟩
    Higher.Lens ⊥ ⊥  ↝⟨ surj ⊥-is-set ⊥-is-set ⟩
    Lens ⊥ ⊥         ↔⟨ Lens-⊥-⊥↔Set ⟩□
    Set _            □

  ⊤≡⊥ : ↑ _ ⊤ ≡ ⊥
  ⊤≡⊥ =
    ↑ _ ⊤              ≡⟨ sym $ right-inverse-of _ ⟩
    to (from (↑ _ ⊤))  ≡⟨⟩
    to (from ⊥)        ≡⟨ right-inverse-of _ ⟩∎
    ⊥                  ∎
    where
    open _↠_ ⊤↠Set

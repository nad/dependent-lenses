------------------------------------------------------------------------
-- "Lenses" defined using bijections
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Bijection
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
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

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens {a = a} {b = b} A B =
  ∃ λ (R : Type (a ⊔ b)) → A ↔ (R × B)

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = λ (_ , bij) a → proj₂ (_↔_.to bij a)
    ; set = λ (_ , bij) a b → _↔_.from bij (proj₁ (_↔_.to bij a) , b)
    }

-- Lens ⊥ ⊥ is equivalent to Type something.

Lens-⊥-⊥≃Type :
  Lens (⊥ {ℓ = a}) (⊥ {ℓ = b}) ≃ Type (a ⊔ b)
Lens-⊥-⊥≃Type =
  Lens ⊥ ⊥               ↔⟨ (∃-cong λ _ → Eq.↔↔≃ ext (mono₁ 1 ⊥-propositional)) ⟩
  (∃ λ R → ⊥ ≃ (R × ⊥))  ↔⟨ (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id ×-right-zero) ⟩
  (∃ λ R → ⊥ ≃ ⊥₀)       ↔⟨ (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ R → ¬ ⊥)          ↔⟨ drop-⊤-right (λ _ → ¬⊥↔⊤ {k = bijection} ext) ⟩□
  Type _                 □

-- There is a split surjection from Lens A B to Higher.Lens A B
-- (assuming univalence).

Lens↠Higher-lens :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  Lens A B ↠ Higher.Lens A B
Lens↠Higher-lens {A = A} {B} univ = record
  { logical-equivalence = record
    { to   = λ { (R , A↔R×B) → Higher.isomorphism-to-lens A↔R×B }
    ; from = λ { l → R l , _≃_.bijection (equiv l) }
    }
  ; right-inverse-of = λ { l →
      _↔_.from (Higher.equality-characterisation₁ ⊠ univ)
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
  ¬ ({A : Type a} {B : Type b} →
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
    Lens ⊥ ⊥         ↔⟨ Lens-⊥-⊥≃Type ⟩□
    Type _           □

  ⊤≡⊥ : ↑ _ ⊤ ≡ ⊥
  ⊤≡⊥ =
    ↑ _ ⊤              ≡⟨ sym $ right-inverse-of _ ⟩
    to (from (↑ _ ⊤))  ≡⟨⟩
    to (from ⊥)        ≡⟨ right-inverse-of _ ⟩∎
    ⊥                  ∎
    where
    open _↠_ ⊤↠Set

-- The split surjection Lens↠Higher-lens preserves getters and
-- setters.

Lens↠Higher-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_↠_.logical-equivalence (Lens↠Higher-lens univ))
Lens↠Higher-lens-preserves-getters-and-setters univ =
    (λ _ → refl _ , refl _)
  , (λ _ → refl _ , refl _)

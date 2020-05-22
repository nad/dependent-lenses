------------------------------------------------------------------------
-- Higher lenses, defined using the requirement that the remainder
-- function should be surjective
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Higher.Surjective-remainder where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths

import Lens.Non-dependent.Higher as Higher

private
  variable
    a b : Level
    A B : Set a

-- A variant of the lenses defined in Lens.Non-dependent.Higher. In
-- this definition the function called inhabited is replaced by a
-- requirement that the remainder function should be surjective.

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens {a = a} {b = b} A B =
  ∃ λ (get       : A → B) →
  ∃ λ (R         : Set (a ⊔ b)) →
  ∃ λ (remainder : A → R) →
    Is-equivalence (λ a → remainder a , get a) ×
    Surjective remainder

-- Higher.Lens A B is isomorphic to Lens A B.

Higher-lens↔Lens : Higher.Lens A B ↔ Lens A B
Higher-lens↔Lens {A = A} {B = B} =

  Higher.Lens A B                                         ↝⟨ Higher.Lens-as-Σ ⟩

  (∃ λ (R : Set _) →
     (A ≃ (R × B)) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Eq.≃-as-Σ ×-cong F.id) ⟩

  (∃ λ (R : Set _) →
     (∃ λ (f : A → R × B) → Eq.Is-equivalence f) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (f : A → R × B) →
     Eq.Is-equivalence f ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ → F.id) ⟩

  (∃ λ (R  : Set _) →
   ∃ λ (rg : (A → R) × (A → B)) →
     Eq.Is-equivalence (λ a → proj₁ rg a , proj₂ rg a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
   ∃ λ (get       : A → B) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (get       : A → B) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ ∃-comm ⟩

  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ get → ∃-cong λ R → ∃-cong λ rem → ∃-cong λ eq →
                                                              ∀-cong ext λ _ → ∥∥-cong $
                                                              lemma get R rem eq _) ⟩□
  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     Surjective remainder)                                □

  where
  lemma : ∀ _ _ _ _ _ → _
  lemma = λ _ _ remainder eq r →
    B                            ↝⟨ (inverse $ drop-⊤-right λ _ →
                                     _⇔_.to contractible⇔↔⊤ $
                                     singleton-contractible _) ⟩
    B × Singleton r              ↝⟨ Σ-assoc ⟩
    (∃ λ { (_ , r′) → r′ ≡ r })  ↝⟨ (Σ-cong ×-comm λ _ → F.id) ⟩
    (∃ λ { (r′ , _) → r′ ≡ r })  ↝⟨ (inverse $ Σ-cong Eq.⟨ _ , eq ⟩ λ _ → F.id) ⟩□
    (∃ λ a → remainder a ≡ r)    □

------------------------------------------------------------------------
-- Higher lenses, defined using the requirement that the remainder
-- function should be surjective
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Surjective-remainder
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher

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

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = λ (get , _) → get
    ; set = λ (_ , _ , rem , equiv , _) a b →
              _≃_.from Eq.⟨ _ , equiv ⟩ (rem a , b)
    }

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

-- The isomorphism preserves getters and setters.

Higher-lens↔Lens-preserves-getters-and-setters :
  Preserves-getters-and-setters-⇔ A B
    (_↔_.logical-equivalence Higher-lens↔Lens)
Higher-lens↔Lens-preserves-getters-and-setters =
    (λ _ → refl _ , refl _)
  , (λ l@(get , _ , rem , is-equiv , _) →
       let equiv = Eq.⟨ _ , is-equiv ⟩ in
         refl _
       , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
         _≃_.to-from (Higher.Lens.equiv (_↔_.from Higher-lens↔Lens l))
           (_≃_.to equiv (_≃_.from equiv (rem a , b))  ≡⟨ _≃_.right-inverse-of equiv _ ⟩∎
            rem a , b                                  ∎))
  where
  open Higher.Lens

------------------------------------------------------------------------
-- Paolo Capriotti's variant of higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Higher.Capriotti where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
open import Preimage equality-with-J
open import Univalence-axiom equality-with-J

import Lens.Non-dependent.Higher      as Higher
import Lens.Non-dependent.Traditional as Traditional

private
  variable
    a b : Level

-- Paolo Capriotti seems to have been first to describe a notion of
-- higher lens
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens {a = a} A B =
  ∃ λ (g : A → B) →
  ∃ λ (H : Pow a ∥ B ∥) →
    (g ⁻¹_) ≡ H ∘ ∣_∣

-- Lens A B is isomorphic to Higher.Lens A B (assuming univalence).
--
-- (This proof was simplified following a suggestion by Paolo
-- Capriotti.)

Lens↔Higher-lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Lens A B ↔ Higher.Lens A B
Lens↔Higher-lens {a = a} {b = b} {A = A} {B = B} univ =

  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) →
     (g ⁻¹_) ≡ H ∘ ∣_∣)                                  ↔⟨ Σ-cong lemma₂ (λ _ → ∃-cong (lemma₃ _)) ⟩

  (∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
   ∃ λ (H : Pow a ∥ B ∥) →
     proj₁ p ≡ H ∘ ∣_∣)                                  ↝⟨ ∃-comm ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
     proj₁ p ≡ H ∘ ∣_∣)                                  ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      A ≃ ∃ P × P ≡ H ∘ ∣_∣)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ∘ ∣_∣ × A ≃ ∃ P)                             ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq →
                                                             Eq.≃-preserves ext F.id (∃-cong λ x → ≡⇒↝ _ (cong (_$ x) eq))) ⟩
  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ∘ ∣_∣ × A ≃ ∃ (H ∘ ∣_∣))                     ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   (∃ λ (P : Pow a B) → P ≡ H ∘ ∣_∣) ×
   A ≃ ∃ (H ∘ ∣_∣))                                      ↝⟨ (∃-cong λ _ →
                                                             drop-⊤-left-× λ _ →
                                                             _⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

  (∃ λ (H : Pow a ∥ B ∥) → A ≃ ∃ (H ∘ ∣_∣))              ↔⟨ inverse $
                                                            Σ-cong (inverse $ Pow↔Fam a ext univ) (λ _ →
                                                            Eq.≃-preserves ext F.id F.id) ⟩

  (∃ λ (H : Fam a ∥ B ∥) → A ≃ ∃ ((proj₂ H ⁻¹_) ∘ ∣_∣))  ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set ℓ) →
   ∃ λ (f : R → ∥ B ∥) → A ≃ ∃ ((f ⁻¹_) ∘ ∣_∣))          ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                             Eq.≃-preserves ext F.id
                            (∃ ((f ⁻¹_) ∘ ∣_∣)                 ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                     _⇔_.to contractible⇔↔⊤ $
                                                                       +⇒≡ truncation-is-proposition) ⟩
                             B × R                             ↔⟨ ×-comm ⟩□
                             R × B                             □)) ⟩

  (∃ λ (R : Set ℓ) → (R → ∥ B ∥) × (A ≃ (R × B)))        ↝⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (R : Set ℓ) → (A ≃ (R × B)) × (R → ∥ B ∥))        ↝⟨ inverse Higher.Lens-as-Σ ⟩□

  Higher.Lens A B                                        □

  where
  ℓ = a ⊔ b

  lemma₁ : ∀ (g : A → B) b →
           g ⁻¹ b ↔ (g ∘ lower {ℓ = ℓ}) ⁻¹ b
  lemma₁ g b = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ { (a , ga≡b) → lift a , ga≡b }
        ; from = λ { (lift a , ga≡b) → a , ga≡b }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  abstract

    lemma₂ : (A → B) ↔ ∃ λ (P : Pow a B) → A ≃ ∃ P
    lemma₂ = →↔Σ≃Σ ℓ ext univ

    lemma₃ :
      (g : A → B) (H : Pow a ∥ B ∥) →
      ((g ⁻¹_) ≡ H ∘ ∣_∣)
        ≃
      (proj₁ (_↔_.to lemma₂ g) ≡ H ∘ ∣_∣)
    lemma₃ g H =
      (g ⁻¹_) ≡ H ∘ ∣_∣                   ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (∀ b → g ⁻¹ b ≡ H ∣ b ∣)            ↝⟨ ∀-cong ext (λ _ →
                                               ≡-preserves-≃ ext univ univ
                                                 (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ∘ lower) ⁻¹ b ≡ H ∣ b ∣)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
      ((g ∘ lower) ⁻¹_) ≡ H ∘ ∣_∣         □

-- If the domain A is a set, then Traditional.Lens A B and Lens A B
-- are isomorphic (assuming univalence).

Lens↔Traditional-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Is-set A →
  Lens A B ↔ Traditional.Lens A B
Lens↔Traditional-lens {A = A} {B} bc univ A-set =
  Lens A B              ↝⟨ Lens↔Higher-lens univ ⟩
  Higher.Lens A B       ↝⟨ Higher.Lens↔Traditional-lens bc univ A-set ⟩□
  Traditional.Lens A B  □

------------------------------------------------------------------------
-- Paolo Capriotti's variant of higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq
open import Preimage equality-with-J
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher      eq as Higher
import Lens.Non-dependent.Traditional eq as Traditional

private
  variable
    a b : Level
    A B : Set a

------------------------------------------------------------------------
-- The lens type family

-- Higher lenses, as presented by Paolo Capriotti, who seems to have
-- been first to describe a notion of higher lens
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens {a = a} A B =
  ∃ λ (g : A → B) →
  ∃ λ (H : Pow a ∥ B ∥) →
    (g ⁻¹_) ≡ H ∘ ∣_∣

-- Some derived definitions.

module Lens {A : Set a} {B : Set b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- A predicate.

  H : Pow a ∥ B ∥
  H = proj₁ (proj₂ l)

  -- An equality.

  get⁻¹-≡ : (get ⁻¹_) ≡ H ∘ ∣_∣
  get⁻¹-≡ = proj₂ (proj₂ l)

  -- A setter.
  --
  -- This definition is based on Paolo Capriotti's.

  set : A → B → A
  set a b =                  $⟨ truncation-is-proposition ∣ get a ∣ ∣ b ∣ ⟩
    ∣ get a ∣ ≡ ∣ b ∣        ↝⟨ cong H ⟩
    H ∣ get a ∣ ≡ H ∣ b ∣    ↝⟨ subst (λ f → f (get a) ≡ f b) (sym get⁻¹-≡) ⟩
    get ⁻¹ get a ≡ get ⁻¹ b  ↝⟨ ≡⇒≃ ⟩
    get ⁻¹ get a ≃ get ⁻¹ b  ↝⟨ flip _≃_.to (a , refl _) ⟩
    get ⁻¹ b                 ↝⟨ proj₁ ⟩□
    A                        □

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Equality characterisation lemmas

-- An equality characterisation lemma.

equality-characterisation₁ :
  {l₁ l₂ : Lens A B} →

  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (⟨ext⟩ (h ∘ ∣_∣))) ≡
     get⁻¹-≡ l₂)
equality-characterisation₁ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                                ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Σ-assoc ⟩

  ((get l₁ , H l₁) , get⁻¹-≡ l₁) ≡ ((get l₂ , H l₂) , get⁻¹-≡ l₂)        ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

  (∃ λ (eq : (get l₁ , H l₁) ≡ (get l₂ , H l₂)) →
     subst (λ (g , H) → g ⁻¹_ ≡ H ∘ ∣_∣) eq (get⁻¹-≡ l₁) ≡ get⁻¹-≡ l₂)   ↝⟨ (Σ-cong-contra ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ ((g , h) : get l₁ ≡ get l₂ × H l₁ ≡ H l₂) →
     subst (λ (g , H) → g ⁻¹_ ≡ H ∘ ∣_∣) (cong₂ _,_ g h) (get⁻¹-≡ l₁) ≡
     get⁻¹-≡ l₂)                                                         ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     subst (λ (g , H) → g ⁻¹_ ≡ H ∘ ∣_∣) (cong₂ _,_ g h) (get⁻¹-≡ l₁) ≡
     get⁻¹-≡ l₂)                                                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $
                                                                             lemma _ _) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     trans (sym (cong _⁻¹_ g)) (trans (get⁻¹-≡ l₁) (cong (_∘ ∣_∣) h)) ≡
     get⁻¹-≡ l₂)                                                         ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                             Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                             F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (cong (_∘ ∣_∣) (⟨ext⟩ h))) ≡
     get⁻¹-≡ l₂)                                                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                             cong (λ eq → trans _ (trans _ eq) ≡ _) $
                                                                             cong-pre-∘-ext _) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (⟨ext⟩ (h ∘ ∣_∣))) ≡
     get⁻¹-≡ l₂)                                                         □
  where
  open Lens

  lemma : ∀ _ _ → _
  lemma g h =
    subst (λ (g , H) → g ⁻¹_ ≡ H ∘ ∣_∣) (cong₂ _,_ g h) (get⁻¹-≡ l₁)     ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (λ (g , _) → g ⁻¹_) (cong₂ _,_ g h)))
      (trans (get⁻¹-≡ l₁) (cong (λ (_ , H) → H ∘ ∣_∣) (cong₂ _,_ g h)))  ≡⟨ cong₂ (λ p q → trans (sym p) (trans (get⁻¹-≡ l₁) q))
                                                                              (trans (sym $ cong-∘ _ _ _) $
                                                                               cong (cong _⁻¹_) $ cong-proj₁-cong₂-, _ _)
                                                                              (trans (sym $ cong-∘ _ _ _) $
                                                                               cong (cong (_∘ ∣_∣)) $ cong-proj₂-cong₂-, _ _) ⟩∎
    trans (sym (cong _⁻¹_ g)) (trans (get⁻¹-≡ l₁) (cong (_∘ ∣_∣) h))     ∎

-- Another equality characterisation lemma.

equality-characterisation₂ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B}
  (univ : Univalence (a ⊔ b)) →

  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (⟨ext⟩ (≃⇒≡ univ ∘ h ∘ ∣_∣))) ≡
     get⁻¹-≡ l₂)
equality-characterisation₂ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} univ =
  l₁ ≡ l₂                                                   ↝⟨ equality-characterisation₁ ⟩

  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (⟨ext⟩ (h ∘ ∣_∣))) ≡
     get⁻¹-≡ l₂)                                            ↝⟨ (∃-cong λ _ →
                                                                Σ-cong-contra (∀-cong ext λ _ → inverse $ ≡≃≃ univ) λ _ → F.id) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (⟨ext⟩ (≃⇒≡ univ ∘ h ∘ ∣_∣))) ≡
     get⁻¹-≡ l₂)                                            □
  where
  open Lens

------------------------------------------------------------------------
-- Conversions between different kinds of lenses

-- Lens A B is isomorphic to Higher.Lens A B (assuming univalence).
--
-- This proof was simplified following a suggestion by Paolo
-- Capriotti.
--
-- I have not proved that this isomorphism preserves getters and
-- setters.

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
      ; right-inverse-of = refl
      }
    ; left-inverse-of = refl
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
      (g ⁻¹_) ≡ H ∘ ∣_∣                                            ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (∀ b → g ⁻¹ b ≡ H ∣ b ∣)                                     ↝⟨ ∀-cong ext (λ _ →
                                                                        ≡-preserves-≃ ext univ univ
                                                                          (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ∘ lower) ⁻¹ b ≡ H ∣ b ∣)                           ↝⟨ Eq.extensionality-isomorphism ext ⟩
      ((g ∘ lower) ⁻¹_) ≡ H ∘ ∣_∣                                  ↝⟨ ≡⇒↝ _ $ cong (λ eq → (g ∘ lower ∘ _≃_.from eq ⁻¹_) ≡ H ∘ ∣_∣) lemma ⟩
      (g ∘ lower ∘ _≃_.from (≡⇒↝ _ (sym (refl _))) ⁻¹_) ≡ H ∘ ∣_∣  ↔⟨⟩
      proj₁ (_↔_.to lemma₂ g) ≡ H ∘ ∣_∣                            □
      where
      lemma =
        F.id                 ≡⟨ sym ≡⇒↝-refl ⟩
        ≡⇒↝ _ (refl _)       ≡⟨ cong (≡⇒↝ _) $ sym sym-refl ⟩∎
        ≡⇒↝ _ (sym (refl _)) ∎

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

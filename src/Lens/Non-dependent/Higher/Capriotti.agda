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
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
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

-- Coherently constant functions.
--
-- This definition is based on Paolo Capriotti's definition of higher
-- lenses.

Coherently-constant :
  {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Coherently-constant {A = A} {B = B} f =
  ∃ λ (g : ∥ A ∥ → B) → f ≡ g ∘ ∣_∣

-- Higher lenses, as presented by Paolo Capriotti, who seems to have
-- been first to describe a notion of higher lens
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹_)

-- Some derived definitions (based on Paolo's presentation).

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

  -- An equivalence.

  get⁻¹-≃ : ∀ b → get ⁻¹ b ≃ H ∣ b ∣
  get⁻¹-≃ = ≡⇒≃ ∘ ext⁻¹ get⁻¹-≡

  -- All the getter's fibres are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant b₁ b₂ =
    get ⁻¹ b₁  ↝⟨ get⁻¹-≃ b₁ ⟩
    H ∣ b₁ ∣   ↝⟨ ≡⇒≃ $ cong H $ T.truncation-is-proposition _ _ ⟩
    H ∣ b₂ ∣   ↝⟨ inverse $ get⁻¹-≃ b₂ ⟩□
    get ⁻¹ b₂  □

  -- A setter.

  set : A → B → A
  set a b =                    $⟨ _≃_.to (get⁻¹-constant (get a) b) ⟩
    (get ⁻¹ get a → get ⁻¹ b)  ↝⟨ _$ (a , refl _) ⟩
    get ⁻¹ b                   ↝⟨ proj₁ ⟩□
    A                          □

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

  lemma : ∀ _ (h : H l₁ ≡ H l₂) → _
  lemma g h =
    subst (λ (g , H) → g ⁻¹_ ≡ H ∘ ∣_∣) (cong₂ _,_ g h) (get⁻¹-≡ l₁)     ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (λ (g , _) → g ⁻¹_) (cong₂ _,_ g h)))
      (trans (get⁻¹-≡ l₁) (cong (λ (_ , H) → H ∘ ∣_∣) (cong₂ _,_ g h)))  ≡⟨ cong₂ (λ p q → trans (sym p) (trans (get⁻¹-≡ l₁) q))
                                                                              (trans (sym $ cong-∘ _ _ _) $
                                                                               cong (cong _⁻¹_) $ cong-proj₁-cong₂-, _ _)
                                                                              (trans (sym $ cong-∘ _ _ _) $
                                                                               cong (cong (_∘ ∣_∣)) $ cong-proj₂-cong₂-, _ h) ⟩∎
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

-- The lenses defined above can be converted to the lenses defined in
-- Higher.

Lens→Higher-lens : Lens A B → Higher.Lens A B
Lens→Higher-lens {A = A} {B = B} (g , H , eq) = record
  { R = Σ ∥ B ∥ H

  ; equiv =
      A                                      ↔⟨ (inverse $ drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                 other-singleton-contractible _) ⟩
      (∃ λ (a : A) → ∃ λ (b : B) → g a ≡ b)  ↔⟨ ∃-comm ⟩
      (∃ λ (b : B) → g ⁻¹ b)                 ↝⟨ (∃-cong λ b → ≡⇒↝ _ $ cong (_$ b) eq) ⟩
      (∃ λ (b : B) → H ∣ b ∣)                ↝⟨ (Σ-cong (inverse T.∥∥×≃) λ _ → ≡⇒↝ _ $ cong H $ T.truncation-is-proposition _ _) ⟩
      (∃ λ ((b , _) : ∥ B ∥ × B) → H b)      ↔⟨ Σ-assoc F.∘
                                                (∃-cong λ _ → ×-comm) F.∘
                                                inverse Σ-assoc ⟩□
      Σ ∥ B ∥ H × B                          □

  ; inhabited = proj₁
  }

-- The conversion preserves getters and setters.

Lens→Higher-lens-preserves-getters-and-setters :
  Preserves-getters-and-setters-→ A B Lens→Higher-lens
Lens→Higher-lens-preserves-getters-and-setters l@(g , H , eq) =
    refl _
  , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
    let h₁ = ≡⇒→ (cong (_$ g a) eq) (a , refl _)

        h₂ =
          _≃_.from (≡⇒≃ (cong H _))
            (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
               (≡⇒→ (cong H _) h₁))

        h₃ = ≡⇒→ (cong H _) h₁

        lemma =
          h₂                                                         ≡⟨ sym $ subst-in-terms-of-inverse∘≡⇒↝ equivalence _ _ _ ⟩

          subst H _
            (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
               (≡⇒→ (cong H _) h₁))                                  ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _)
                                                                                      (subst (H ∘ proj₁)
                                                                                         (sym (_≃_.left-inverse-of T.∥∥×≃ (∣ g a ∣ , b)))
                                                                                         x)) $ sym $
                                                                        subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
          subst H _
            (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
               (subst H _ h₁))                                       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                                        subst-∘ _ _ _ ⟩

          subst H _ (subst H _ (subst H _ h₁))                       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                                        subst-subst _ _ _ _ ⟩

          subst H _ (subst H _ h₁)                                   ≡⟨ subst-subst _ _ _ _ ⟩

          subst H _ h₁                                               ≡⟨ cong (λ eq → subst H eq h₁) $
                                                                        mono₁ 1 T.truncation-is-proposition _ _ ⟩

          subst H _ h₁                                               ≡⟨ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩∎

          ≡⇒→ (cong H _) h₁                                          ∎
    in
    (Higher.Lens.set (Lens→Higher-lens l) a b    ≡⟨⟩
     proj₁ (_≃_.from (≡⇒≃ (cong (_$ b) eq)) h₂)  ≡⟨ cong (λ h → proj₁ (_≃_.from (≡⇒≃ (cong (_$ b) eq)) h)) lemma ⟩
     proj₁ (_≃_.from (≡⇒≃ (cong (_$ b) eq)) h₃)  ≡⟨⟩
     Lens.set l a b                              ∎)

-- Lens A B is equivalent to Higher.Lens A B (assuming univalence).

Lens≃Higher-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Lens A B ≃ Higher.Lens A B
Lens≃Higher-lens {A = A} {B = B} ⊠ univ =
  Eq.↔→≃ to from to∘from from∘to
  where
  to = Lens→Higher-lens

  from : Higher.Lens A B → Lens A B
  from l =
      get
    , (λ _ → R)
    , (                      $⟨ (λ b → inverse (Higher.remainder≃get⁻¹ l b)) ⟩
       (∀ b → get ⁻¹ b ≃ R)  ↝⟨ (∀-cong _ λ _ → ≃⇒≡ univ) ⟩
       (∀ b → get ⁻¹ b ≡ R)  ↝⟨ ⟨ext⟩ ⟩□
       get ⁻¹_ ≡ const R     □)
    where
    open Higher.Lens l

  to∘from : ∀ l → to (from l) ≡ l
  to∘from l = _↔_.from (Higher.equality-characterisation₂ univ)
    ( (∥ B ∥ × R  ↔⟨ (drop-⊤-left-× λ r → _⇔_.to contractible⇔↔⊤ $
                      propositional⇒inhabited⇒contractible
                        T.truncation-is-proposition
                        (inhabited r)) ⟩□
       R          □)
    , (λ a →
         ≡⇒→ (cong (λ _ → R) (T.truncation-is-proposition _ _))
           (≡⇒→ (cong (_$ get a)
                   (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘
                           Higher.remainder≃get⁻¹ l)))
              (a , refl _))                                               ≡⟨ cong (λ eq → ≡⇒→ eq (≡⇒→ (cong (_$ get a)
                                                                                                         (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘
                                                                                                                 Higher.remainder≃get⁻¹ l)))
                                                                                                    (a , refl _))) $
                                                                             cong-const _ ⟩
         ≡⇒→ (refl _)
           (≡⇒→ (cong (_$ get a)
                   (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘
                           Higher.remainder≃get⁻¹ l)))
              (a , refl _))                                               ≡⟨ cong (_$ ≡⇒→ (cong (_$ get a)
                                                                                             (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘
                                                                                                     Higher.remainder≃get⁻¹ l)))
                                                                                        (a , refl _))
                                                                             ≡⇒→-refl ⟩
         ≡⇒→ (cong (_$ get a)
                (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘ Higher.remainder≃get⁻¹ l)))
           (a , refl _)                                                   ≡⟨ cong (λ eq → ≡⇒→ eq (a , refl _)) $
                                                                             cong-ext (≃⇒≡ univ ∘ inverse ∘ Higher.remainder≃get⁻¹ l) ⟩
         ≡⇒→ (≃⇒≡ univ (inverse (Higher.remainder≃get⁻¹ l (get a))))
           (a , refl _)                                                   ≡⟨ cong (_$ a , refl _) $
                                                                             ≡⇒→-≃⇒≡ equivalence univ ⟩

         _≃_.from (Higher.remainder≃get⁻¹ l (get a)) (a , refl _)         ≡⟨⟩

         remainder a                                                      ∎)
    , (λ _ → refl _)
    )
    where
    open Higher.Lens l

  from∘to : ∀ l → from (to l) ≡ l
  from∘to l = _≃_.from (equality-characterisation₂ univ)
    ( (λ _ → refl _)
    , Σ∥B∥H≃H
    , (trans (sym (cong _⁻¹_ (⟨ext⟩ λ _ → refl _)))
         (trans
            (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘ Higher.remainder≃get⁻¹ (to l)))
            (⟨ext⟩ (≃⇒≡ univ ∘ Σ∥B∥H≃H ∘ ∣_∣)))                           ≡⟨ cong (flip trans _) $
                                                                             trans (cong (sym ∘ cong _⁻¹_) ext-refl) $
                                                                             trans (cong sym $ cong-refl _) $
                                                                             sym-refl ⟩
       trans (refl _)
         (trans
            (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘ Higher.remainder≃get⁻¹ (to l)))
            (⟨ext⟩ (≃⇒≡ univ ∘ Σ∥B∥H≃H ∘ ∣_∣)))                           ≡⟨ trans-reflˡ _ ⟩

       trans
         (⟨ext⟩ (≃⇒≡ univ ∘ inverse ∘ Higher.remainder≃get⁻¹ (to l)))
         (⟨ext⟩ (≃⇒≡ univ ∘ Σ∥B∥H≃H ∘ ∣_∣))                               ≡⟨ sym $ ext-trans _ _ ⟩

       (⟨ext⟩ λ b →
        trans
          (≃⇒≡ univ (inverse (Higher.remainder≃get⁻¹ (to l) b)))
          (≃⇒≡ univ (Σ∥B∥H≃H ∣ b ∣)))                                     ≡⟨ (cong ⟨ext⟩ $ ⟨ext⟩ λ _ → sym $
                                                                              ≃⇒≡-∘ univ ext _ _) ⟩
       (⟨ext⟩ λ b →
        ≃⇒≡ univ (Σ∥B∥H≃H ∣ b ∣ F.∘
                  inverse (Higher.remainder≃get⁻¹ (to l) b)))             ≡⟨ (cong ⟨ext⟩ $ ⟨ext⟩ λ _ → cong (≃⇒≡ univ) $ Eq.lift-equality ext $
                                                                              ⟨ext⟩ (lemma _)) ⟩

       (⟨ext⟩ λ b → ≃⇒≡ univ (≡⇒≃ (ext⁻¹ get⁻¹-≡ b)))                     ≡⟨ (cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                              _≃_.left-inverse-of (≡≃≃ univ) _) ⟩

       (⟨ext⟩ λ b → ext⁻¹ get⁻¹-≡ b)                                      ≡⟨ _≃_.right-inverse-of (Eq.extensionality-isomorphism bad-ext) _ ⟩∎

       get⁻¹-≡                                                            ∎)
    )
    where
    open Lens l

    Σ∥B∥H≃H = λ b →
      Σ ∥ B ∥ H  ↔⟨ (drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                     propositional⇒inhabited⇒contractible
                       T.truncation-is-proposition b) ⟩□
      H b        □

    lemma : ∀ b (p : get ⁻¹ b) → _
    lemma b p@(a , get-a≡b) =
      _≃_.to (Σ∥B∥H≃H ∣ b ∣)
        (_≃_.from (Higher.remainder≃get⁻¹ (to l) b) p)                    ≡⟨⟩

      subst H _
        (≡⇒→ (cong H _)
           (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _)))                  ≡⟨ cong (subst H _) $ sym $
                                                                             subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩

      subst H _ (subst H _ (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _)))  ≡⟨ subst-subst _ _ _ _ ⟩

      subst H _ (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))              ≡⟨ cong (λ eq → subst H eq
                                                                                            (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))) $
                                                                             mono₁ 1 T.truncation-is-proposition _ _ ⟩
      subst H (cong ∣_∣ get-a≡b)
        (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))                      ≡⟨ elim¹
                                                                               (λ {b} eq →
                                                                                  subst H (cong ∣_∣ eq)
                                                                                    (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _)) ≡
                                                                                  ≡⇒→ (cong (_$ b) get⁻¹-≡) (a , eq))
                                                                               (
          subst H (cong ∣_∣ (refl _))
            (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))                        ≡⟨ cong (λ eq → subst H eq
                                                                                                  (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))) $
                                                                                   cong-refl _ ⟩
          subst H (refl _)
            (≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _))                        ≡⟨ subst-refl _ _ ⟩∎

          ≡⇒→ (cong (_$ get a) get⁻¹-≡) (a , refl _)                            ∎)
                                                                               get-a≡b ⟩
      ≡⇒→ (cong (_$ b) get⁻¹-≡) p                                         ≡⟨⟩

      ≡⇒→ (ext⁻¹ get⁻¹-≡ b) p                                             ∎

-- The equivalence preserves getters and setters.

Lens≃Higher-lens-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (bc : Block "conversion")
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Lens≃Higher-lens bc univ))
Lens≃Higher-lens-preserves-getters-and-setters ⊠ univ =
  Preserves-getters-and-setters-→-↠-⇔
    ⦃ L₂ = Higher.has-getter-and-setter ⦄
    (_≃_.surjection (Lens≃Higher-lens ⊠ univ))
    Lens→Higher-lens-preserves-getters-and-setters

-- An alternative proof showing that Lens A B is equivalent to
-- Higher.Lens A B (assuming univalence).
--
-- This proof was simplified following a suggestion by Paolo
-- Capriotti.
--
-- I have not proved that this equivalence preserves getters and
-- setters.

Lens≃Higher-lens′ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Lens A B ≃ Higher.Lens A B
Lens≃Higher-lens′ {a = a} {b = b} {A = A} {B = B} univ =

  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) →
     (g ⁻¹_) ≡ H ∘ ∣_∣)                                  ↔⟨ Σ-cong lemma₂ (λ _ → ∃-cong (lemma₃ _)) ⟩

  (∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
   ∃ λ (H : Pow a ∥ B ∥) →
     proj₁ p ≡ H ∘ ∣_∣)                                  ↔⟨ ∃-comm ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
     proj₁ p ≡ H ∘ ∣_∣)                                  ↔⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      A ≃ ∃ P × P ≡ H ∘ ∣_∣)                             ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ∘ ∣_∣ × A ≃ ∃ P)                             ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq →
                                                             Eq.≃-preserves ext F.id (∃-cong λ x → ≡⇒↝ _ (cong (_$ x) eq))) ⟩
  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ∘ ∣_∣ × A ≃ ∃ (H ∘ ∣_∣))                     ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   (∃ λ (P : Pow a B) → P ≡ H ∘ ∣_∣) ×
   A ≃ ∃ (H ∘ ∣_∣))                                      ↔⟨ (∃-cong λ _ →
                                                             drop-⊤-left-× λ _ →
                                                             _⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

  (∃ λ (H : Pow a ∥ B ∥) → A ≃ ∃ (H ∘ ∣_∣))              ↔⟨ inverse $
                                                            Σ-cong (inverse $ Pow↔Fam a ext univ) (λ _ →
                                                            Eq.≃-preserves ext F.id F.id) ⟩

  (∃ λ (H : Fam a ∥ B ∥) → A ≃ ∃ ((proj₂ H ⁻¹_) ∘ ∣_∣))  ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set ℓ) →
   ∃ λ (f : R → ∥ B ∥) → A ≃ ∃ ((f ⁻¹_) ∘ ∣_∣))          ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                             Eq.≃-preserves ext F.id
                            (∃ ((f ⁻¹_) ∘ ∣_∣)                 ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                     _⇔_.to contractible⇔↔⊤ $
                                                                       +⇒≡ T.truncation-is-proposition) ⟩
                             B × R                             ↔⟨ ×-comm ⟩□
                             R × B                             □)) ⟩

  (∃ λ (R : Set ℓ) → (R → ∥ B ∥) × (A ≃ (R × B)))        ↔⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (R : Set ℓ) → (A ≃ (R × B)) × (R → ∥ B ∥))        ↔⟨ inverse Higher.Lens-as-Σ ⟩□

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
  Lens A B              ↔⟨ Lens≃Higher-lens bc univ ⟩
  Higher.Lens A B       ↝⟨ Higher.Lens↔Traditional-lens bc univ A-set ⟩□
  Traditional.Lens A B  □

-- The isomorphism preserves getters and setters.

Lens↔Traditional-lens-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (bc : Block "conversion")
  (univ : Univalence (a ⊔ b))
  (s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_↔_.logical-equivalence (Lens↔Traditional-lens bc univ s))
Lens↔Traditional-lens-preserves-getters-and-setters bc univ s =
  Preserves-getters-and-setters-⇔-∘
    {f = _↔_.logical-equivalence $
           Higher.Lens↔Traditional-lens bc univ s}
    {g = _≃_.logical-equivalence $ Lens≃Higher-lens bc univ}
    (Higher.Lens↔Traditional-lens-preserves-getters-and-setters
       bc univ s)
    (Lens≃Higher-lens-preserves-getters-and-setters bc univ)

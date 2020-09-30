------------------------------------------------------------------------
-- A variant of Paolo Capriotti's variant of higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti.Variant
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

import Bijection equality-with-J as B
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Preimage equality-with-J
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher
import Lens.Non-dependent.Higher.Capriotti eq as Capriotti

private
  variable
    a b p : Level
    A B   : Set a

------------------------------------------------------------------------
-- The lens type family

-- Coherently constant type-valued functions.
--
-- This definition is based on Paolo Capriotti's definition of higher
-- lenses, but uses a family of equivalences instead of an equality.

Coherently-constant :
  {A : Set a} → (A → Set p) → Set (a ⊔ lsuc p)
Coherently-constant {p = p} {A = A} P =
  ∃ λ (Q : ∥ A ∥ → Set p) → ∀ x → P x ≃ Q ∣ x ∣

-- Paolo Capriotti's variant of higher lenses, but with a family of
-- equivalences instead of an equality.

Lens : Set a → Set b → Set (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹_)

-- Some derived definitions (based on Capriotti's).

module Lens {A : Set a} {B : Set b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- A predicate.

  H : Pow a ∥ B ∥
  H = proj₁ (proj₂ l)

  -- An equivalence.

  get⁻¹-≃ : ∀ b → get ⁻¹ b ≃ H ∣ b ∣
  get⁻¹-≃ = proj₂ (proj₂ l)

  -- All the getter's "preimages" are equivalent.

  get⁻¹-constant : (b₁ b₂ : B) → get ⁻¹ b₁ ≃ get ⁻¹ b₂
  get⁻¹-constant b₁ b₂ =
    get ⁻¹ b₁  ↝⟨ get⁻¹-≃ b₁ ⟩
    H ∣ b₁ ∣   ↝⟨ ≡⇒≃ $ cong H $ T.truncation-is-proposition _ _ ⟩
    H ∣ b₂ ∣   ↝⟨ inverse $ get⁻¹-≃ b₂ ⟩□
    get ⁻¹ b₂  □

  -- The two directions of get⁻¹-constant.

  get⁻¹-const : (b₁ b₂ : B) → get ⁻¹ b₁ → get ⁻¹ b₂
  get⁻¹-const b₁ b₂ = _≃_.to (get⁻¹-constant b₁ b₂)

  get⁻¹-const⁻¹ : (b₁ b₂ : B) → get ⁻¹ b₂ → get ⁻¹ b₁
  get⁻¹-const⁻¹ b₁ b₂ = _≃_.from (get⁻¹-constant b₁ b₂)

  -- Some coherence properties.

  get⁻¹-const-∘ :
    (b₁ b₂ b₃ : B) (p : get ⁻¹ b₁) →
    get⁻¹-const b₂ b₃ (get⁻¹-const b₁ b₂ p) ≡ get⁻¹-const b₁ b₃ p
  get⁻¹-const-∘ b₁ b₂ b₃ p =
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃_.to (get⁻¹-≃ b₂)
            (_≃_.from (get⁻¹-≃ b₂)
               (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
                  (_≃_.to (get⁻¹-≃ b₁) p)))))                   ≡⟨ cong (_≃_.from (get⁻¹-≃ _) ∘ ≡⇒→ _) $
                                                                   _≃_.right-inverse-of (get⁻¹-≃ _) _ ⟩
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
            (_≃_.to (get⁻¹-≃ b₁) p)))                           ≡⟨ cong (λ eq → _≃_.from (get⁻¹-≃ _) (_≃_.to eq (_≃_.to (get⁻¹-≃ _) _))) $ sym $
                                                                   ≡⇒≃-trans ext _ _ ⟩
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (trans (cong H $ T.truncation-is-proposition _ _)
              (cong H $ T.truncation-is-proposition _ _))
            (_≃_.to (get⁻¹-≃ b₁) p))                            ≡⟨ cong (λ eq → _≃_.from (get⁻¹-≃ b₃) (≡⇒→ eq _)) $
                                                                   trans (sym $ cong-trans _ _ _) $
                                                                   cong (cong H) $ mono₁ 1 T.truncation-is-proposition _ _ ⟩∎
    _≃_.from (get⁻¹-≃ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃_.to (get⁻¹-≃ b₁) p))                               ∎

  get⁻¹-const-id :
    (b : B) (p : get ⁻¹ b) → get⁻¹-const b b p ≡ p
  get⁻¹-const-id b p =
    get⁻¹-const b b p                                        ≡⟨ sym $ _≃_.left-inverse-of (get⁻¹-constant _ _) _ ⟩
    get⁻¹-const⁻¹ b b (get⁻¹-const b b (get⁻¹-const b b p))  ≡⟨ cong (get⁻¹-const⁻¹ b b) $ get⁻¹-const-∘ _ _ _ _ ⟩
    get⁻¹-const⁻¹ b b (get⁻¹-const b b p)                    ≡⟨ _≃_.left-inverse-of (get⁻¹-constant _ _) _ ⟩∎
    p                                                        ∎

  get⁻¹-const-inverse :
    (b₁ b₂ : B) (p : get ⁻¹ b₁) →
    get⁻¹-const b₁ b₂ p ≡ get⁻¹-const⁻¹ b₂ b₁ p
  get⁻¹-const-inverse b₁ b₂ p =
    sym $ _≃_.to-from (get⁻¹-constant _ _) (
      get⁻¹-const b₂ b₁ (get⁻¹-const b₁ b₂ p)  ≡⟨ get⁻¹-const-∘ _ _ _ _ ⟩
      get⁻¹-const b₁ b₁ p                      ≡⟨ get⁻¹-const-id _ _ ⟩∎
      p                                        ∎)

  -- A setter.

  set : A → B → A
  set a b =                    $⟨ get⁻¹-const _ _ ⟩
    (get ⁻¹ get a → get ⁻¹ b)  ↝⟨ _$ (a , refl _) ⟩
    get ⁻¹ b                   ↝⟨ proj₁ ⟩□
    A                          □

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    get (proj₁ (get⁻¹-const (get a) b (a , refl _)))  ≡⟨ proj₂ (get⁻¹-const (get a) b (a , refl _)) ⟩∎
    b                                                 ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    proj₁ (get⁻¹-const (get a) (get a) (a , refl _))  ≡⟨ cong proj₁ $ get⁻¹-const-id _ _ ⟩∎
    a                                                 ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl _))  ≡⟨ elim¹
                                                                      (λ {b} eq →
                                                                         proj₁ (get⁻¹-const (get (set a b₁)) b₂ (set a b₁ , refl _)) ≡
                                                                         proj₁ (get⁻¹-const b b₂ (set a b₁ , eq)))
                                                                      (refl _)
                                                                      (get-set a b₁) ⟩

    proj₁ (get⁻¹-const b₁ b₂ (set a b₁ , get-set a b₁))          ≡⟨⟩

    proj₁ (get⁻¹-const b₁ b₂
             (get⁻¹-const (get a) b₁ (a , refl _)))              ≡⟨ cong proj₁ $ get⁻¹-const-∘ _ _ _ _ ⟩∎

    proj₁ (get⁻¹-const (get a) b₂ (a , refl _))                  ∎

  -- TODO: Can get-set-get and get-set-set be proved for the lens laws
  -- given above?

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Conversion between two kinds of lenses

-- The lenses defined above are equivalent to Capriotti's (assuming
-- univalence).

≃Capriotti :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Lens A B ≃ Capriotti.Lens A B
≃Capriotti {a = a} {A = A} {B = B} univ =
  Lens A B                                                            ↔⟨⟩
  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $ ≡≃≃ univ) ⟩
  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) → ∀ b → g ⁻¹ b ≡ H ∣ b ∣)  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → Eq.extensionality-isomorphism bad-ext) ⟩
  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) → g ⁻¹_ ≡ H ∘ ∣_∣)         ↔⟨⟩
  Capriotti.Lens A B                                                  □

-- The conversion preserves getters and setters.

≃Capriotti-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (≃Capriotti univ))
≃Capriotti-preserves-getters-and-setters {A = A} {B = B} univ =
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (≃Capriotti univ)) λ l →
      refl _
    , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
      (let eq₁ = cong (H l) $
                   T.truncation-is-proposition ∣ get l a ∣ ∣ b ∣
           eq₂ = ⟨ext⟩ (≃⇒≡ univ ∘ get⁻¹-≃ l)
       in
       proj₁ (_≃_.from (≡⇒≃ (cong (_$ b) eq₂))
                (≡⇒→ eq₁ (≡⇒→ (cong (_$ get l a) eq₂) (a , refl _))))   ≡⟨ cong₂ (λ p q → proj₁ (_≃_.from p (≡⇒→ eq₁ (_≃_.to q (a , refl _)))))
                                                                             (lemma l _)
                                                                             (lemma l _) ⟩∎
       proj₁ (_≃_.from (get⁻¹-≃ l b)
                (≡⇒→ eq₁ (_≃_.to (get⁻¹-≃ l (get l a)) (a , refl _))))  ∎)
  where
  open Lens

  lemma :
    ∀ (l : Lens A B) b →
    ≡⇒≃ (cong (_$ b) (⟨ext⟩ (≃⇒≡ univ ∘ get⁻¹-≃ l))) ≡ get⁻¹-≃ l b
  lemma l b =
    ≡⇒≃ (cong (_$ b) (⟨ext⟩ (≃⇒≡ univ ∘ get⁻¹-≃ l)))  ≡⟨ cong ≡⇒≃ $ cong-ext (≃⇒≡ univ ∘ get⁻¹-≃ l) ⟩
    ≡⇒≃ (≃⇒≡ univ (get⁻¹-≃ l b))                      ≡⟨ _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    get⁻¹-≃ l b                                       ∎

------------------------------------------------------------------------
-- Equality characterisation lemmas

-- An equality characterisation lemma.

equality-characterisation₁ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)
equality-characterisation₁ {a = a} {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                          ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Σ-assoc ⟩

  ((get l₁ , H l₁) , get⁻¹-≃ l₁) ≡ ((get l₂ , H l₂) , get⁻¹-≃ l₂)  ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

  (∃ λ (eq : (get l₁ , H l₁) ≡ (get l₂ , H l₂)) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣) eq (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↝⟨ (Σ-cong-contra ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ ((g , h) : get l₁ ≡ get l₂ × H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹-≃ l₁) ≡
     get⁻¹-≃ l₂)                                                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                       Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → ∀ b → g ⁻¹ b ≃ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹-≃ l₁) b ≡
           get⁻¹-≃ l₂ b)                                           ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                       push-subst-application _ _) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹-≃ l₁ b) ≡
           get⁻¹-≃ l₂ b)                                           ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                       ≃-to-≡↔≡ ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     _≃_.to (subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
               (cong₂ _,_ g h) (get⁻¹-≃ l₁ b)) p ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                       ≡⇒↝ _ $ cong (_≡ _) $ lemma _ _ _ _) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                      □
  where
  open Lens

  lemma : ∀ _ _ _ _ → _ ≡ _
  lemma g h b p =
    _≃_.to (subst (λ (g , H) → g ⁻¹ b ≃ H ∣ b ∣)
              (cong₂ _,_ g h) (get⁻¹-≃ l₁ b)) p                 ≡⟨ cong (_$ p) Eq.to-subst ⟩

    subst (λ (g , H) → g ⁻¹ b → H ∣ b ∣)
      (cong₂ _,_ g h) (_≃_.to (get⁻¹-≃ l₁ b)) p                 ≡⟨ subst-→ ⟩

    subst (λ (g , H) → H ∣ b ∣) (cong₂ _,_ g h)
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (λ (g , H) → g ⁻¹ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ subst-∘ _ _ _ ⟩

    subst (_$ ∣ b ∣) (cong proj₂ $ cong₂ _,_ g h)
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (λ (g , H) → g ⁻¹ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ cong₂ (λ p q → subst (λ (H : Pow a _) → H ∣ b ∣)
                                                                                    p (_≃_.to (get⁻¹-≃ l₁ b) q))
                                                                     (cong-proj₂-cong₂-, _ _)
                                                                     (subst-∘ _ _ _) ⟩
    subst (_$ ∣ b ∣) h
      (_≃_.to (get⁻¹-≃ l₁ b)
         (subst (_⁻¹ b) (cong proj₁ $ sym $ cong₂ _,_ g h) p))  ≡⟨ cong (λ eq → subst (_$ ∣ b ∣) h
                                                                                  (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) eq p))) $
                                                                   trans (cong-sym _ _) $
                                                                   cong sym $ cong-proj₁-cong₂-, _ _ ⟩∎
    subst (_$ ∣ b ∣) h
      (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p))         ∎

-- Another equality characterisation lemma.

equality-characterisation₂ :
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst id (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)
equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ ⊠ ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym g) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                        Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                        F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst (_$ ∣ b ∣) (⟨ext⟩ h)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        ≡⇒↝ _ $ cong (_≡ _) $
                                                                        subst-ext _ _) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst id (h ∣ b ∣)
       (_≃_.to (get⁻¹-≃ l₁ b) (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃_.to (get⁻¹-≃ l₂ b) p)                                       □
  where
  open Lens

------------------------------------------------------------------------
-- Some results related to fibres of Lens.set

-- When proving that Lens.set ⁻¹ s is a proposition, for
-- s : A → B → A, one can assume that B is inhabited.
--
-- This result is due to Andrea Vezzosi.

[codomain-inhabited→proposition]→proposition :
  {s : A → B → A} →
  (B → Is-proposition (Lens.set ⁻¹ s)) ≃
  Is-proposition (Lens.set ⁻¹ s)
[codomain-inhabited→proposition]→proposition {B = B} {s = s} =
  block λ b →

  (B → Is-proposition (Lens.set ⁻¹ s))      ↝⟨ inverse $ T.universal-property (H-level-propositional ext 1) ⟩
  (∥ B ∥ → Is-proposition (Lens.set ⁻¹ s))  ↔⟨⟩
  (∥ B ∥ → (p q : Lens.set ⁻¹ s) → p ≡ q)   ↔⟨ (∀-cong ext λ _ → Π-comm) F.∘ Π-comm ⟩
  ((p q : Lens.set ⁻¹ s) → ∥ B ∥ → p ≡ q)   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → lemma b _ _) ⟩
  ((p q : Lens.set ⁻¹ s) → p ≡ q)           ↔⟨⟩
  Is-proposition (Lens.set ⁻¹ s)            □
  where
  open Lens

  lemma :
    (b : Block "equality-characterisation") →
    (p₁ p₂ : Lens.set ⁻¹ s) →
    (∥ B ∥ → p₁ ≡ p₂) ≃ (p₁ ≡ p₂)
  lemma b p₁@(l₁ , eq₁) p₂@(l₂ , eq₂) =
    (∥ B ∥ → p₁ ≡ p₂)                                           ↝⟨ (∀-cong ext λ _ → ec) ⟩

    (∥ B ∥ →
     ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ T.push-∥∥ (∣_∣ ∘ get l₁) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∥ B ∥ →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → T.push-∥∥ id) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∥ B ∥ →
     ∃ λ (f : ∀ b p →
              subst id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → T.push-∥∥ ∣_∣) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∥ B ∥ →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → T.drop-∥∥ (∣_∣ ∘ get l₁)) ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∃ λ (f : ∀ b p →
              subst id (h ∣ b ∣)
                (_≃_.to (get⁻¹-≃ l₁ b)
                   (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
              _≃_.to (get⁻¹-≃ l₂ b) p) →
       ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                      (_≃_.from (equality-characterisation₂ b)
                         (g , h , f)) eq₁) a ≡
             ext⁻¹ eq₂ a)                                       ↝⟨ inverse ec ⟩□

    p₁ ≡ p₂                                                     □
    where
    ec =
      p₁ ≡ p₂                                                     ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

      (∃ λ (l : l₁ ≡ l₂) →
         subst (λ l → Lens.set l ≡ s) l eq₁ ≡ eq₂)                ↝⟨ (∃-cong λ _ → inverse $
                                                                      Eq.≃-≡ $ inverse $ Eq.extensionality-isomorphism ext) ⟩
      (∃ λ (l : l₁ ≡ l₂) →
         ext⁻¹ (subst (λ l → Lens.set l ≡ s) l eq₁) ≡ ext⁻¹ eq₂)  ↝⟨ (∃-cong λ _ → inverse $
                                                                      Eq.extensionality-isomorphism ext) ⟩
      (∃ λ (l : l₁ ≡ l₂) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s) l eq₁) a ≡
               ext⁻¹ eq₂ a)                                       ↝⟨ (Σ-cong-contra (inverse $ equality-characterisation₂ b) λ _ → F.id) ⟩

      (∃ λ (l : ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
                ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
                  ∀ b p →
                  subst id (h ∣ b ∣)
                    (_≃_.to (get⁻¹-≃ l₁ b)
                       (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
                  _≃_.to (get⁻¹-≃ l₂ b) p) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                        (_≃_.from (equality-characterisation₂ b)
                           l) eq₁) a ≡
               ext⁻¹ eq₂ a)                                       ↔⟨ (∃-cong λ _ → inverse Σ-assoc) F.∘ inverse Σ-assoc ⟩□

      (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
       ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∃ λ (f : ∀ b p →
                subst id (h ∣ b ∣)
                  (_≃_.to (get⁻¹-≃ l₁ b)
                     (subst (_⁻¹ b) (sym (⟨ext⟩ g)) p)) ≡
                _≃_.to (get⁻¹-≃ l₂ b) p) →
         ∀ a → ext⁻¹ (subst (λ l → Lens.set l ≡ s)
                        (_≃_.from (equality-characterisation₂ b)
                           (g , h , f)) eq₁) a ≡
               ext⁻¹ eq₂ a)                                       □

-- The previous result holds also for the lenses in Higher (assuming
-- univalence).

[codomain-inhabited→proposition]→proposition-for-higher :
  {A : Set a} {B : Set b} {s : A → B → A} →
  Univalence (a ⊔ b) →
  (B → Is-proposition (Higher.Lens.set ⁻¹ s)) ≃
  Is-proposition (Higher.Lens.set ⁻¹ s)
[codomain-inhabited→proposition]→proposition-for-higher
  {A = A} {B = B} {s = s} univ =

  (B → Is-proposition (Higher.Lens.set ⁻¹ s))  ↝⟨ (∀-cong ext λ _ → H-level-cong ext 1 lemma) ⟩
  (B → Is-proposition (Lens.set ⁻¹ s))         ↝⟨ [codomain-inhabited→proposition]→proposition ⟩
  Is-proposition (Lens.set ⁻¹ s)               ↝⟨ inverse $ H-level-cong ext 1 lemma ⟩□
  Is-proposition (Higher.Lens.set ⁻¹ s)        □
  where
  lemma : Higher.Lens.set ⁻¹ s ≃ Lens.set ⁻¹ s
  lemma = block λ b →
    (∃ λ (l : Higher.Lens A B) → Higher.Lens.set l ≡ s)        ↝⟨ (Σ-cong (inverse $ Capriotti.Lens≃Higher-lens b univ) λ _ →
                                                                   ≡⇒↝ _ $ cong (_≡ s) $ sym $ proj₂ $
                                                                   proj₂ (Capriotti.Lens≃Higher-lens-preserves-getters-and-setters b univ) _) ⟩
    (∃ λ (l : Capriotti.Lens A B) → Capriotti.Lens.set l ≡ s)  ↝⟨ (Σ-cong (inverse $ ≃Capriotti univ) λ _ →
                                                                   ≡⇒↝ _ $ cong (_≡ s) $ sym $ proj₂ $
                                                                   proj₂ (≃Capriotti-preserves-getters-and-setters univ) _) ⟩□
    (∃ λ (l : Lens A B) → Lens.set l ≡ s)                      □

-- If a certain variant of Higher.lenses-equal-if-setters-equal can be
-- proved, then Higher.Lens.set ⁻¹ s is a proposition (assuming
-- univalence).

lenses-equal-if-setters-equal→set⁻¹-proposition :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b)) →
  ((l₁ l₂ : Higher.Lens A B) →
   B →
   (s : Higher.Lens.set l₁ ≡ Higher.Lens.set l₂) →
   ∃ λ (l : l₁ ≡ l₂) → cong Higher.Lens.set l ≡ s) →
  (s : A → B → A) →
  Is-proposition (Higher.Lens.set ⁻¹ s)
lenses-equal-if-setters-equal→set⁻¹-proposition
  {B = B} univ lenses-equal-if-setters-equal s =
                                               $⟨ lemma ⟩
  (B → Is-proposition (Higher.Lens.set ⁻¹ s))  ↝⟨ [codomain-inhabited→proposition]→proposition-for-higher univ ⟩□
  Is-proposition (Higher.Lens.set ⁻¹ s)        □
  where
  lemma : B → Is-proposition (Higher.Lens.set ⁻¹ s)
  lemma b (l₁ , set-l₁≡s) (l₂ , set-l₂≡s) = Σ-≡,≡→≡
    lemma₁
    (subst (λ l → set l ≡ s) lemma₁ set-l₁≡s                     ≡⟨ subst-∘ _ _ _ ⟩
     subst (_≡ s) (cong set lemma₁) set-l₁≡s                     ≡⟨ subst-trans-sym ⟩
     trans (sym (cong set lemma₁)) set-l₁≡s                      ≡⟨ cong (λ eq → trans (sym eq) set-l₁≡s) lemma₂ ⟩
     trans (sym (trans set-l₁≡s (sym set-l₂≡s))) set-l₁≡s        ≡⟨ cong (λ eq → trans eq set-l₁≡s) $ sym-trans _ _ ⟩
     trans (trans (sym (sym set-l₂≡s)) (sym set-l₁≡s)) set-l₁≡s  ≡⟨ trans-[trans-sym]- _ _ ⟩
     sym (sym set-l₂≡s)                                          ≡⟨ sym-sym _ ⟩∎
     set-l₂≡s                                                    ∎)
    where
    open Higher.Lens

    lemma′ =
      lenses-equal-if-setters-equal l₁ l₂ b
        (set l₁  ≡⟨ set-l₁≡s ⟩
         s       ≡⟨ sym set-l₂≡s ⟩∎
         set l₂  ∎)

    lemma₁ = proj₁ lemma′
    lemma₂ = proj₂ lemma′

-- If a certain variant of Higher.lenses-equal-if-setters-equal can be
-- proved, then lenses with equal setters are equal (assuming
-- univalence).
--
-- TODO: Can one, given the same assumptions, prove that
-- Higher.Lens.set is an embedding?

lenses-equal-if-setters-equal→lenses-equal-if-setters-equal :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ((l₁ l₂ : Higher.Lens A B) →
   B →
   (s : Higher.Lens.set l₁ ≡ Higher.Lens.set l₂) →
   ∃ λ (l : l₁ ≡ l₂) → cong Higher.Lens.set l ≡ s) →
  (l₁ l₂ : Higher.Lens A B) →
  Higher.Lens.set l₁ ≡ Higher.Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal→lenses-equal-if-setters-equal
  univ lenses-equal-if-setters-equal l₁ l₂ s =
  cong proj₁ (
    (l₁ , s)       ≡⟨ lenses-equal-if-setters-equal→set⁻¹-proposition
                        univ lenses-equal-if-setters-equal (Higher.Lens.set l₂) _ _ ⟩∎
    (l₂ , refl _)  ∎)

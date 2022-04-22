------------------------------------------------------------------------
-- Paolo Capriotti's variant of higher lenses
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Coherently-constant eq using (Coherently-constant)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Preimage equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher eq as Higher
import Lens.Non-dependent.Higher.Capriotti.Variant eq as Variant
import Lens.Non-dependent.Traditional eq as Traditional

private
  variable
    a b p : Level
    A B   : Type a
    P Q   : A → Type p

------------------------------------------------------------------------
-- Coherently-constant

-- A preservation lemma for Coherently-constant.
--
-- Note that P and Q must target the same universe.

Coherently-constant-map :
  {P : A → Type p} {Q : B → Type p} →
  Univalence p →
  (f : B → A) →
  (∀ x → P (f x) ≃ Q x) →
  Coherently-constant P → Coherently-constant Q
Coherently-constant-map {P = P} {Q = Q} univ f P≃Q (R , P≡R) =
    R ∘ T.∥∥-map f
  , ⟨ext⟩ λ x → ≃⇒≡ univ
      (Q x        ↝⟨ inverse $ P≃Q x ⟩
       P (f x)    ↝⟨ ≡⇒≃ $ cong (_$ f x) P≡R ⟩□
       R ∣ f x ∣  □)

-- Coherently-constant is, in a certain sense, closed under Σ.
--
-- This lemma is due to Paolo Capriotti.

Coherently-constant-Σ :
  Coherently-constant P →
  Coherently-constant Q →
  Coherently-constant (λ x → ∃ λ (y : P x) → Q (x , y))
Coherently-constant-Σ {P = P} {Q = Q} (P′ , p) (Q′ , q) =
    (λ x → ∃ λ (y : P′ x) →
               Q′ (T.elim
                     (λ x → P′ x → ∥ ∃ P ∥)
                     (λ _ → Π-closure ext 1 λ _ →
                            T.truncation-is-proposition)
                     (λ x y → ∣ x , subst id (sym (p′ x)) y ∣)
                     x y))
  , (⟨ext⟩ λ x →

     ((∃ λ (y : P x) → Q (x , y))                                ≡⟨ (cong (uncurry Σ) $ Σ-≡,≡→≡ (p′ x) $ ⟨ext⟩ λ y →

        subst (λ P → P → Type _) (p′ x) (λ y → Q (x , y)) y          ≡⟨ subst-→-domain _ _ ⟩

        Q (x , subst id (sym (p′ x)) y)                              ≡⟨ cong (_$ (x , subst id (sym (p′ x)) y)) q ⟩∎

        Q′ ∣ x , subst id (sym (p′ x)) y ∣                           ∎) ⟩∎

      (∃ λ (y : P′ ∣ x ∣) → Q′ ∣ x , subst id (sym (p′ x)) y ∣)  ∎))
  where
  p′ : ∀ _ → _
  p′ x = cong (_$ x) p

-- If the domain of f is stable, then there is a split surjection from
-- Constant f to Coherently-constant f.
--
-- In "Notions of Anonymous Existence in Martin-Löf Type Theory" Kraus
-- Escardó, Coquand and Altenkirch prove that Constant f implies
-- Coherently-constant f when the domain of f is stable, and the other
-- direction holds without the assumption.

Constant↠Coherently-constant :
  {f : A → B} →
  (∥ A ∥ → A) →
  Constant f ↠ Coherently-constant f
Constant↠Coherently-constant {f = f} s = record
  { logical-equivalence = record
    { to   = λ c → f ∘ s
           , ⟨ext⟩ λ x → c x (s ∣ x ∣)
    ; from = λ (g , eq) x y →
        f x      ≡⟨ cong (_$ x) eq ⟩
        g ∣ x ∣  ≡⟨ cong g $ T.truncation-is-proposition ∣ x ∣ ∣ y ∣ ⟩
        g ∣ y ∣  ≡⟨ cong (_$ y) $ sym eq ⟩∎
        f y      ∎
    }
  ; right-inverse-of = λ (g , eq) → Σ-≡,≡→≡
      (f ∘ s        ≡⟨ cong (_∘ s) eq ⟩
       g ∘ ∣_∣ ∘ s  ≡⟨ (⟨ext⟩ λ x → cong g $ T.truncation-is-proposition ∣ s x ∣ x) ⟩∎
       g            ∎)
      (subst (λ g → f ≡ g ∘ ∣_∣)
         (trans (cong (_∘ s) eq)
            (⟨ext⟩ λ x →
             cong g (T.truncation-is-proposition ∣ s x ∣ x)))
         (⟨ext⟩ λ x →
          trans (cong (_$ x) eq)
            (trans (cong g (T.truncation-is-proposition
                              ∣ x ∣ (∣ s ∣ x ∣ ∣)))
               (cong (_$ s ∣ x ∣) (sym eq))))                            ≡⟨ trans (subst-∘ _ _ _) $
                                                                            sym trans-subst ⟩
       trans
         (⟨ext⟩ λ x →
          trans (cong (_$ x) eq)
            (trans (cong g (T.truncation-is-proposition
                              ∣ x ∣ (∣ s ∣ x ∣ ∣)))
               (cong (_$ s ∣ x ∣) (sym eq))))
         (cong (_∘ ∣_∣) $
          trans (cong (_∘ s) eq)
            (⟨ext⟩ λ x →
             cong g (T.truncation-is-proposition ∣ s x ∣ x)))            ≡⟨ cong₂ trans
                                                                              (trans (ext-trans ext) $
                                                                               cong₂ trans
                                                                                 (_≃_.right-inverse-of
                                                                                    (Eq.extensionality-isomorphism ext) _)
                                                                                 (trans (ext-trans ext) $
                                                                                  cong (trans _) $
                                                                                  cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                  trans (sym $ cong-∘ _ _ _) $
                                                                                  cong (cong _) $ cong-sym _ _))
                                                                              (trans (cong-trans _ _ _) $
                                                                               cong₂ trans
                                                                                 (cong-∘ _ _ _)
                                                                                 (cong-pre-∘-ext ext ext)) ⟩
       trans
         (trans eq
            (trans (⟨ext⟩ λ x →
                    cong g (T.truncation-is-proposition
                              ∣ x ∣ (∣ s ∣ x ∣ ∣)))
               (⟨ext⟩ λ x → cong (_$ x) (sym (cong (_∘ s ∘ ∣_∣) eq)))))
         (trans (cong (_∘ s ∘ ∣_∣) eq)
            (⟨ext⟩ λ x →
             cong g (T.truncation-is-proposition
                       (∣ s ∣ x ∣ ∣) ∣ x ∣)))                            ≡⟨ trans (trans-assoc _ _ _) $
                                                                            cong (trans _) $
                                                                            trans (trans-assoc _ _ _) $
                                                                            cong₂ trans
                                                                              (trans (cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                      trans (cong (cong _) $
                                                                                             H-level.mono₁ 1 T.truncation-is-proposition _ _) $
                                                                                      cong-sym _ _) $
                                                                               ext-sym ext)
                                                                              (cong (flip trans _) $
                                                                               _≃_.right-inverse-of
                                                                                 (Eq.extensionality-isomorphism ext) _) ⟩
       trans eq
         (trans (sym $
                 ⟨ext⟩ λ x →
                 cong g (T.truncation-is-proposition
                           (∣ s ∣ x ∣ ∣) ∣ x ∣))
            (trans (sym (cong (_∘ s ∘ ∣_∣) eq))
               (trans (cong (_∘ s ∘ ∣_∣) eq)
                  (⟨ext⟩ λ x →
                   cong g (T.truncation-is-proposition
                          (∣ s ∣ x ∣ ∣) ∣ x ∣)))))                       ≡⟨ trans (cong (trans _) $
                                                                                   trans (cong (trans _) $
                                                                                          trans-sym-[trans] _ _) $
                                                                                   trans-symˡ _) $
                                                                            trans-reflʳ _ ⟩∎
       eq                                                                ∎)
  }

------------------------------------------------------------------------
-- The lens type family

-- Higher lenses, as presented by Paolo Capriotti, who seems to have
-- been first to describe a notion of higher lens
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹_)

-- Some derived definitions (based on Paolo's presentation).

module Lens {A : Type a} {B : Type b} (l : Lens A B) where

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
     get⁻¹-≡ l₂)                                                         ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                             Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                             F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     trans (sym (cong _⁻¹_ (⟨ext⟩ g)))
       (trans (get⁻¹-≡ l₁) (cong (_∘ ∣_∣) (⟨ext⟩ h))) ≡
     get⁻¹-≡ l₂)                                                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                             cong (λ eq → trans _ (trans _ eq) ≡ _) $
                                                                             cong-pre-∘-ext ext ext) ⟩□
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
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
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

-- Variant.Coherently-constant P is equivalent to
-- Coherently-constant P (assuming univalence).

Variant-coherently-constant≃Coherently-constant :
  {P : A → Type p} →
  Univalence p →
  Variant.Coherently-constant P ≃ Coherently-constant P
Variant-coherently-constant≃Coherently-constant
  {A = A} {p = p} {P = P} univ =

  Variant.Coherently-constant P                     ↔⟨⟩
  (∃ λ (H : ∥ A ∥ → Type p) → ∀ b → P b ≃ H ∣ b ∣)  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse $ ≡≃≃ univ) ⟩
  (∃ λ (H : ∥ A ∥ → Type p) → ∀ b → P b ≡ H ∣ b ∣)  ↝⟨ (∃-cong λ _ → Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (H : ∥ A ∥ → Type p) → P ≡ H ∘ ∣_∣)          ↔⟨⟩
  Coherently-constant P                             □

-- The lenses defined above are equivalent to those defined in Variant
-- (assuming univalence).

Variant-lens≃Lens :
  {A : Type a} {B : Type b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Variant.Lens A B ≃ Lens A B
Variant-lens≃Lens {a = a} {A = A} {B = B} ⊠ univ =
  Variant.Lens A B                                             ↔⟨⟩
  (∃ λ (get : A → B) → Variant.Coherently-constant (get ⁻¹_))  ↝⟨ (∃-cong λ _ → Variant-coherently-constant≃Coherently-constant univ) ⟩
  (∃ λ (get : A → B) → Coherently-constant (get ⁻¹_))          ↔⟨⟩
  Lens A B                                                     □

-- The conversion preserves getters and setters.

Variant-lens≃Lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bc : Block "conversion")
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Variant-lens≃Lens bc univ))
Variant-lens≃Lens-preserves-getters-and-setters
  {A = A} {B = B} bc@⊠ univ =
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (Variant-lens≃Lens bc univ)) λ l →
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
  open Variant.Lens

  lemma :
    ∀ (l : Variant.Lens A B) b →
    ≡⇒≃ (cong (_$ b) (⟨ext⟩ (≃⇒≡ univ ∘ get⁻¹-≃ l))) ≡ get⁻¹-≃ l b
  lemma l b =
    ≡⇒≃ (cong (_$ b) (⟨ext⟩ (≃⇒≡ univ ∘ get⁻¹-≃ l)))  ≡⟨ cong ≡⇒≃ $ cong-ext {f≡g = ≃⇒≡ univ ∘ get⁻¹-≃ l} ext ⟩
    ≡⇒≃ (≃⇒≡ univ (get⁻¹-≃ l b))                      ≡⟨ _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    get⁻¹-≃ l b                                       ∎

-- The lenses defined above are equivalent to those defined in Higher
-- (assuming univalence).

Lens≃Higher-lens :
  {A : Type a} {B : Type b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Lens A B ≃ Higher.Lens A B
Lens≃Higher-lens {A = A} {B = B} bc univ =
  Lens A B          ↝⟨ inverse $ Variant-lens≃Lens bc univ ⟩
  Variant.Lens A B  ↝⟨ Variant.Lens≃Higher-lens bc univ ⟩□
  Higher.Lens A B   □

-- The conversion preserves getters and setters.

Lens≃Higher-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bc : Block "conversion")
  (univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (Lens≃Higher-lens bc univ))
Lens≃Higher-lens-preserves-getters-and-setters bc univ =
  Preserves-getters-and-setters-⇔-∘
    {f = _≃_.logical-equivalence $ Variant.Lens≃Higher-lens bc univ}
    (Variant.Lens≃Higher-lens-preserves-getters-and-setters bc univ)
    (Preserves-getters-and-setters-⇔-inverse
       {f = _≃_.logical-equivalence $ Variant-lens≃Lens bc univ}
       (Variant-lens≃Lens-preserves-getters-and-setters bc univ))

-- An alternative proof showing that Lens A B is equivalent to
-- Higher.Lens A B (assuming univalence).
--
-- This proof was simplified following a suggestion by Paolo
-- Capriotti.
--
-- I have not proved that this equivalence preserves getters and
-- setters.

Lens≃Higher-lens′ :
  {A : Type a} {B : Type b} →
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

  (∃ λ (R : Type ℓ) →
   ∃ λ (f : R → ∥ B ∥) → A ≃ ∃ ((f ⁻¹_) ∘ ∣_∣))          ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                             Eq.≃-preserves ext F.id
                            (∃ ((f ⁻¹_) ∘ ∣_∣)                 ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                     _⇔_.to contractible⇔↔⊤ $
                                                                       +⇒≡ T.truncation-is-proposition) ⟩
                             B × R                             ↔⟨ ×-comm ⟩□
                             R × B                             □)) ⟩

  (∃ λ (R : Type ℓ) → (R → ∥ B ∥) × (A ≃ (R × B)))       ↔⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (R : Type ℓ) → (A ≃ (R × B)) × (R → ∥ B ∥))       ↔⟨ inverse Higher.Lens-as-Σ ⟩□

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
      let lemma =
            F.id                 ≡⟨ sym ≡⇒↝-refl ⟩
            ≡⇒↝ _ (refl _)       ≡⟨ cong (≡⇒↝ _) $ sym sym-refl ⟩∎
            ≡⇒↝ _ (sym (refl _)) ∎
      in
      (g ⁻¹_) ≡ H ∘ ∣_∣                                            ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (∀ b → g ⁻¹ b ≡ H ∣ b ∣)                                     ↝⟨ ∀-cong ext (λ _ →
                                                                        ≡-preserves-≃ ext univ univ
                                                                          (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ∘ lower) ⁻¹ b ≡ H ∣ b ∣)                           ↝⟨ Eq.extensionality-isomorphism ext ⟩
      ((g ∘ lower) ⁻¹_) ≡ H ∘ ∣_∣                                  ↝⟨ ≡⇒↝ _ $ cong (λ eq → (g ∘ lower ∘ _≃_.from eq ⁻¹_) ≡ H ∘ ∣_∣) lemma ⟩
      (g ∘ lower ∘ _≃_.from (≡⇒↝ _ (sym (refl _))) ⁻¹_) ≡ H ∘ ∣_∣  ↔⟨⟩
      proj₁ (_↔_.to lemma₂ g) ≡ H ∘ ∣_∣                            □

-- If the domain A is a set, then Traditional.Lens A B and Lens A B
-- are isomorphic (assuming univalence).

Lens↔Traditional-lens :
  {A : Type a} {B : Type b} →
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
  {A : Type a} {B : Type b}
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

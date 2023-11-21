------------------------------------------------------------------------
-- The lens type in Lens.Non-dependent.Higher.Capriotti.Variant, but
-- with erased "proofs"
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti.Variant.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq using (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages.Cubical eq as ECP
  using (_⁻¹ᴱ_)
open import Erased.Cubical eq
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Preimage equality-with-J using (_⁻¹_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Erased eq as Higher
import Lens.Non-dependent.Higher.Capriotti.Variant eq as V

private
  variable
    a b p : Level
    A B   : Type a

------------------------------------------------------------------------
-- The lens type family

-- Coherently constant type-valued functions.

Coherently-constant :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant {p = p} {A = A} P =
  ∃ λ (Q : ∥ A ∥ → Type p) → ∀ x → P x ≃ᴱ Q ∣ x ∣

-- Higher lenses with erased "proofs".

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹ᴱ_)

-- In erased contexts Lens A B is equivalent to V.Lens A B.

@0 Lens≃Variant-lens : Lens A B ≃ V.Lens A B
Lens≃Variant-lens =
  (∃ λ get → ∃ λ Q → ∀ x → get ⁻¹ᴱ x ≃ᴱ Q ∣ x ∣)  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse
                                                      EEq.≃≃≃ᴱ) ⟩
  (∃ λ get → ∃ λ Q → ∀ x → get ⁻¹ᴱ x ≃  Q ∣ x ∣)  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                      Eq.≃-preserves ext (inverse ECP.⁻¹≃⁻¹ᴱ) F.id) ⟩□
  (∃ λ get → ∃ λ Q → ∀ x → get ⁻¹  x ≃  Q ∣ x ∣)  □

-- Some derived definitions.

module Lens {A : Type a} {B : Type b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- A predicate.

  H : Pow a ∥ B ∥
  H = proj₁ (proj₂ l)

  -- An equivalence (with erased proofs).

  get⁻¹ᴱ-≃ᴱ : ∀ b → get ⁻¹ᴱ b ≃ᴱ H ∣ b ∣
  get⁻¹ᴱ-≃ᴱ = proj₂ (proj₂ l)

  -- All the getter's "preimages" are equivalent (with erased proofs).

  get⁻¹ᴱ-constant : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ ≃ᴱ get ⁻¹ᴱ b₂
  get⁻¹ᴱ-constant b₁ b₂ =
    get ⁻¹ᴱ b₁  ↝⟨ get⁻¹ᴱ-≃ᴱ b₁ ⟩
    H ∣ b₁ ∣    ↔⟨ ≡⇒≃ $ cong H $ T.truncation-is-proposition _ _ ⟩
    H ∣ b₂ ∣    ↝⟨ inverse $ get⁻¹ᴱ-≃ᴱ b₂ ⟩□
    get ⁻¹ᴱ b₂  □

  -- The two directions of get⁻¹ᴱ-constant.

  get⁻¹ᴱ-const : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂
  get⁻¹ᴱ-const b₁ b₂ = _≃ᴱ_.to (get⁻¹ᴱ-constant b₁ b₂)

  get⁻¹ᴱ-const⁻¹ᴱ : (b₁ b₂ : B) → get ⁻¹ᴱ b₂ → get ⁻¹ᴱ b₁
  get⁻¹ᴱ-const⁻¹ᴱ b₁ b₂ = _≃ᴱ_.from (get⁻¹ᴱ-constant b₁ b₂)

  -- Some coherence properties.

  @0 get⁻¹ᴱ-const-∘ :
    (b₁ b₂ b₃ : B) (p : get ⁻¹ᴱ b₁) →
    get⁻¹ᴱ-const b₂ b₃ (get⁻¹ᴱ-const b₁ b₂ p) ≡ get⁻¹ᴱ-const b₁ b₃ p
  get⁻¹ᴱ-const-∘ b₁ b₂ b₃ p =
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₂)
            (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₂)
               (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
                  (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))))                ≡⟨ cong (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) ∘ ≡⇒→ _) $
                                                                   _≃ᴱ_.right-inverse-of (get⁻¹ᴱ-≃ᴱ _) _ ⟩
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
            (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))                        ≡⟨ cong (λ eq → _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) (_≃_.to eq (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ _) _))) $ sym $
                                                                   ≡⇒≃-trans ext _ _ ⟩
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (≡⇒→ (trans (cong H $ T.truncation-is-proposition _ _)
              (cong H $ T.truncation-is-proposition _ _))
            (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p))                         ≡⟨ cong (λ eq → _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃) (≡⇒→ eq _)) $
                                                                   trans (sym $ cong-trans _ _ _) $
                                                                   cong (cong H) $ mono₁ 1 T.truncation-is-proposition _ _ ⟩∎
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (≡⇒→ (cong H $ T.truncation-is-proposition _ _)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p))                            ∎

  @0 get⁻¹ᴱ-const-id :
    (b : B) (p : get ⁻¹ᴱ b) → get⁻¹ᴱ-const b b p ≡ p
  get⁻¹ᴱ-const-id b p =
    get⁻¹ᴱ-const b b p                                           ≡⟨ sym $ _≃ᴱ_.left-inverse-of (get⁻¹ᴱ-constant _ _) _ ⟩
    get⁻¹ᴱ-const⁻¹ᴱ b b (get⁻¹ᴱ-const b b (get⁻¹ᴱ-const b b p))  ≡⟨ cong (get⁻¹ᴱ-const⁻¹ᴱ b b) $ get⁻¹ᴱ-const-∘ _ _ _ _ ⟩
    get⁻¹ᴱ-const⁻¹ᴱ b b (get⁻¹ᴱ-const b b p)                     ≡⟨ _≃ᴱ_.left-inverse-of (get⁻¹ᴱ-constant _ _) _ ⟩∎
    p                                                            ∎

  @0 get⁻¹ᴱ-const-inverse :
    (b₁ b₂ : B) (p : get ⁻¹ᴱ b₁) →
    get⁻¹ᴱ-const b₁ b₂ p ≡ get⁻¹ᴱ-const⁻¹ᴱ b₂ b₁ p
  get⁻¹ᴱ-const-inverse b₁ b₂ p =
    sym $ _≃_.to-from (EEq.≃ᴱ→≃ (get⁻¹ᴱ-constant _ _)) (
      get⁻¹ᴱ-const b₂ b₁ (get⁻¹ᴱ-const b₁ b₂ p)  ≡⟨ get⁻¹ᴱ-const-∘ _ _ _ _ ⟩
      get⁻¹ᴱ-const b₁ b₁ p                       ≡⟨ get⁻¹ᴱ-const-id _ _ ⟩∎
      p                                          ∎)

  -- A setter.

  set : A → B → A
  set a b =                      $⟨ get⁻¹ᴱ-const _ _ ⟩
    (get ⁻¹ᴱ get a → get ⁻¹ᴱ b)  ↝⟨ _$ (a , [ refl _ ]) ⟩
    get ⁻¹ᴱ b                    ↝⟨ proj₁ ⟩□
    A                            □

  -- Lens laws.

  @0 get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    get (proj₁ (get⁻¹ᴱ-const (get a) b (a , [ refl _ ])))  ≡⟨ erased (proj₂ (get⁻¹ᴱ-const (get a) b (a , [ refl _ ]))) ⟩∎
    b                                                      ∎

  @0 set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    proj₁ (get⁻¹ᴱ-const (get a) (get a) (a , [ refl _ ]))  ≡⟨ cong proj₁ $ get⁻¹ᴱ-const-id _ _ ⟩∎
    a                                                      ∎

  @0 set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    proj₁ (get⁻¹ᴱ-const (get (set a b₁)) b₂ (set a b₁ , [ refl _ ]))  ≡⟨ elim¹
                                                                           (λ {b} eq →
                                                                              proj₁ (get⁻¹ᴱ-const (get (set a b₁)) b₂ (set a b₁ , [ refl _ ])) ≡
                                                                              proj₁ (get⁻¹ᴱ-const b b₂ (set a b₁ , [ eq ])))
                                                                           (refl _)
                                                                           (get-set a b₁) ⟩

    proj₁ (get⁻¹ᴱ-const b₁ b₂ (set a b₁ , [ get-set a b₁ ]))          ≡⟨ cong (proj₁ ∘ get⁻¹ᴱ-const b₁ b₂ ∘ (_ ,_)) $
                                                                         Erased-η ⟩
    proj₁ (get⁻¹ᴱ-const b₁ b₂
             (get⁻¹ᴱ-const (get a) b₁ (a , [ refl _ ])))              ≡⟨ cong proj₁ $ get⁻¹ᴱ-const-∘ _ _ _ _ ⟩∎

    proj₁ (get⁻¹ᴱ-const (get a) b₂ (a , [ refl _ ]))                  ∎

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
-- Equality characterisation lemmas

opaque

  -- An equality characterisation lemma.

  @0 equality-characterisation₁ :
    {l₁ l₂ : Lens A B} →
    let open Lens in

    (l₁ ≡ l₂)
      ≃
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (h : H l₁ ≡ H l₂) →
       ∀ b p →
       subst (_$ ∣ b ∣) h
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
  equality-characterisation₁ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                           ↝⟨ inverse $ Eq.≃-≡ Lens≃Variant-lens ⟩

    l₁′ ≡ l₂′                                                         ↝⟨ V.equality-characterisation₁ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (h : H l₁ ≡ H l₂) →
       ∀ b p →
       subst (_$ ∣ b ∣) h
         (_≃_.to (V.Lens.get⁻¹-≃ l₁′ b) (subst (_⁻¹ b) (sym g) p)) ≡
       _≃_.to (V.Lens.get⁻¹-≃ l₂′ b) p)                               ↝⟨ (∃-cong λ g → ∃-cong λ h → ∀-cong ext λ b →
                                                                          Π-cong ext ECP.⁻¹≃⁻¹ᴱ λ p →
                                                                          ≡⇒↝ _ $ cong (λ p′ → subst (_$ _) h (_≃_.to (V.Lens.get⁻¹-≃ l₁′ _) p′) ≡
                                                                                               _≃_.to (V.Lens.get⁻¹-≃ l₂′ _) p)
                                                                            (
       subst (_⁻¹ b) (sym g) p                                               ≡⟨ elim₁
                                                                                  (λ g → subst (_⁻¹ b) (sym g) p ≡
                                                                                         Σ-map id erased (subst (_⁻¹ᴱ b) (sym g) (Σ-map id [_]→ p)))
                                                                                  (
         subst (_⁻¹ b) (sym (refl _)) p                                            ≡⟨ trans (cong (flip (subst (_⁻¹ b)) _) sym-refl) $
                                                                                      subst-refl _ _ ⟩

         p                                                                         ≡⟨ cong (Σ-map id erased) $ sym $
                                                                                      trans (cong (flip (subst (_⁻¹ᴱ b)) _) sym-refl) $
                                                                                      subst-refl _ _ ⟩∎
         Σ-map id erased
           (subst (_⁻¹ᴱ b) (sym (refl _)) (Σ-map id [_]→ p))                       ∎)
                                                                                  _ ⟩
       Σ-map id erased (subst (_⁻¹ᴱ b) (sym g) (Σ-map id [_]→ p))            ≡⟨⟩

       _≃_.from ECP.⁻¹≃⁻¹ᴱ
         (subst (_⁻¹ᴱ b) (sym g) (_≃_.to ECP.⁻¹≃⁻¹ᴱ p))                      ∎)) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (h : H l₁ ≡ H l₂) →
       ∀ b p →
       subst (_$ ∣ b ∣) h
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b)
            ( proj₁ (subst (_⁻¹ᴱ b) (sym g) p)
            , [ erased (proj₂ (subst (_⁻¹ᴱ b) (sym g) p)) ]
            )) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                    ↝⟨ (∃-cong λ _ → ∃-cong λ h → ∀-cong ext λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $
                                                                          cong ((_≡ _) ∘ subst (_$ ∣ _ ∣) h ∘ _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ _) ∘ (_ ,_)) $
                                                                          Erased-η) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (h : H l₁ ≡ H l₂) →
       ∀ b p →
       subst (_$ ∣ b ∣) h
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                    □
    where
    open Lens

    l₁′ l₂′ : V.Lens A B
    l₁′ = _≃_.to Lens≃Variant-lens l₁
    l₂′ = _≃_.to Lens≃Variant-lens l₂

opaque

  -- Another equality characterisation lemma.

  @0 equality-characterisation₂ :
    {l₁ l₂ : Lens A B} →
    let open Lens in

    (l₁ ≡ l₂)
      ≃
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∀ b p →
       subst id (h ∣ b ∣)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
  equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                               ↝⟨ equality-characterisation₁ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (h : H l₁ ≡ H l₂) →
       ∀ b p →
       subst (_$ ∣ b ∣) h
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                              Σ-cong-contra (Eq.extensionality-isomorphism ext) λ _ →
                                                                              F.id) ⟩
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∀ b p →
       subst (_$ ∣ b ∣) (⟨ext⟩ h)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (_≡ _) $
                                                                              subst-ext ext) ⟩□
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∀ b p →
       subst id (h ∣ b ∣)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        □
    where
    open Lens

opaque

  -- Yet another equality characterisation lemma.

  @0 equality-characterisation₃ :
    {l₁ l₂ : Lens A B} →
    let open Lens in

    (l₁ ≡ l₂)
      ≃
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
       ∀ b p →
       _≃_.to (h ∣ b ∣)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
  equality-characterisation₃ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                               ↝⟨ equality-characterisation₂ ⟩

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
       ∀ b p →
       subst id (h ∣ b ∣)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (∃-cong λ _ →
                                                                              Σ-cong-contra (∀-cong ext λ _ → inverse $ ≡≃≃ univ) λ _ → F.id) ⟩
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
       ∀ b p →
       subst id (≃⇒≡ univ (h ∣ b ∣))
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (_≡ _) $
                                                                              trans (subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                              cong (λ eq → _≃_.to eq _) $
                                                                              _≃_.right-inverse-of (≡≃≃ univ) _) ⟩□
    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
       ∀ b p →
       _≃_.to (h ∣ b ∣)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
       _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        □
    where
    open Lens

------------------------------------------------------------------------
-- Conversion functions

opaque

  -- The lenses defined above can be converted to and from the lenses
  -- defined in Higher.

  Lens⇔Higher-lens : Lens A B ⇔ Higher.Lens A B
  Lens⇔Higher-lens {A = A} {B = B} = record
    { to = λ (g , H , eq) → record
             { R = Σ ∥ B ∥ H

             ; equiv =
                 A                                               ↝⟨ (inverse $ drop-⊤-right λ _ → _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤
                                                                     Contractibleᴱ-Erased-other-singleton) ⟩
                 (∃ λ (a : A) → ∃ λ (b : B) → Erased (g a ≡ b))  ↔⟨ ∃-comm ⟩
                 (∃ λ (b : B) → g ⁻¹ᴱ b)                         ↝⟨ ∃-cong eq ⟩
                 (∃ λ (b : B) → H ∣ b ∣)                         ↔⟨ (Σ-cong (inverse T.∥∥×≃) λ _ → ≡⇒≃ $ cong H $ T.truncation-is-proposition _ _) ⟩
                 (∃ λ ((b , _) : ∥ B ∥ × B) → H b)               ↔⟨ Σ-assoc F.∘
                                                                    (∃-cong λ _ → ×-comm) F.∘
                                                                    inverse Σ-assoc ⟩□
                 Σ ∥ B ∥ H × B                                   □

             ; inhabited = proj₁
             }
    ; from = λ l →
                 Higher.Lens.get l
               , (λ _ → Higher.Lens.R l)
               , (λ b → inverse (Higher.remainder≃ᴱget⁻¹ᴱ l b))
    }

opaque
  unfolding Lens⇔Higher-lens

  -- The conversion preserves getters and setters.

  Lens⇔Higher-lens-preserves-getters-and-setters :
    Preserves-getters-and-setters-⇔ A B Lens⇔Higher-lens
  Lens⇔Higher-lens-preserves-getters-and-setters =
      (λ l@(g , H , eq) →
           refl _
         , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
           let h₁ = _≃ᴱ_.to (eq (g a)) (a , [ refl _ ])

               h₂ =
                 _≃_.from (≡⇒≃ (cong H _))
                   (subst (H ∘ proj₁) (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                      (≡⇒→ (cong H _) h₁))

               h₃ = ≡⇒→ (cong H _) h₁

               lemma =
                 h₂                                         ≡⟨ sym $ subst-in-terms-of-inverse∘≡⇒↝ equivalence _ _ _ ⟩

                 subst H _
                   (subst (H ∘ proj₁)
                      (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                      (≡⇒→ (cong H _) h₁))                  ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _)
                                                                             (subst (H ∘ proj₁)
                                                                                (sym (_≃_.left-inverse-of T.∥∥×≃ (∣ g a ∣ , b)))
                                                                                x)) $ sym $
                                                               subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
                 subst H _
                   (subst (H ∘ proj₁)
                      (sym (_≃_.left-inverse-of T.∥∥×≃ _))
                      (subst H _ h₁))                       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                               subst-∘ _ _ _ ⟩

                 subst H _ (subst H _ (subst H _ h₁))       ≡⟨ cong (λ x → subst H (sym $ T.truncation-is-proposition _ _) x) $
                                                               subst-subst _ _ _ _ ⟩

                 subst H _ (subst H _ h₁)                   ≡⟨ subst-subst _ _ _ _ ⟩

                 subst H _ h₁                               ≡⟨ cong (λ eq → subst H eq h₁) $
                                                               mono₁ 1 T.truncation-is-proposition _ _ ⟩

                 subst H _ h₁                               ≡⟨ subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩∎

                 ≡⇒→ (cong H _) h₁                          ∎
           in
           proj₁ (_≃ᴱ_.from (eq b) h₂)  ≡⟨ cong (λ h → proj₁ (_≃ᴱ_.from (eq b) h)) lemma ⟩∎
           proj₁ (_≃ᴱ_.from (eq b) h₃)  ∎)
    , (λ l →
           refl _
         , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
           Lens.set (_⇔_.from Lens⇔Higher-lens l) a b        ≡⟨⟩

           _≃ᴱ_.from (Higher.Lens.equiv l)
             ( ≡⇒→ (cong (λ _ → Higher.Lens.R l) _)
                 (Higher.Lens.remainder l a)
             , b
             )                                               ≡⟨ cong (λ eq → _≃ᴱ_.from (Higher.Lens.equiv l) (≡⇒→ eq _ , b)) $
                                                                cong-const _ ⟩
           _≃ᴱ_.from (Higher.Lens.equiv l)
             (≡⇒→ (refl _) (Higher.Lens.remainder l a) , b)  ≡⟨ cong (λ f → _≃ᴱ_.from (Higher.Lens.equiv l) (f _ , b)) $
                                                                ≡⇒→-refl ⟩
           _≃ᴱ_.from (Higher.Lens.equiv l)
             (Higher.Lens.remainder l a , b)                 ≡⟨⟩

           Higher.Lens.set l a b                             ∎)

-- Lens A B is equivalent to Higher.Lens A B (with erased proofs).

Lens≃ᴱHigher-lens : Lens A B ≃ᴱ Higher.Lens A B
Lens≃ᴱHigher-lens {A = A} {B = B} =
  EEq.↔→≃ᴱ
    (_⇔_.to Lens⇔Higher-lens)
    (_⇔_.from Lens⇔Higher-lens)
    to∘from
    from∘to
  where
  opaque
    unfolding Lens⇔Higher-lens

    @0 to∘from :
      (l : Higher.Lens A B) →
      _⇔_.to Lens⇔Higher-lens (_⇔_.from Lens⇔Higher-lens l) ≡ l
    to∘from l = _↔_.from Higher.equality-characterisation₂
      ( (∥ B ∥ × R  ↔⟨ (drop-⊤-left-× λ r → _⇔_.to contractible⇔↔⊤ $
                        propositional⇒inhabited⇒contractible
                          T.truncation-is-proposition
                          (inhabited r)) ⟩□
         R          □)
      , (λ a →
           ≡⇒→ (cong (λ _ → R) (T.truncation-is-proposition _ _))
             (remainder a)                                         ≡⟨ cong (λ eq → ≡⇒→ eq _) $ cong-const _ ⟩

           ≡⇒→ (refl _) (remainder a)                              ≡⟨ cong (_$ _) ≡⇒→-refl ⟩∎

           remainder a                                             ∎)
      , (λ _ → refl _)
      )
      where
      open Higher.Lens l

    @0 from∘to :
      (l : Lens A B) →
      _⇔_.from Lens⇔Higher-lens (_⇔_.to Lens⇔Higher-lens l) ≡ l
    from∘to l = _≃_.from equality-characterisation₃
      ( (λ _ → refl _)
      , Σ∥B∥H≃H
      , (λ b p@(a , [ get-a≡b ]) →
           _≃_.to (Σ∥B∥H≃H ∣ b ∣)
             (_≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                           (_⇔_.to Lens⇔Higher-lens l) b)
                (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ λ _ → refl _)) p))       ≡⟨ cong (_≃_.to (Σ∥B∥H≃H ∣ b ∣) ∘
                                                                              _≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                                                                                           (_⇔_.to Lens⇔Higher-lens l) b)) $
                                                                        trans (cong (flip (subst (_⁻¹ᴱ b)) p) $
                                                                               trans (cong sym $ ext-refl ext) $
                                                                               sym-refl) $
                                                                        subst-refl _ _ ⟩
           _≃_.to (Σ∥B∥H≃H ∣ b ∣)
             (_≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                           (_⇔_.to Lens⇔Higher-lens l) b)
                p)                                                   ≡⟨⟩

           _≃_.to (Σ∥B∥H≃H ∣ b ∣)
             (Higher.Lens.remainder (_⇔_.to Lens⇔Higher-lens l) a)   ≡⟨⟩

           subst H _
             (≡⇒→ (cong H _) (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a))
                                (a , [ refl _ ])))                   ≡⟨ cong (subst H _) $ sym $
                                                                        subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩

           subst H _ (subst H _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a))
                                   (a , [ refl _ ])))                ≡⟨ subst-subst _ _ _ _ ⟩

           subst H _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ]))  ≡⟨ cong (λ eq → subst H eq (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ]))) $
                                                                        mono₁ 1 T.truncation-is-proposition _ _ ⟩
           subst H (cong ∣_∣ get-a≡b)
             (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ]))          ≡⟨ elim¹
                                                                          (λ {b} eq →
                                                                             subst H (cong ∣_∣ eq)
                                                                               (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ])) ≡
                                                                             _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) (a , [ eq ]))
                                                                          (
             subst H (cong ∣_∣ (refl _))
               (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ]))              ≡⟨ trans (cong (flip (subst H) _) $ cong-refl _) $
                                                                              subst-refl _ _ ⟩
             _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a)) (a , [ refl _ ])                  ∎)
                                                                          _ ⟩

           _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) (p .proj₁ , [ erased (p .proj₂) ])  ≡⟨ cong (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ _) ∘ (_ ,_))
                                                                        Erased-η ⟩∎
           _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) p                                   ∎)
      )
      where
      open Lens l

      Σ∥B∥H≃H : ∀ b → Σ ∥ B ∥ H ≃ H b
      Σ∥B∥H≃H b =
        Σ ∥ B ∥ H  ↔⟨ (drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                       propositional⇒inhabited⇒contractible
                         T.truncation-is-proposition b) ⟩□
        H b        □

-- The equivalence preserves getters and setters.

Lens≃ᴱHigher-lens-preserves-getters-and-setters :
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence Lens≃ᴱHigher-lens)
Lens≃ᴱHigher-lens-preserves-getters-and-setters =
  Lens⇔Higher-lens-preserves-getters-and-setters

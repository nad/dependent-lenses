------------------------------------------------------------------------
-- A variant of the lens type in
-- Lens.Non-dependent.Higher.Capriotti.Variant.Erased
--
-- This variant uses ∥_∥ᴱ instead of ∥_∥.
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq
  using (_≃ᴱ_; _⁻¹ᴱ_; Contractibleᴱ)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq using (∥_∥; ∣_∣)
open import H-level.Truncation.Propositional.Erased eq as T
  using (∥_∥ᴱ; ∣_∣)
open import Preimage equality-with-J using (_⁻¹_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Erased eq as Higher
import Lens.Non-dependent.Higher.Capriotti.Variant eq as V

private
  variable
    a b p q  : Level
    A B      : Type a
    Q        : A → Type q
    b₁ b₂ b₃ : A

------------------------------------------------------------------------
-- The lens type family

-- Coherently constant type-valued functions.

Coherently-constant :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant {p = p} {A = A} P =
  ∃ λ (Q : ∥ A ∥ᴱ → Type p) →
    (∀ x → P x ≃ᴱ Q ∣ x ∣) ×
    ∃ λ (Q≃Q : ∀ x y → Q x ≃ᴱ Q y) →
      Erased (∀ x y → Q≃Q x y ≡
                      ≡⇒↝ _ (cong Q (T.truncation-is-proposition x y)))

-- The "last part" of Coherently-constant is contractible (in erased
-- contexts).

@0 Contractible-last-part-of-Coherently-constant :
  Contractible
    (∃ λ (Q≃Q : ∀ x y → Q x ≃ᴱ Q y) →
     Erased (∀ x y → Q≃Q x y ≡
                     ≡⇒↝ _ (cong Q (T.truncation-is-proposition x y))))
Contractible-last-part-of-Coherently-constant {Q = Q} =                  $⟨ Contractibleᴱ-Erased-singleton ⟩
  Contractibleᴱ
    (∃ λ (Q≃Q : ∀ x y → Q x ≃ᴱ Q y) →
     Erased (Q≃Q ≡ λ x y →
                   ≡⇒↝ _ (cong Q (T.truncation-is-proposition x y))))    ↝⟨ (EEq.Contractibleᴱ-cong _ $
                                                                             ∃-cong λ _ → Erased-cong (inverse $
                                                                             Eq.extensionality-isomorphism ext F.∘
                                                                             ∀-cong ext λ _ → Eq.extensionality-isomorphism ext)) ⦂ (_ → _) ⟩
  Contractibleᴱ
    (∃ λ (Q≃Q : ∀ x y → Q x ≃ᴱ Q y) →
     Erased (∀ x y → Q≃Q x y ≡
                     ≡⇒↝ _ (cong Q (T.truncation-is-proposition x y))))  ↝⟨ EEq.Contractibleᴱ→Contractible ⟩□

  Contractible
    (∃ λ (Q≃Q : ∀ x y → Q x ≃ᴱ Q y) →
     Erased (∀ x y → Q≃Q x y ≡
                     ≡⇒↝ _ (cong Q (T.truncation-is-proposition x y))))  □

-- Higher lenses with erased "proofs".

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹ᴱ_)

-- In erased contexts Lens A B is equivalent to V.Lens A B.

@0 Lens≃Variant-lens : Lens A B ≃ V.Lens A B
Lens≃Variant-lens {B = B} =
  (∃ λ get → ∃ λ (Q : ∥ B ∥ᴱ → _) → (∀ x → get ⁻¹ᴱ x ≃ᴱ Q ∣ x ∣) × _)  ↔⟨ (∃-cong λ _ → ∃-cong λ _ → drop-⊤-right λ _ →
                                                                           _⇔_.to contractible⇔↔⊤
                                                                           Contractible-last-part-of-Coherently-constant) ⟩
  (∃ λ get → ∃ λ (Q : ∥ B ∥ᴱ → _) → ∀ x → get ⁻¹ᴱ x ≃ᴱ Q ∣ x ∣)        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                           EEq.≃≃≃ᴱ ext) ⟩
  (∃ λ get → ∃ λ (Q : ∥ B ∥ᴱ → _) → ∀ x → get ⁻¹ᴱ x ≃  Q ∣ x ∣)        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                           Eq.≃-preserves ext (inverse EEq.⁻¹≃⁻¹ᴱ) F.id) ⟩
  (∃ λ get → ∃ λ (Q : ∥ B ∥ᴱ → _) → ∀ x → get ⁻¹  x ≃  Q ∣ x ∣)        ↝⟨ (∃-cong λ _ →
                                                                           Σ-cong {k₁ = equivalence} (→-cong₁ ext T.∥∥ᴱ≃∥∥) λ _ → F.id) ⟩□
  (∃ λ get → ∃ λ (Q : ∥ B ∥  → _) → ∀ x → get ⁻¹  x ≃  Q ∣ x ∣)        □

-- Some derived definitions.

module Lens {A : Type a} {B : Type b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- A predicate.

  H : Pow a ∥ B ∥ᴱ
  H = proj₁ (proj₂ l)

  -- An equivalence (with erased proofs).

  get⁻¹ᴱ-≃ᴱ : ∀ b → get ⁻¹ᴱ b ≃ᴱ H ∣ b ∣
  get⁻¹ᴱ-≃ᴱ = proj₁ (proj₂ (proj₂ l))

  -- The predicate H is weakly constant (up to _≃ᴱ_).

  H≃ᴱH : ∀ b₁ b₂ → H b₁ ≃ᴱ H b₂
  H≃ᴱH = proj₁ (proj₂ (proj₂ (proj₂ l)))

  -- In erased contexts H≃ᴱH can be expressed using
  -- T.truncation-is-proposition.

  @0 H≃ᴱH≡ :
    H≃ᴱH b₁ b₂ ≡ ≡⇒↝ _ (cong H (T.truncation-is-proposition b₁ b₂))
  H≃ᴱH≡ = erased (proj₂ (proj₂ (proj₂ (proj₂ l)))) _ _

  -- A variant of the previous result.

  @0 to-H≃ᴱH≡ :
    _≃ᴱ_.to (H≃ᴱH b₁ b₂) ≡ subst H (T.truncation-is-proposition b₁ b₂)
  to-H≃ᴱH≡ {b₁ = b₁} {b₂ = b₂} =
    _≃ᴱ_.to (H≃ᴱH b₁ b₂)                                          ≡⟨ cong _≃ᴱ_.to H≃ᴱH≡ ⟩
    _≃ᴱ_.to (≡⇒↝ _ (cong H (T.truncation-is-proposition b₁ b₂)))  ≡⟨ (⟨ext⟩ λ _ → sym $ subst-in-terms-of-≡⇒↝ equivalenceᴱ _ _ _) ⟩∎
    subst H (T.truncation-is-proposition b₁ b₂)                   ∎

  -- All the getter's "preimages" are equivalent (with erased proofs).

  get⁻¹ᴱ-constant : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ ≃ᴱ get ⁻¹ᴱ b₂
  get⁻¹ᴱ-constant b₁ b₂ =
    get ⁻¹ᴱ b₁  ↝⟨ get⁻¹ᴱ-≃ᴱ b₁ ⟩
    H ∣ b₁ ∣    ↝⟨ H≃ᴱH ∣ b₁ ∣ ∣ b₂ ∣ ⟩
    H ∣ b₂ ∣    ↝⟨ inverse $ get⁻¹ᴱ-≃ᴱ b₂ ⟩□
    get ⁻¹ᴱ b₂  □

  -- The two directions of get⁻¹ᴱ-constant.

  get⁻¹ᴱ-const : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂
  get⁻¹ᴱ-const b₁ b₂ = _≃ᴱ_.to (get⁻¹ᴱ-constant b₁ b₂)

  get⁻¹ᴱ-const⁻¹ᴱ : (b₁ b₂ : B) → get ⁻¹ᴱ b₂ → get ⁻¹ᴱ b₁
  get⁻¹ᴱ-const⁻¹ᴱ b₁ b₂ = _≃ᴱ_.from (get⁻¹ᴱ-constant b₁ b₂)

  -- Some coherence properties.

  @0 H≃ᴱH-∘ :
    _≃ᴱ_.to (H≃ᴱH b₂ b₃) ∘ _≃ᴱ_.to (H≃ᴱH b₁ b₂) ≡ _≃ᴱ_.to (H≃ᴱH b₁ b₃)
  H≃ᴱH-∘ {b₂ = b₂} {b₃ = b₃} {b₁ = b₁} =
    _≃ᴱ_.to (H≃ᴱH b₂ b₃) ∘ _≃ᴱ_.to (H≃ᴱH b₁ b₂)         ≡⟨ cong₂ (λ f g → f ∘ g) to-H≃ᴱH≡ to-H≃ᴱH≡ ⟩

    subst H (T.truncation-is-proposition b₂ b₃) ∘
    subst H (T.truncation-is-proposition b₁ b₂)         ≡⟨ (⟨ext⟩ λ _ → subst-subst _ _ _ _) ⟩

    subst H (trans (T.truncation-is-proposition b₁ b₂)
               (T.truncation-is-proposition b₂ b₃))     ≡⟨ cong (subst H) $
                                                           mono₁ 1 T.truncation-is-proposition _ _ ⟩

    subst H (T.truncation-is-proposition b₁ b₃)         ≡⟨ sym to-H≃ᴱH≡ ⟩∎

    _≃ᴱ_.to (H≃ᴱH b₁ b₃)                                ∎

  @0 H≃ᴱH-id : ∀ {b} → _≃ᴱ_.to (H≃ᴱH b b) ≡ id
  H≃ᴱH-id {b = b} =
    _≃ᴱ_.to (H≃ᴱH b b)                         ≡⟨ to-H≃ᴱH≡ ⟩
    subst H (T.truncation-is-proposition b b)  ≡⟨ cong (subst H) $
                                                  mono₁ 1 T.truncation-is-proposition _ _ ⟩
    subst H (refl b)                           ≡⟨ (⟨ext⟩ λ _ → subst-refl _ _) ⟩∎
    id                                         ∎

  @0 H≃ᴱH-inverse : _≃ᴱ_.to (H≃ᴱH b₁ b₂) ≡ _≃ᴱ_.from (H≃ᴱH b₂ b₁)
  H≃ᴱH-inverse {b₁ = b₁} {b₂ = b₂} =
    _≃ᴱ_.to (H≃ᴱH b₁ b₂)                                            ≡⟨ to-H≃ᴱH≡ ⟩
    subst H (T.truncation-is-proposition b₁ b₂)                     ≡⟨ cong (subst H) $
                                                                       mono₁ 1 T.truncation-is-proposition _ _ ⟩
    subst H (sym $ T.truncation-is-proposition b₂ b₁)               ≡⟨ (⟨ext⟩ λ _ → subst-in-terms-of-inverse∘≡⇒↝ equivalenceᴱ _ _ _) ⟩
    _≃ᴱ_.from (≡⇒↝ _ (cong H (T.truncation-is-proposition b₂ b₁)))  ≡⟨ cong _≃ᴱ_.from $ sym H≃ᴱH≡ ⟩∎
    _≃ᴱ_.from (H≃ᴱH b₂ b₁)                                          ∎

  @0 get⁻¹ᴱ-const-∘ :
    (b₁ b₂ b₃ : B) (p : get ⁻¹ᴱ b₁) →
    get⁻¹ᴱ-const b₂ b₃ (get⁻¹ᴱ-const b₁ b₂ p) ≡ get⁻¹ᴱ-const b₁ b₃ p
  get⁻¹ᴱ-const-∘ b₁ b₂ b₃ p =
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (_≃ᴱ_.to (H≃ᴱH _ _)
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₂)
            (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₂)
               (_≃ᴱ_.to (H≃ᴱH _ _)
                  (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))))                ≡⟨ cong (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) ∘ _≃ᴱ_.to (H≃ᴱH _ _)) $
                                                                   _≃ᴱ_.right-inverse-of (get⁻¹ᴱ-≃ᴱ _) _ ⟩
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (_≃ᴱ_.to (H≃ᴱH _ _)
         (_≃ᴱ_.to (H≃ᴱH _ _)
            (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))                        ≡⟨ cong (λ f → _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) (f (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ _) _)))
                                                                   H≃ᴱH-∘ ⟩∎
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (_≃ᴱ_.to (H≃ᴱH _ _)
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
    proj₁ (get⁻¹ᴱ-const b₁ b₂ (set a b₁ , [ get-set a b₁ ]))          ≡⟨⟩

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

-- An equality characterisation lemma.

@0 equality-characterisation₁ :
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
equality-characterisation₁
  {a = a} {b = b} {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} ⊠ =

  l₁ ≡ l₂                                                              ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ (Σ-assoc F.∘ ∃-cong λ _ → Σ-assoc) ⟩

  ((get l₁ , H l₁ , get⁻¹ᴱ-≃ᴱ l₁) , _) ≡
  ((get l₂ , H l₂ , get⁻¹ᴱ-≃ᴱ l₂) , _)                                 ↔⟨ inverse $ ignore-propositional-component $ mono₁ 0
                                                                          Contractible-last-part-of-Coherently-constant ⟩

  (get l₁ , H l₁ , get⁻¹ᴱ-≃ᴱ l₁) ≡ (get l₂ , H l₂ , get⁻¹ᴱ-≃ᴱ l₂)      ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Σ-assoc ⟩

  ((get l₁ , H l₁) , get⁻¹ᴱ-≃ᴱ l₁) ≡ ((get l₂ , H l₂) , get⁻¹ᴱ-≃ᴱ l₂)  ↔⟨ inverse B.Σ-≡,≡↔≡ ⟩

  (∃ λ (eq : (get l₁ , H l₁) ≡ (get l₂ , H l₂)) →
     subst (λ (g , H) → ∀ b → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣) eq (get⁻¹ᴱ-≃ᴱ l₁) ≡
     get⁻¹ᴱ-≃ᴱ l₂)                                                     ↝⟨ (Σ-cong-contra ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ ((g , h) : get l₁ ≡ get l₂ × H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁) ≡
     get⁻¹ᴱ-≃ᴱ l₂)                                                     ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     subst (λ (g , H) → ∀ b → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
       (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁) ≡
     get⁻¹ᴱ-≃ᴱ l₂)                                                     ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                           Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → ∀ b → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁) b ≡
           get⁻¹ᴱ-≃ᴱ l₂ b)                                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                           push-subst-application _ _) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b → subst (λ (g , H) → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
             (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁ b) ≡
           get⁻¹ᴱ-≃ᴱ l₂ b)                                             ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                           EEq.to≡to≃≡ ext) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     _≃ᴱ_.to (subst (λ (g , H) → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
               (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁ b)) p ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (_≡ _) $ lemma _ _ _ _) ⟩□
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                       □

  where

  open Lens

  lemma : ∀ _ _ _ _ → _ ≡ _
  lemma g h b p =
    _≃ᴱ_.to (subst (λ (g , H) → g ⁻¹ᴱ b ≃ᴱ H ∣ b ∣)
              (cong₂ _,_ g h) (get⁻¹ᴱ-≃ᴱ l₁ b)) p                ≡⟨ cong (_$ p) EEq.to-subst ⟩

    subst (λ (g , H) → g ⁻¹ᴱ b → H ∣ b ∣)
      (cong₂ _,_ g h) (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b)) p               ≡⟨ subst-→ ⟩

    subst (λ (g , H) → H ∣ b ∣) (cong₂ _,_ g h)
      (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b)
         (subst (λ (g , H) → g ⁻¹ᴱ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ subst-∘ _ _ _ ⟩

    subst (_$ ∣ b ∣) (cong proj₂ $ cong₂ _,_ g h)
      (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b)
         (subst (λ (g , H) → g ⁻¹ᴱ b) (sym $ cong₂ _,_ g h) p))  ≡⟨ cong₂ (λ p q → subst (λ (H : Pow a ∥ _ ∥ᴱ) → H ∣ b ∣)
                                                                                     p (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) q))
                                                                      (cong-proj₂-cong₂-, _ _)
                                                                      (subst-∘ _ _ _) ⟩
    subst (_$ ∣ b ∣) h
      (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b)
         (subst (_⁻¹ᴱ b) (cong proj₁ $ sym $ cong₂ _,_ g h) p))  ≡⟨ cong (λ eq → subst (_$ ∣ b ∣) h
                                                                                   (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) eq p))) $
                                                                    trans (cong-sym _ _) $
                                                                    cong sym $ cong-proj₁-cong₂-, _ _ ⟩∎
    subst (_$ ∣ b ∣) h
      (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p))      ∎

-- Another equality characterisation lemma.

@0 equality-characterisation₂ :
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst id (h ∣ b ∣)
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                               ↝⟨ equality-characterisation₁ ⊠ ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (h : H l₁ ≡ H l₂) →
     ∀ b p →
     subst (_$ ∣ b ∣) h
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym g) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                            Σ-cong-contra (Eq.extensionality-isomorphism bad-ext) λ _ →
                                                                            F.id) ⟩
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst (_$ ∣ b ∣) (⟨ext⟩ h)
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                            ≡⇒↝ _ $ cong (_≡ _) $
                                                                            subst-ext _ _) ⟩□
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≡ H l₂ b) →
     ∀ b p →
     subst id (h ∣ b ∣)
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)                                        □
  where
  open Lens

-- Yet another equality characterisation lemma.

@0 equality-characterisation₃ :
  {A : Type a} {B : Type b}
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  Univalence (a ⊔ b) →
  let open Lens in

  (l₁ ≡ l₂)
    ≃
  (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
   ∃ λ (h : ∀ b → H l₁ b ≃ H l₂ b) →
     ∀ b p →
     _≃_.to (h ∣ b ∣)
       (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₁ b) (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ g)) p)) ≡
     _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ l₂ b) p)
equality-characterisation₃ {l₁ = l₁} {l₂ = l₂} ⊠ univ =
  l₁ ≡ l₂                                                               ↝⟨ equality-characterisation₂ ⊠ ⟩

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

-- The lenses defined above can be converted to and from the lenses
-- defined in Higher.

Lens⇔Higher-lens :
  Block "conversion" →
  Lens A B ⇔ Higher.Lens A B
Lens⇔Higher-lens {A = A} {B = B} ⊠ = record
  { to = λ l → let open Lens l in record
      { R = Σ ∥ B ∥ᴱ H

      ; equiv =
          A                                                      ↝⟨ (inverse $ drop-⊤-right λ _ → _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤
                                                                     Contractibleᴱ-Erased-other-singleton) ⟩
          (∃ λ (a : A) → ∃ λ (b : B) → Erased (get a ≡ b))       ↔⟨ ∃-comm ⟩
          (∃ λ (b : B) → get ⁻¹ᴱ b)                              ↝⟨ ∃-cong get⁻¹ᴱ-≃ᴱ ⟩
          (∃ λ (b : B) → H ∣ b ∣)                                ↝⟨ EEq.↔→≃ᴱ
                                                                      (λ (b , h) → (∣ b ∣ , b) , h)
                                                                      (λ ((∥b∥ , b) , h) → b , _≃ᴱ_.to (H≃ᴱH ∥b∥ ∣ b ∣) h)
                                                                      (λ ((∥b∥ , b) , h) →
                                                                         Σ-≡,≡→≡ (cong (_, _) (T.truncation-is-proposition _ _)) (
              subst (H ∘ proj₁)
                (cong (_, _) (T.truncation-is-proposition _ _))
                (_≃ᴱ_.to (H≃ᴱH _ _) h)                                     ≡⟨ trans (subst-∘ _ _ _) $
                                                                              trans (cong (flip (subst H) _) $ cong-∘ _ _ _) $
                                                                              cong (flip (subst H) _) $ sym $ cong-id _ ⟩
              subst H (T.truncation-is-proposition _ _)
                (_≃ᴱ_.to (H≃ᴱH _ _) h)                                     ≡⟨ cong (_$ _) $ sym to-H≃ᴱH≡ ⟩

              _≃ᴱ_.to (H≃ᴱH _ _) (_≃ᴱ_.to (H≃ᴱH _ _) h)                    ≡⟨ cong (_$ h) H≃ᴱH-∘ ⟩

              _≃ᴱ_.to (H≃ᴱH _ _) h                                         ≡⟨ cong (_$ h) H≃ᴱH-id ⟩∎

              h                                                            ∎))
                                                                      (λ (b , h) → cong (_ ,_) (
              _≃ᴱ_.to (H≃ᴱH _ _) h                                       ≡⟨ cong (_$ h) H≃ᴱH-id ⟩∎
              h                                                          ∎)) ⟩

          (∃ λ ((b , _) : ∥ B ∥ᴱ × B) → H b)                     ↔⟨ Σ-assoc F.∘
                                                                    (∃-cong λ _ → ×-comm) F.∘
                                                                    inverse Σ-assoc ⟩□
          Σ ∥ B ∥ᴱ H × B                                         □

      ; inhabited = _≃_.to T.∥∥ᴱ≃∥∥ ∘ proj₁
      }
  ; from = λ l →
        Higher.Lens.get l
      , (λ _ → Higher.Lens.R l)
      , (λ b → inverse (Higher.remainder≃ᴱget⁻¹ᴱ l b))
      , (λ _ _ → F.id)
      , [ (λ x y → EEq.to≡to→≡ ext (⟨ext⟩ λ r →
             r                                                     ≡⟨ cong (λ f → _≃ᴱ_.to f r) $ sym ≡⇒↝-refl ⟩
             _≃ᴱ_.to (≡⇒↝ _ (refl _)) r                            ≡⟨ cong (λ eq → _≃ᴱ_.to (≡⇒↝ _ eq) r) $ sym $ cong-const _ ⟩∎
             _≃ᴱ_.to (≡⇒↝ _ (cong (const (Higher.Lens.R l)) _)) r  ∎))
        ]
  }

-- The conversion preserves getters and setters.

Lens⇔Higher-lens-preserves-getters-and-setters :
  (bl : Block "conversion") →
  Preserves-getters-and-setters-⇔ A B (Lens⇔Higher-lens bl)
Lens⇔Higher-lens-preserves-getters-and-setters ⊠ =
    (λ l →
       let open Lens l in
         refl _
       , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
         proj₁ (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b)
                  (_≃ᴱ_.to (H≃ᴱH ∣ get a ∣ ∣ b ∣)
                     (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ (get a))
                        (a , [ refl (get a) ]))))  ∎)
  , (λ _ → refl _ , refl _)

-- Lens A B is equivalent to Higher.Lens A B (with erased proofs,
-- assuming univalence).

Lens≃ᴱHigher-lens :
  {A : Type a} {B : Type b} →
  Block "conversion" →
  @0 Univalence (a ⊔ b) →
  Lens A B ≃ᴱ Higher.Lens A B
Lens≃ᴱHigher-lens {A = A} {B = B} bl univ =
  EEq.↔→≃ᴱ
    (_⇔_.to (Lens⇔Higher-lens bl))
    (_⇔_.from (Lens⇔Higher-lens bl))
    (to∘from bl)
    (from∘to bl)
  where
  @0 to∘from :
    (bl : Block "conversion") →
    ∀ l →
    _⇔_.to (Lens⇔Higher-lens bl) (_⇔_.from (Lens⇔Higher-lens bl) l) ≡ l
  to∘from ⊠ l = _↔_.from (Higher.equality-characterisation₁ univ)
    ( (∥ B ∥ᴱ × R  ↔⟨ (drop-⊤-left-× λ r → _⇔_.to contractible⇔↔⊤ $
                       propositional⇒inhabited⇒contractible
                         T.truncation-is-proposition
                         (_≃_.from T.∥∥ᴱ≃∥∥ (inhabited r))) ⟩□
       R          □)
    , (λ _ → refl _)
    )
    where
    open Higher.Lens l

  @0 from∘to :
    (bl : Block "conversion") →
    ∀ l →
    _⇔_.from (Lens⇔Higher-lens bl) (_⇔_.to (Lens⇔Higher-lens bl) l) ≡ l
  from∘to bl@⊠ l = _≃_.from (equality-characterisation₃ ⊠ univ)
    ( (λ _ → refl _)
    , Σ∥B∥ᴱH≃H
    , (λ b p@(a , [ get-a≡b ]) →
         _≃_.to (Σ∥B∥ᴱH≃H ∣ b ∣)
           (_≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                         (_⇔_.to (Lens⇔Higher-lens bl) l) b)
              (subst (_⁻¹ᴱ b) (sym (⟨ext⟩ λ _ → refl _)) p))       ≡⟨ cong (_≃_.to (Σ∥B∥ᴱH≃H ∣ b ∣) ∘
                                                                            _≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                                                                                         (_⇔_.to (Lens⇔Higher-lens bl) l) b)) $
                                                                      trans (cong (flip (subst (_⁻¹ᴱ b)) p) $
                                                                             trans (cong sym ext-refl) $
                                                                             sym-refl) $
                                                                      subst-refl _ _ ⟩
         _≃_.to (Σ∥B∥ᴱH≃H ∣ b ∣)
           (_≃ᴱ_.from (Higher.remainder≃ᴱget⁻¹ᴱ
                         (_⇔_.to (Lens⇔Higher-lens bl) l) b)
              p)                                                   ≡⟨⟩

         _≃_.to (Σ∥B∥ᴱH≃H ∣ b ∣)
           (Higher.Lens.remainder
              (_⇔_.to (Lens⇔Higher-lens bl) l) a)                  ≡⟨⟩

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
                                                                        _ ⟩∎
         _≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) p                                   ∎)
    )
    where
    open Lens l

    Σ∥B∥ᴱH≃H = λ b →
      Σ ∥ B ∥ᴱ H  ↔⟨ (drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                      propositional⇒inhabited⇒contractible
                        T.truncation-is-proposition b) ⟩□
      H b         □

-- The equivalence preserves getters and setters.

Lens≃ᴱHigher-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bl : Block "conversion")
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱHigher-lens bl univ))
Lens≃ᴱHigher-lens-preserves-getters-and-setters bl univ =
  Lens⇔Higher-lens-preserves-getters-and-setters bl

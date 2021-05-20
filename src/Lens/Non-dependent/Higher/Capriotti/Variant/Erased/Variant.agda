------------------------------------------------------------------------
-- A variant of the lens type in
-- Lens.Non-dependent.Higher.Capriotti.Variant.Erased
--
-- This variant uses ∥_∥ᴱ instead of ∥_∥.
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages.Cubical eq as ECP
  using (_⁻¹ᴱ_; Contractibleᴱ)
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
    P Q      : A → Type p
    b₁ b₂ b₃ : A
    f        : (x : A) → P x

------------------------------------------------------------------------
-- Coherently-constant

-- Coherently constant type-valued functions.

Coherently-constant :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant {p = p} {A = A} P =
  ∃ λ (Q : ∥ A ∥ᴱ → Type p) →
    (∀ x → P x ≃ᴱ Q ∣ x ∣) ×
    ∃ λ (Q→Q : ∀ x y → Q x → Q y) →
      Erased (∀ x y → Q→Q x y ≡
                      subst Q (T.truncation-is-proposition x y))

-- The "last part" of Coherently-constant is contractible (in erased
-- contexts).

@0 Contractible-last-part-of-Coherently-constant :
  Contractible
    (∃ λ (Q→Q : ∀ x y → Q x → Q y) →
     Erased (∀ x y → Q→Q x y ≡
                     subst Q (T.truncation-is-proposition x y)))
Contractible-last-part-of-Coherently-constant {Q = Q} =           $⟨ Contractibleᴱ-Erased-singleton ⟩
  Contractibleᴱ
    (∃ λ (Q→Q : ∀ x y → Q x → Q y) →
     Erased (Q→Q ≡ λ x y →
                   subst Q (T.truncation-is-proposition x y)))    ↝⟨ (ECP.Contractibleᴱ-cong _ $
                                                                      ∃-cong λ _ → Erased-cong (inverse $
                                                                      Eq.extensionality-isomorphism ext F.∘
                                                                      ∀-cong ext λ _ → Eq.extensionality-isomorphism ext)) ⦂ (_ → _) ⟩
  Contractibleᴱ
    (∃ λ (Q→Q : ∀ x y → Q x → Q y) →
     Erased (∀ x y → Q→Q x y ≡
                     subst Q (T.truncation-is-proposition x y)))  ↝⟨ ECP.Contractibleᴱ→Contractible ⟩□

  Contractible
    (∃ λ (Q→Q : ∀ x y → Q x → Q y) →
     Erased (∀ x y → Q→Q x y ≡
                     subst Q (T.truncation-is-proposition x y)))  □

-- In erased contexts Coherently-constant P is equivalent to
-- V.Coherently-constant P.

@0 Coherently-constant≃Variant-coherently-constant :
  {P : A → Type p} →
  Coherently-constant P ≃ V.Coherently-constant P
Coherently-constant≃Variant-coherently-constant {A = A} {P = P} =
  (∃ λ (Q : ∥ A ∥ᴱ → _) → (∀ x → P x ≃ᴱ Q ∣ x ∣) × _)  ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                           _⇔_.to contractible⇔↔⊤
                                                           Contractible-last-part-of-Coherently-constant) ⟩
  (∃ λ (Q : ∥ A ∥ᴱ → _) → ∀ x → P x ≃ᴱ Q ∣ x ∣)        ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse
                                                           EEq.≃≃≃ᴱ) ⟩
  (∃ λ (Q : ∥ A ∥ᴱ → _) → ∀ x → P x ≃  Q ∣ x ∣)        ↝⟨ (Σ-cong {k₁ = equivalence} (→-cong₁ ext T.∥∥ᴱ≃∥∥) λ _ → F.id) ⟩□
  (∃ λ (Q : ∥ A ∥  → _) → ∀ x → P x ≃  Q ∣ x ∣)        □

-- In erased contexts Coherently-constant (f ⁻¹ᴱ_) is equivalent to
-- V.Coherently-constant (f ⁻¹_).

@0 Coherently-constant-⁻¹ᴱ≃Variant-coherently-constant-⁻¹ :
  Coherently-constant (f ⁻¹ᴱ_) ≃ V.Coherently-constant (f ⁻¹_)
Coherently-constant-⁻¹ᴱ≃Variant-coherently-constant-⁻¹ {f = f} =
  Coherently-constant (f ⁻¹ᴱ_)        ↝⟨ Coherently-constant≃Variant-coherently-constant ⟩
  V.Coherently-constant (f ⁻¹ᴱ_)      ↔⟨⟩
  (∃ λ Q → ∀ x → f ⁻¹ᴱ x ≃  Q ∣ x ∣)  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ →
                                          Eq.≃-preserves ext (inverse ECP.⁻¹≃⁻¹ᴱ) F.id) ⟩
  (∃ λ Q → ∀ x → f ⁻¹ x ≃  Q ∣ x ∣)   ↔⟨⟩
  V.Coherently-constant (f ⁻¹_)       □

-- A variant of Coherently-constant.

Coherently-constant′ :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant′ {p = p} {A = A} P =
  ∃ λ (P→P : ∀ x y → P x → P y) →
  ∃ λ (Q : ∥ A ∥ᴱ → Type p) →
  ∃ λ (P≃Q : ∀ x → P x ≃ᴱ Q ∣ x ∣) →
  Erased (P→P ≡
          λ x y →
          _≃ᴱ_.from (P≃Q y) ∘
          subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
          _≃ᴱ_.to (P≃Q x))

-- Coherently-constant and Coherently-constant′ are pointwise
-- equivalent (with erased proofs).

Coherently-constant≃ᴱCoherently-constant′ :
  Coherently-constant P ≃ᴱ Coherently-constant′ P
Coherently-constant≃ᴱCoherently-constant′ {P = P} =
  (∃ λ Q →
   (∀ x → P x ≃ᴱ Q ∣ x ∣) ×
   ∃ λ (Q→Q : ∀ x y → Q x → Q y) →
   Erased (∀ x y → Q→Q x y ≡ subst Q (T.truncation-is-proposition x y)))  ↝⟨ lemma ⟩

  (∃ λ Q →
   ∃ λ (P≃Q : ∀ x → P x ≃ᴱ Q ∣ x ∣) →
   ∃ λ (P→P : ∀ x y → P x → P y) →
   Erased (P→P ≡
           λ x y →
           _≃ᴱ_.from (P≃Q y) ∘
           subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
           _≃ᴱ_.to (P≃Q x)))                                              ↔⟨ ∃-comm F.∘
                                                                             (∃-cong λ _ → ∃-comm) ⟩□
  (∃ λ (P→P : ∀ x y → P x → P y) →
   ∃ λ Q →
   ∃ λ (P≃Q : ∀ x → P x ≃ᴱ Q ∣ x ∣) →
   Erased (P→P ≡
           λ x y →
           _≃ᴱ_.from (P≃Q y) ∘
           subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
           _≃ᴱ_.to (P≃Q x)))                                              □
  where
  lemma =
    ∃-cong λ Q → ∃-cong λ P≃Q →

    (∃ λ (Q→Q : ∀ x y → Q x → Q y) →
     Erased (∀ x y →
             Q→Q x y ≡ subst Q (T.truncation-is-proposition x y)))        ↔⟨ (∀-cong ext λ _ → ∃-cong λ _ → Erased-cong (from-equivalence $
                                                                              Eq.extensionality-isomorphism bad-ext)) F.∘
                                                                             inverse ΠΣ-comm F.∘
                                                                             (∃-cong λ _ → Erased-Π↔Π) ⟩
    (∀ x →
     ∃ λ (Q→Q : ∀ y → Q x → Q y) →
     Erased (Q→Q ≡ λ y → subst Q (T.truncation-is-proposition x y)))      ↔⟨ (∀-cong ext λ _ →
                                                                              T.Σ-Π-∥∥ᴱ-Erased-≡-≃) ⟩
    (∀ x →
     ∃ λ (Q→Q : ∀ y → Q x → Q ∣ y ∣) →
     Erased (Q→Q ≡ λ y → subst Q (T.truncation-is-proposition x ∣ y ∣)))  ↔⟨ (∃-cong λ _ →
                                                                              (Erased-cong (from-equivalence $
                                                                               Eq.extensionality-isomorphism bad-ext)) F.∘
                                                                              inverse Erased-Π↔Π) F.∘
                                                                             ΠΣ-comm ⟩
    (∃ λ (Q→Q : ∀ x y → Q x → Q ∣ y ∣) →
     Erased (Q→Q ≡
             λ x y → subst Q (T.truncation-is-proposition x ∣ y ∣)))      ↔⟨ T.Σ-Π-∥∥ᴱ-Erased-≡-≃ ⟩

    (∃ λ (Q→Q : ∀ x y → Q ∣ x ∣ → Q ∣ y ∣) →
     Erased (Q→Q ≡
             λ x y → subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)))  ↔⟨ (inverse $
                                                                              ΠΣ-comm F.∘
                                                                              (∀-cong ext λ _ → ΠΣ-comm)) F.∘
                                                                             (∃-cong λ _ →
                                                                              ((∀-cong ext λ _ → Erased-Π↔Π) F.∘
                                                                               Erased-Π↔Π) F.∘
                                                                              Erased-cong (from-equivalence $ inverse $
                                                                              Eq.extensionality-isomorphism bad-ext F.∘
                                                                              (∀-cong ext λ _ → Eq.extensionality-isomorphism bad-ext))) ⟩
    (∀ x y →
     ∃ λ (Q→Q : Q ∣ x ∣ → Q ∣ y ∣) →
     Erased (Q→Q ≡ subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)))    ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              let lemma = inverse $ →-cong ext (P≃Q _) (P≃Q _) in
                                                                              EEq.Σ-cong-≃ᴱ-Erased lemma λ _ →
                                                                              Erased-cong (from-equivalence $ inverse $
                                                                              Eq.≃-≡ $ EEq.≃ᴱ→≃ lemma)) ⟩
    (∀ x y →
     ∃ λ (P→P : P x → P y) →
     Erased (P→P ≡
             _≃ᴱ_.from (P≃Q y) ∘
             subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
             _≃ᴱ_.to (P≃Q x)))                                            ↔⟨ (∃-cong λ _ → Erased-cong (from-equivalence $
                                                                              Eq.extensionality-isomorphism bad-ext F.∘
                                                                              (∀-cong ext λ _ → Eq.extensionality-isomorphism bad-ext))) F.∘
                                                                             (∃-cong λ _ →
                                                                              inverse $
                                                                              (∀-cong ext λ _ → Erased-Π↔Π) F.∘
                                                                              Erased-Π↔Π) F.∘
                                                                             ΠΣ-comm F.∘
                                                                             (∀-cong ext λ _ → ΠΣ-comm) ⟩□
    (∃ λ (P→P : ∀ x y → P x → P y) →
     Erased (P→P ≡
             λ x y →
             _≃ᴱ_.from (P≃Q y) ∘
             subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
             _≃ᴱ_.to (P≃Q x)))                                            □

------------------------------------------------------------------------
-- The lens type family

-- Higher lenses with erased "proofs".

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹ᴱ_)

-- In erased contexts Lens A B is equivalent to V.Lens A B.

@0 Lens≃Variant-lens : Lens A B ≃ V.Lens A B
Lens≃Variant-lens {B = B} =
  (∃ λ get → Coherently-constant (get ⁻¹ᴱ_))   ↝⟨ (∃-cong λ _ → Coherently-constant-⁻¹ᴱ≃Variant-coherently-constant-⁻¹) ⟩□
  (∃ λ get → V.Coherently-constant (get ⁻¹_))  □

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

  -- The predicate H is, in a certain sense, constant.

  H→H : ∀ b₁ b₂ → H b₁ → H b₂
  H→H = proj₁ (proj₂ (proj₂ (proj₂ l)))

  -- In erased contexts H→H can be expressed using
  -- T.truncation-is-proposition.

  @0 H→H≡ : H→H b₁ b₂ ≡ subst H (T.truncation-is-proposition b₁ b₂)
  H→H≡ = erased (proj₂ (proj₂ (proj₂ (proj₂ l)))) _ _

  -- In erased contexts H→H b₁ b₂ is an equivalence.

  @0 H→H-equivalence : ∀ b₁ b₂ → Is-equivalence (H→H b₁ b₂)
  H→H-equivalence b₁ b₂ =                                         $⟨ _≃_.is-equivalence $ Eq.subst-as-equivalence _ _ ⟩
    Is-equivalence (subst H (T.truncation-is-proposition b₁ b₂))  ↝⟨ subst Is-equivalence $ sym H→H≡ ⟩□
    Is-equivalence (H→H b₁ b₂)                                    □

  -- One can convert from any "preimage" (with erased proofs) of the
  -- getter to any other.

  get⁻¹ᴱ-const : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂
  get⁻¹ᴱ-const b₁ b₂ =
    get ⁻¹ᴱ b₁  ↝⟨ _≃ᴱ_.to $ get⁻¹ᴱ-≃ᴱ b₁ ⟩
    H ∣ b₁ ∣    ↝⟨ H→H ∣ b₁ ∣ ∣ b₂ ∣ ⟩
    H ∣ b₂ ∣    ↝⟨ _≃ᴱ_.from $ get⁻¹ᴱ-≃ᴱ b₂ ⟩□
    get ⁻¹ᴱ b₂  □

  -- The function get⁻¹ᴱ-const b₁ b₂ is an equivalence (in erased
  -- contexts).

  @0 get⁻¹ᴱ-const-equivalence :
    (b₁ b₂ : B) → Is-equivalence (get⁻¹ᴱ-const b₁ b₂)
  get⁻¹ᴱ-const-equivalence b₁ b₂ = _≃_.is-equivalence (
    get ⁻¹ᴱ b₁  ↝⟨ EEq.≃ᴱ→≃ $ get⁻¹ᴱ-≃ᴱ b₁ ⟩
    H ∣ b₁ ∣    ↝⟨ Eq.⟨ _ , H→H-equivalence ∣ b₁ ∣ ∣ b₂ ∣ ⟩ ⟩
    H ∣ b₂ ∣    ↝⟨ EEq.≃ᴱ→≃ $ inverse $ get⁻¹ᴱ-≃ᴱ b₂ ⟩□
    get ⁻¹ᴱ b₂  □)

  -- Some coherence properties.

  @0 H→H-∘ : H→H b₂ b₃ ∘ H→H b₁ b₂ ≡ H→H b₁ b₃
  H→H-∘ {b₂ = b₂} {b₃ = b₃} {b₁ = b₁} =
    H→H b₂ b₃ ∘ H→H b₁ b₂                               ≡⟨ cong₂ (λ f g → f ∘ g) H→H≡ H→H≡ ⟩

    subst H (T.truncation-is-proposition b₂ b₃) ∘
    subst H (T.truncation-is-proposition b₁ b₂)         ≡⟨ (⟨ext⟩ λ _ → subst-subst _ _ _ _) ⟩

    subst H (trans (T.truncation-is-proposition b₁ b₂)
               (T.truncation-is-proposition b₂ b₃))     ≡⟨ cong (subst H) $
                                                           mono₁ 1 T.truncation-is-proposition _ _ ⟩

    subst H (T.truncation-is-proposition b₁ b₃)         ≡⟨ sym H→H≡ ⟩∎

    H→H b₁ b₃                                           ∎

  @0 H→H-id : ∀ {b} → H→H b b ≡ id
  H→H-id {b = b} =
    H→H b b                                    ≡⟨ H→H≡ ⟩
    subst H (T.truncation-is-proposition b b)  ≡⟨ cong (subst H) $
                                                  mono₁ 1 T.truncation-is-proposition _ _ ⟩
    subst H (refl b)                           ≡⟨ (⟨ext⟩ λ _ → subst-refl _ _) ⟩∎
    id                                         ∎

  @0 H→H-inverse : H→H b₁ b₂ ∘ H→H b₂ b₁ ≡ id
  H→H-inverse {b₁ = b₁} {b₂ = b₂} =
    H→H b₁ b₂ ∘ H→H b₂ b₁  ≡⟨ H→H-∘ ⟩
    H→H b₂ b₂              ≡⟨ H→H-id ⟩∎
    id                     ∎

  @0 get⁻¹ᴱ-const-∘ :
    get⁻¹ᴱ-const b₂ b₃ ∘ get⁻¹ᴱ-const b₁ b₂ ≡ get⁻¹ᴱ-const b₁ b₃
  get⁻¹ᴱ-const-∘ {b₂ = b₂} {b₃ = b₃} {b₁ = b₁} = ⟨ext⟩ λ p →
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (H→H _ _
         (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₂)
            (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₂)
               (H→H _ _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))))             ≡⟨ cong (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) ∘ H→H _ _) $
                                                                      _≃ᴱ_.right-inverse-of (get⁻¹ᴱ-≃ᴱ _) _ ⟩
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃)
      (H→H _ _ (H→H _ _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p)))               ≡⟨ cong (λ f → _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ _) (f (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ _) _)))
                                                                      H→H-∘ ⟩∎
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b₃) (H→H _ _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b₁) p))  ∎

  @0 get⁻¹ᴱ-const-id : ∀ {b} → get⁻¹ᴱ-const b b ≡ id
  get⁻¹ᴱ-const-id {b = b} = ⟨ext⟩ λ p →
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b) (H→H _ _ (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) p))  ≡⟨ cong (_≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b)) $ cong (_$ _) H→H-id  ⟩
    _≃ᴱ_.from (get⁻¹ᴱ-≃ᴱ b) (_≃ᴱ_.to (get⁻¹ᴱ-≃ᴱ b) p)            ≡⟨ _≃ᴱ_.left-inverse-of (get⁻¹ᴱ-≃ᴱ b) _ ⟩∎
    p                                                            ∎

  @0 get⁻¹ᴱ-const-inverse :
    get⁻¹ᴱ-const b₁ b₂ ∘ get⁻¹ᴱ-const b₂ b₁ ≡ id
  get⁻¹ᴱ-const-inverse {b₁ = b₁} {b₂ = b₂} =
    get⁻¹ᴱ-const b₁ b₂ ∘ get⁻¹ᴱ-const b₂ b₁  ≡⟨ get⁻¹ᴱ-const-∘ ⟩
    get⁻¹ᴱ-const b₂ b₂                       ≡⟨ get⁻¹ᴱ-const-id ⟩∎
    id                                       ∎

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
    proj₁ (get⁻¹ᴱ-const (get a) (get a) (a , [ refl _ ]))  ≡⟨ cong proj₁ $ cong (_$ a , [ refl _ ]) get⁻¹ᴱ-const-id ⟩∎
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
             (get⁻¹ᴱ-const (get a) b₁ (a , [ refl _ ])))              ≡⟨ cong proj₁ $ cong (_$ a , [ refl _ ]) get⁻¹ᴱ-const-∘ ⟩∎

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
                                                                      (λ ((∥b∥ , b) , h) → b , H→H ∥b∥ ∣ b ∣ h)
                                                                      (λ ((∥b∥ , b) , h) →
                                                                         Σ-≡,≡→≡ (cong (_, _) (T.truncation-is-proposition _ _)) (
              subst (H ∘ proj₁)
                (cong (_, _) (T.truncation-is-proposition _ _))
                (H→H _ _ h)                                                ≡⟨ trans (subst-∘ _ _ _) $
                                                                              trans (cong (flip (subst H) _) $ cong-∘ _ _ _) $
                                                                              cong (flip (subst H) _) $ sym $ cong-id _ ⟩
              subst H (T.truncation-is-proposition _ _)
                (H→H _ _ h)                                                ≡⟨ cong (_$ _) $ sym H→H≡ ⟩

              H→H _ _ (H→H _ _ h)                                          ≡⟨ cong (_$ h) H→H-∘ ⟩

              H→H _ _ h                                                    ≡⟨ cong (_$ h) H→H-id ⟩∎

              h                                                            ∎))
                                                                      (λ (b , h) → cong (_ ,_) (
              H→H _ _ h                                                  ≡⟨ cong (_$ h) H→H-id ⟩∎
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
      , (λ _ _ → id)
      , [ (λ _ _ → ⟨ext⟩ λ r →
             r                                    ≡⟨ sym $ subst-const _ ⟩∎
             subst (const (Higher.Lens.R l)) _ r  ∎)
        ]
  }

-- The conversion preserves getters and setters.

Lens⇔Higher-lens-preserves-getters-and-setters :
  (bl : Block "conversion") →
  Preserves-getters-and-setters-⇔ A B (Lens⇔Higher-lens bl)
Lens⇔Higher-lens-preserves-getters-and-setters ⊠ =
    (λ _ → refl _ , refl _)
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

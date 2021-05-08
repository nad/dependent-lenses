------------------------------------------------------------------------
-- Coinductive higher lenses with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

import Colimit.Sequential.Very-erased eq as CS
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages.Cubical eq
  using (_⁻¹ᴱ_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Erased eq as T
  using (∥_∥ᴱ; ∣_∣)
import H-level.Truncation.Propositional.Non-recursive.Erased eq as N
open import H-level.Truncation.Propositional.One-step eq as O
  using (∣_∣; ∥_∥¹-out-^; ∥_∥¹-in-^; ∣_,_∣-in-^)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq
import Lens.Non-dependent.Higher.Erased eq as Higher
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant eq
  as V
open import Lens.Non-dependent.Higher.Coherently.Coinductive eq
import Lens.Non-dependent.Higher.Coinductive eq as C
import Lens.Non-dependent.Higher.Coinductive.Small eq as S

private
  variable
    a b p : Level
    A B   : Type a
    n     : ℕ

------------------------------------------------------------------------
-- The lemma ∥∥ᴱ→≃

private

  -- A lemma used in the implementation of ∥∥ᴱ→≃.
  --
  -- This definition is erased because its implementation makes use of
  -- code related to O.∥_∥¹ (a HIT with a non-erased higher
  -- constructor).

  @0 ∥∥ᴱ→≃-lemma :
    Block "∥∥ᴱ→≃-lemma" →
    (f₀ : A → B) →
    (∃ λ (f₊ : ∀ n → ∥ A ∥¹-out-^ (1 + n) → B) →
       (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
       (∀ n x → f₊ (suc n) ∣ x ∣ ≡ f₊ n x)) ≃
    (∃ λ (f₊ : ∀ n → ∥ A ∥¹-in-^ (1 + n) → B) →
       (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
       (∀ n x → f₊ (suc n) ∣ n , x ∣-in-^ ≡ f₊ n x))
  ∥∥ᴱ→≃-lemma ⊠ _ =
    inverse $
    Σ-cong {k₁ = equivalence}
      (∀-cong ext λ n →
       →-cong₁ ext (inverse $ O.∥∥¹-out-^≃∥∥¹-in-^ (suc n))) λ f →
    ∃-cong λ _ → ∀-cong ext λ n →
    Π-cong-contra ext (O.∥∥¹-out-^≃∥∥¹-in-^ (suc n)) λ x →
    ≡⇒≃ $ cong (λ y → f (suc n) y ≡
                      f n (_≃_.to (O.∥∥¹-out-^≃∥∥¹-in-^ (suc n)) x)) $
    sym $ O.∣∣≡∣,∣-in-^ (1 + n)

-- Functions from ∥ A ∥ᴱ can be expressed as coherently constant
-- functions from A with erased "proofs" (assuming univalence).

∥∥ᴱ→≃ :
  Block "∥∥ᴱ→≃" →
  {A : Type a} {B : Type b} →
  @0 Univalence (a ⊔ b) →
  (∥ A ∥ᴱ → B)
    ≃
  (∃ λ (f : A → B) → Erased (C.Coherently-constant f))
∥∥ᴱ→≃ bl {A = A} {B = B} univ =
  (∥ A ∥ᴱ → B)                                                 ↝⟨ →-cong ext T.∥∥ᴱ≃∥∥ᴱ F.id ⟩

  (N.∥ A ∥ᴱ → B)                                               ↝⟨ CS.universal-property ⟩

  (∃ λ (f₀ : A → B) →
     Erased (∃ λ (f₊ : ∀ n → ∥ A ∥¹-out-^ (1 + n) → B) →
               (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
               (∀ n x → f₊ (suc n) ∣ x ∣ ≡ f₊ n x)))           ↝⟨ ∃-cong (λ f → Erased-cong (∥∥ᴱ→≃-lemma bl f)) ⟩

  (∃ λ (f₀ : A → B) →
     Erased (∃ λ (f₊ : ∀ n → ∥ A ∥¹-in-^ (1 + n) → B) →
               (∀ x → f₊ zero ∣ x ∣ ≡ f₀ x) ×
               (∀ n x → f₊ (suc n) ∣ n , x ∣-in-^ ≡ f₊ n x)))  ↝⟨ ∃-cong (λ f → Erased-cong (inverse $
                                                                  C.Coherently-constant′≃ bl)) ⟩

  (∃ λ (f : A → B) → Erased (C.Coherently-constant′ f))        ↝⟨ ∃-cong (λ f → Erased-cong (inverse $
                                                                  C.Coherently-constant≃Coherently-constant′ bl univ)) ⟩□
  (∃ λ (f : A → B) → Erased (C.Coherently-constant f))         □

-- A "computation" rule for ∥∥ᴱ→≃.

@0 cong-from-∥∥ᴱ→≃-truncation-is-proposition :
  (bl : Block "∥∥ᴱ→≃")
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b)) →
  {f : A → B} {c : C.Coherently-constant f}
  {x y : A} {p : ∣ x ∣ ≡ ∣ y ∣} →
  cong (_≃_.from (∥∥ᴱ→≃ bl univ) (f , [ c ])) p ≡
  c .property x y
cong-from-∥∥ᴱ→≃-truncation-is-proposition
  bl {A = A} univ {f = f} {c = c} {x = x} {y = y} {p = p} =
  cong (_≃_.from (∥∥ᴱ→≃ bl univ) (f , [ c ])) p                         ≡⟨⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]) ∘
        _≃_.to T.∥∥ᴱ≃∥∥ᴱ)
    p                                                                   ≡⟨ sym $ cong-∘ _ _ _ ⟩

  (cong (_≃_.from CS.universal-property (f , [ g bl ])) $
   cong (_≃_.to T.∥∥ᴱ≃∥∥ᴱ) p)                                           ≡⟨ cong (cong _) $ mono₁ 1 N.∥∥ᴱ-proposition _ _ ⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]))
    (N.∥∥ᴱ-proposition N.∣ x ∣ N.∣ y ∣)                                 ≡⟨⟩

  cong (_≃_.from CS.universal-property (f , [ g bl ]))
    (trans (sym (CS.∣∣₊≡∣∣₀ x))
       (trans (cong CS.∣_∣₊ (O.∣∣-constant x y))
          (CS.∣∣₊≡∣∣₀ y)))                                              ≡⟨ trans (cong-trans _ _ _) $
                                                                           cong₂ trans
                                                                             (cong-sym _ _)
                                                                             (trans (cong-trans _ _ _) $
                                                                              cong (flip trans _) $
                                                                              cong-∘ _ _ _) ⟩
  trans
    (sym $ cong (_≃_.from CS.universal-property (f , [ g bl ]))
             (CS.∣∣₊≡∣∣₀ x))
    (trans
       (cong (_≃_.from CS.universal-property (f , [ g bl ]) ∘ CS.∣_∣₊)
          (O.∣∣-constant x y))
       (cong (_≃_.from CS.universal-property (f , [ g bl ]))
          (CS.∣∣₊≡∣∣₀ y)))                                              ≡⟨ cong₂ trans
                                                                             (cong sym CS.rec-∣∣₊≡∣∣₀)
                                                                             (cong (trans _) CS.rec-∣∣₊≡∣∣₀) ⟩
  trans (sym $ proj₁ (proj₂ (g bl)) x)
    (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
       (proj₁ (proj₂ (g bl)) y))                                        ≡⟨ lemma bl ⟩∎

  c .property x y                                                       ∎
  where
  g : ∀ _ → _
  g bl =
    _≃_.from (∥∥ᴱ→≃-lemma bl _) $
    _≃_.to (C.Coherently-constant′≃ bl) $
    _≃_.to (C.Coherently-constant≃Coherently-constant′ bl univ) c

  lemma :
    ∀ bl →
    trans (sym $ proj₁ (proj₂ (g bl)) x)
      (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
         (proj₁ (proj₂ (g bl)) y)) ≡
    c .property x y
  lemma bl@⊠ =
    trans (sym $ proj₁ (proj₂ (g bl)) x)
      (trans (cong (proj₁ (g bl) 0) (O.∣∣-constant x y))
         (proj₁ (proj₂ (g bl)) y))                                ≡⟨⟩

    trans (sym $ refl _)
      (trans (cong (O.rec′ f (c .property)) (O.∣∣-constant x y))
         (refl _))                                                ≡⟨ trans (cong₂ trans sym-refl (trans-reflʳ _)) $
                                                                     trans-reflˡ _ ⟩

    cong (O.rec′ f (c .property)) (O.∣∣-constant x y)             ≡⟨ O.rec-∣∣-constant ⟩∎

    c .property x y                                               ∎

------------------------------------------------------------------------
-- Coherently-constant

-- Coherently constant type-valued functions.

Coherently-constant :
  {A : Type a} → (A → Type p) → Type (a ⊔ lsuc p)
Coherently-constant P =
  ∃ λ (f : ∀ x y → P x → P y) →
  Erased (∃ λ (c : C.Coherently-constant P) →
          ∀ x y → f x y ≡ subst id (c .property x y))

-- Coherently-constant is pointwise equivalent (with erased proofs) to
-- V.Coherently-constant (assuming univalence).

Coherently-constant≃ᴱCoherently-constant :
  {A : Type a} {P : A → Type p} →
  @0 Univalence (a ⊔ lsuc p) →
  @0 Univalence p →
  Coherently-constant P ≃ᴱ V.Coherently-constant P
Coherently-constant≃ᴱCoherently-constant
  {a = a} {p = p} {A = A} {P = P} univ′ univ =
  block λ bl →

  Coherently-constant P                                                 ↔⟨⟩

  (∃ λ (P-const : ∀ x y → P x → P y) →
   Erased (
   ∃ λ (c : C.Coherently-constant P) →
   ∀ x y →
   P-const x y ≡ subst id (c .property x y)))                           ↔⟨ (∃-cong λ P-const → Erased-cong (
                                                                            ∃-cong λ c → ∀-cong ext λ x → ∀-cong ext λ y →
                                                                            ≡⇒≃ $ cong (P-const x y ≡_) (
      subst id (c .property x y)                                            ≡⟨ cong (subst id) $ sym $
                                                                                 cong-from-∥∥ᴱ→≃-truncation-is-proposition bl univ′ ⟩
      subst id
        (cong (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
           (T.truncation-is-proposition ∣ x ∣ ∣ y ∣))                       ≡⟨ (⟨ext⟩ λ _ → sym $
                                                                                  subst-∘ _ _ _) ⟩∎
      subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
        (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)                           ∎))) ⟩

  (∃ λ (P-const : ∀ x y → P x → P y) →
   Erased (
   ∃ λ (c : C.Coherently-constant P) →
   ∀ x y →
   P-const x y ≡
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
     (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)))                        ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                            Eq.extensionality-isomorphism bad-ext F.∘
                                                                            (∀-cong ext λ _ → Eq.extensionality-isomorphism bad-ext))) ⟩
  (∃ λ (P-const : ∀ x y → P x → P y) →
   Erased (
   ∃ λ (c : C.Coherently-constant P) →
   P-const ≡
   λ x y →
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
     (T.truncation-is-proposition ∣ x ∣ ∣ y ∣)))                        ↔⟨ (∃-cong λ P-const → Erased-cong (
                                                                            ∃-cong λ c → ≡⇒≃ $ cong (P-const ≡_) $ sym $
                                                                            ⟨ext⟩ λ x → ⟨ext⟩ λ y →
                                                                            cong₂ (λ (f : P y → P y) (g : P x → P x) →
                                                                                     f ∘
                                                                                     subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
                                                                                       (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
                                                                                     g)
                                                                              (cong _≃_.to $
                                                                               trans (cong ≡⇒≃ $ cong-refl (_$ y)) $
                                                                               ≡⇒↝-refl)
                                                                              (cong _≃_.from $
                                                                               trans (cong ≡⇒≃ $ cong-refl (_$ x)) $
                                                                               ≡⇒↝-refl))) ⟩
  (∃ λ (P-const : ∀ x y → P x → P y) →
   Erased (
   ∃ λ (c : C.Coherently-constant P) →
   P-const ≡
   λ x y →
   ≡⇒→ (cong (_$ y) (refl P)) ∘
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (P , [ c ]))
     (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
   _≃_.from (≡⇒≃ (cong (_$ x) (refl P)))))                              ↝⟨ (∃-cong λ P-const → inverse $
                                                                            EEq.drop-⊤-left-Σ-≃ᴱ-Erased
                                                                              (EEq.other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤ ext univ)) ⟩
  (∃ λ (P-const : ∀ x y → P x → P y) →
   ∃ λ ((Q , P≃) : ∃ λ (Q : A → Type p) → ∀ x → P x ≃ᴱ Q x) →
   Erased (
   ∃ λ (c : C.Coherently-constant Q) →
   P-const ≡
   λ x y →
   _≃ᴱ_.from (P≃ y) ∘
   subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (Q , [ c ]))
     (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
   _≃ᴱ_.to (P≃ x)))                                                     ↔⟨ (∃-cong λ _ →
                                                                            Σ-assoc F.∘
                                                                            (∃-cong λ _ → ∃-comm) F.∘
                                                                            inverse Σ-assoc F.∘
                                                                            (∃-cong λ _ → Erased-Σ↔Σ)) ⟩
  (∃ λ (P-const : ∀ x y → P x → P y) →
   ∃ λ ((Q , c) : ∃ λ (Q : A → Type p) →
                  Erased (C.Coherently-constant Q)) →
   ∃ λ (P≃ : ∀ x → P x ≃ᴱ Q x) →
   Erased (P-const ≡
           λ x y →
           _≃ᴱ_.from (P≃ y) ∘
           subst (_≃_.from (∥∥ᴱ→≃ bl univ′) (Q , c))
             (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
           _≃ᴱ_.to (P≃ x)))                                             ↔⟨ (∃-cong λ _ →
                                                                            Σ-cong (inverse $ ∥∥ᴱ→≃ bl univ′) λ _ → Eq.id) ⟩
  (∃ λ (P-const : ∀ x y → P x → P y) →
   ∃ λ (Q : ∥ A ∥ᴱ → Type p) →
   ∃ λ (P≃ : ∀ x → P x ≃ᴱ Q ∣ x ∣) →
   Erased (P-const ≡
           λ x y →
           _≃ᴱ_.from (P≃ y) ∘
           subst Q (T.truncation-is-proposition ∣ x ∣ ∣ y ∣) ∘
           _≃ᴱ_.to (P≃ x)))                                             ↔⟨⟩

  V.Coherently-constant′ P                                              ↝⟨ inverse V.Coherently-constant≃ᴱCoherently-constant′ ⟩□

  V.Coherently-constant P                                               □

------------------------------------------------------------------------
-- The lens type family

-- Coinductive lenses.

Lens : Type a → Type b → Type (lsuc (a ⊔ b))
Lens A B = ∃ λ (get : A → B) → Coherently-constant (get ⁻¹ᴱ_)

-- Some derived definitions.

module Lens {A : Type a} {B : Type b} (l : Lens A B) where

  -- A getter.

  get : A → B
  get = proj₁ l

  -- One can convert from any "preimage" (with an erased proof) of the
  -- getter to any other.

  get⁻¹ᴱ-const : (b₁ b₂ : B) → get ⁻¹ᴱ b₁ → get ⁻¹ᴱ b₂
  get⁻¹ᴱ-const b₁ b₂ = proj₁ (proj₂ l) b₁ b₂

  -- A setter.

  set : A → B → A
  set a b =                      $⟨ get⁻¹ᴱ-const (get a) b ⟩
    (get ⁻¹ᴱ get a → get ⁻¹ᴱ b)  ↝⟨ _$ (a , [ refl _ ]) ⟩
    get ⁻¹ᴱ b                    ↝⟨ proj₁ ⟩□
    A                            □

instance

  -- The lenses defined above have getters and setters.

  has-getter-and-setter : Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

-- Lens A B is equivalent to V.Lens A B (with erased proofs, assuming
-- univalence).

Lens≃ᴱLens :
  Block "Lens≃ᴱLens" →
  {A : Type a} {B : Type b} →
  @0 Univalence (lsuc (a ⊔ b)) →
  @0 Univalence (a ⊔ b) →
  Lens A B ≃ᴱ V.Lens A B
Lens≃ᴱLens ⊠ {A = A} {B = B} univ′ univ =
  (∃ λ (get : A → B) → Coherently-constant (get ⁻¹ᴱ_))    ↝⟨ (∃-cong λ _ →
                                                              Coherently-constant≃ᴱCoherently-constant univ′ univ) ⟩□
  (∃ λ (get : A → B) → V.Coherently-constant (get ⁻¹ᴱ_))  □

-- The right-to-left direction of the equivalence preserves getters
-- and setters.

from-Lens≃ᴱLens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱLens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-→ A B
    (_≃ᴱ_.from (Lens≃ᴱLens bl univ′ univ))
from-Lens≃ᴱLens-preserves-getters-and-setters ⊠ _ _ l =
    refl _
  , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
    proj₁ (get⁻¹ᴱ-const (get a) b (a , [ refl (get a) ]))  ∎
  where
  open V.Lens l

-- In erased contexts the equivalence preserves getters and setters.
--
-- (I do not know if this result can be proved in non-erased
-- contexts.)

@0 Lens≃ᴱLens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱLens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱLens bl univ′ univ))
Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ =
  Preserves-getters-and-setters-⇔-inverse
    {f = _≃ᴱ_.logical-equivalence
           (inverse $ Lens≃ᴱLens bl univ′ univ)} $
  Preserves-getters-and-setters-→-↠-⇔
    (_≃_.surjection (EEq.≃ᴱ→≃ $ inverse $ Lens≃ᴱLens bl univ′ univ))
    (from-Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ)

-- Lens A B is equivalent to Higher.Lens A B (with erased proofs,
-- assuming univalence).

Lens≃ᴱHigher-lens :
  Block "Lens≃ᴱHigher-Lens" →
  {A : Type a} {B : Type b} →
  @0 Univalence (lsuc (a ⊔ b)) →
  @0 Univalence (a ⊔ b) →
  Lens A B ≃ᴱ Higher.Lens A B
Lens≃ᴱHigher-lens bl {A = A} {B = B} univ′ univ =
  Lens A B         ↝⟨ Lens≃ᴱLens bl univ′ univ ⟩
  V.Lens A B       ↝⟨ V.Lens≃ᴱHigher-lens bl univ ⟩□
  Higher.Lens A B  □

-- In erased contexts the equivalence preserves getters and setters.

@0 Lens≃ᴱHigher-lens-preserves-getters-and-setters :
  (bl : Block "Lens≃ᴱHigher-lens")
  {A : Type a} {B : Type b}
  (@0 univ′ : Univalence (lsuc (a ⊔ b)))
  (@0 univ : Univalence (a ⊔ b)) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱHigher-lens bl univ′ univ))
Lens≃ᴱHigher-lens-preserves-getters-and-setters bl univ′ univ =
  Preserves-getters-and-setters-⇔-∘
    {f = _≃ᴱ_.logical-equivalence $ V.Lens≃ᴱHigher-lens bl univ}
    {g = _≃ᴱ_.logical-equivalence $ Lens≃ᴱLens bl univ′ univ}
    (V.Lens≃ᴱHigher-lens-preserves-getters-and-setters bl univ)
    (Lens≃ᴱLens-preserves-getters-and-setters bl univ′ univ)

------------------------------------------------------------------------
-- H-levels

-- If P has h-level n (pointwise), then Coherently-constant P has
-- h-level n (assuming univalence).

H-level-Coherently-constant :
  {A : Type a} {P : A → Type p} →
  @0 Univalence (lsuc (a ⊔ p)) →
  @0 Univalence (a ⊔ lsuc p) →
  @0 Univalence p →
  ((a : A) → H-level n (P a)) →
  H-level n (Coherently-constant P)
H-level-Coherently-constant {n = n} univ₁ univ₂ univ₃ h =
  Σ-closure n
    (Π-closure ext n λ _ →
     Π-closure ext n λ _ →
     Π-closure ext n λ _ →
     h _) λ _ →
  H-level-Erased n (
  Σ-closure n
    (S.H-level-Coinductive-Coherently-constant
       univ₁ univ₂ univ₃ h) λ _ →
  Π-closure ext n λ _ →
  Π-closure ext n λ _ →
  H-level.⇒≡ n $
  Π-closure ext n λ _ →
  h _)

-- If A and B have h-level n given the assumption that the other type
-- is inhabited, then Lens A B has h-level n (assuming univalence).

lens-preserves-h-level :
  {A : Type a} {B : Type b} →
  @0 Univalence (lsuc (a ⊔ b)) →
  @0 Univalence (a ⊔ b) →
  ∀ n → (B → H-level n A) → (A → H-level n B) →
  H-level n (Lens A B)
lens-preserves-h-level univ₁ univ₂ n hA hB =
  Σ-closure n
    (Π-closure ext n λ a →
     hB a) λ _ →
  H-level-Coherently-constant univ₁ univ₁ univ₂ λ b →
  Σ-closure n (hA b) λ a →
  H-level-Erased n (
  H-level.⇒≡ n (hB a))

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n (in erased contexts, assuming
-- univalence).

@0 h-level-respects-lens-from-inhabited :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  Univalence (a ⊔ b) →
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited univ′ univ n =
  Higher.h-level-respects-lens-from-inhabited n ∘
  _≃ᴱ_.to (Lens≃ᴱHigher-lens ⊠ univ′ univ)

-- If A has positive h-level n, then Lens A B also has h-level n (in
-- erased contexts, assuming univalence).

@0 lens-preserves-h-level-of-domain :
  {A : Type a} {B : Type b} →
  Univalence (lsuc (a ⊔ b)) →
  Univalence (a ⊔ b) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain univ′ univ n hA =
  H-level.[inhabited⇒+]⇒+ n λ l →
  lens-preserves-h-level univ′ univ (1 + n) (λ _ → hA) λ a →
  h-level-respects-lens-from-inhabited univ′ univ _ l a hA

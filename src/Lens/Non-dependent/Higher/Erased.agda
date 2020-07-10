------------------------------------------------------------------------
-- Higher lenses with erased proofs
------------------------------------------------------------------------

-- At the time of writing there are counterparts in this file of more
-- or less everything in Lens.Non-dependent.Higher, except for parts
-- of the section called "A category". There is also a counterpart to
-- one of the properties related to higher lenses from
-- Lens.Non-dependent.Equivalent-preimages
-- (higher-lens-preserves-h-level-of-domain).

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Bi-invertibility.Erased
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Circle eq using (𝕊¹)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ; Contractibleᴱ; _⁻¹ᴱ_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)
import Lens.Non-dependent.Equivalent-preimages eq as EP
import Lens.Non-dependent.Higher eq as H
import Lens.Non-dependent.Traditional eq as T
import Lens.Non-dependent.Traditional.Erased eq as Traditionalᴱ

private
  variable
    a b c d p r     : Level
    A A₁ A₂ B B₁ B₂ : Set a
    P               : A → Set p
    n               : ℕ

------------------------------------------------------------------------
-- Higher lenses

private

 module Temporarily-private where

  -- Higher lenses with erased "proofs".

  record Lens (A : Set a) (B : Set b) : Set (lsuc (a ⊔ b)) where
    constructor ⟨_,_,_⟩
    pattern
    no-eta-equality
    field
      -- Remainder type.
      R : Set (a ⊔ b)

      -- Equivalence (with erased proofs).
      equiv : A ≃ᴱ (R × B)

      -- The proof of (mere) inhabitance.
      @0 inhabited : R → ∥ B ∥

open Temporarily-private public hiding (module Lens)

-- Lens can be expressed as a nested Σ-type.

Lens-as-Σ :
  {A : Set a} {B : Set b} →
  Lens A B ≃
  ∃ λ (R : Set (a ⊔ b)) →
    (A ≃ᴱ (R × B)) ×
    Erased (R → ∥ B ∥)
Lens-as-Σ = Eq.↔→≃
  (λ l → R l , equiv l , [ inhabited l ])
  (λ (R , equiv , [ inhabited ]) → record
     { R         = R
     ; equiv     = equiv
     ; inhabited = inhabited
     })
  refl
  (λ { ⟨ _ , _ , _ ⟩ → refl _ })
  where
  open Temporarily-private.Lens

-- Lenses without erased proofs can be turned into lenses with erased
-- proofs.

Higher-lens→Lens : H.Lens A B → Lens A B
Higher-lens→Lens {A = A} {B = B} l@(H.⟨ _ , _ , _ ⟩) =     $⟨ l ⟩
  H.Lens A B                                               ↔⟨ H.Lens-as-Σ ⟩
  (∃ λ (R : Set _) → (A ≃ (R × B)) × (R → ∥ B ∥))          ↝⟨ Σ-map P.id (Σ-map EEq.≃→≃ᴱ [_]→) ⟩
  (∃ λ (R : Set _) → (A ≃ᴱ (R × B)) × Erased (R → ∥ B ∥))  ↔⟨ inverse Lens-as-Σ ⟩□
  Lens A B                                                 □

-- In erased contexts Lens A B is equivalent to H.Lens A B.

@0 Lens≃Higher-lens : Lens A B ≃ H.Lens A B
Lens≃Higher-lens {A = A} {B = B} =
  Eq.with-other-inverse
    (Lens A B                                                 ↝⟨ Lens-as-Σ ⟩
     (∃ λ (R : Set _) → (A ≃ᴱ (R × B)) × Erased (R → ∥ B ∥))  ↝⟨ (∃-cong λ _ →
                                                                  inverse (EEq.≃≃≃ᴱ ext) ×-cong Eq.↔⇒≃ (erased Erased↔)) ⟩
     (∃ λ (R : Set _) → (A ≃ (R × B)) × (R → ∥ B ∥))          ↔⟨ inverse H.Lens-as-Σ ⟩□
     H.Lens A B                                               □)
    Higher-lens→Lens
    (λ { H.⟨ _ , _ , _ ⟩ → refl _ })

private

  -- The forward direction of Lens≃Higher-lens.

  @0 high : Lens A B → H.Lens A B
  high = _≃_.to Lens≃Higher-lens

-- Some derived definitions.

module Lens (l : Lens A B) where

  open Temporarily-private.Lens l public

  -- Remainder.

  remainder : A → R
  remainder a = proj₁ (_≃ᴱ_.to equiv a)

  -- Getter.

  get : A → B
  get a = proj₂ (_≃ᴱ_.to equiv a)

  -- Setter.

  set : A → B → A
  set a b = _≃ᴱ_.from equiv (remainder a , b)

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

  -- Lens laws.

  @0 get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    proj₂ (_≃ᴱ_.to equiv (_≃ᴱ_.from equiv (remainder a , b)))  ≡⟨ cong proj₂ (_≃ᴱ_.right-inverse-of equiv _) ⟩∎
    proj₂ (remainder a , b)                                    ∎

  @0 set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    _≃ᴱ_.from equiv (_≃ᴱ_.to equiv a)  ≡⟨ _≃ᴱ_.left-inverse-of equiv _ ⟩∎
    a                                  ∎

  @0 set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    let r = remainder a in

    _≃ᴱ_.from equiv (remainder (_≃ᴱ_.from equiv (r , b₁)) , b₂)  ≡⟨⟩

    _≃ᴱ_.from equiv
      (proj₁ (_≃ᴱ_.to equiv (_≃ᴱ_.from equiv (r , b₁))) , b₂)    ≡⟨ cong (λ p → _≃ᴱ_.from equiv (proj₁ p , b₂)) $
                                                                    _≃ᴱ_.right-inverse-of equiv _ ⟩∎
    _≃ᴱ_.from equiv (r , b₂)                                     ∎

  -- Another law.

  @0 remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set = H.Lens.remainder-set (high l)

  -- The remainder function is surjective (in erased contexts).

  @0 remainder-surjective : Surjective remainder
  remainder-surjective =
    H.Lens.remainder-surjective (high l)

  -- A traditional lens with erased proofs.

  traditional-lens : Traditionalᴱ.Lens A B
  traditional-lens = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }

  -- The following two coherence laws, which do not necessarily hold
  -- for traditional lenses with erased proofs (see
  -- Traditionalᴱ.getter-equivalence-but-not-coherent), hold
  -- unconditionally for higher lenses (in erased contexts).

  @0 get-set-get : ∀ a → cong get (set-get a) ≡ get-set a (get a)
  get-set-get a =
    cong (proj₂ ⊚ _≃ᴱ_.to equiv) (_≃ᴱ_.left-inverse-of equiv _)       ≡⟨ sym $ cong-∘ _ _ (_≃ᴱ_.left-inverse-of equiv _) ⟩
    cong proj₂ (cong (_≃ᴱ_.to equiv) (_≃ᴱ_.left-inverse-of equiv _))  ≡⟨ cong (cong proj₂) $ _≃ᴱ_.left-right-lemma equiv _ ⟩∎
    cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)                        ∎

  @0 get-set-set :
    ∀ a b₁ b₂ →
    cong get (set-set a b₁ b₂) ≡
    trans (get-set (set a b₁) b₂) (sym (get-set a b₂))
  get-set-set a b₁ b₂ = elim₁
    (λ eq →
       cong (proj₂ ⊚ _≃ᴱ_.to equiv)
         (cong (λ p → _≃ᴱ_.from equiv (proj₁ p , _)) eq) ≡
       trans (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _))
         (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _))))
    (cong (proj₂ ⊚ _≃ᴱ_.to equiv)
       (cong (λ p → _≃ᴱ_.from equiv (proj₁ p , b₂))
          (refl (proj₁ (_≃ᴱ_.to equiv a) , b₁)))           ≡⟨ cong (cong (proj₂ ⊚ _≃ᴱ_.to equiv)) $ cong-refl _ ⟩

     cong (proj₂ ⊚ _≃ᴱ_.to equiv) (refl _)                 ≡⟨ cong-refl _ ⟩

     refl _                                                ≡⟨ sym $ trans-symʳ _ ⟩∎

     trans (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _))
       (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))  ∎)
    (_≃ᴱ_.right-inverse-of equiv _)

  -- A somewhat coherent lens with erased proofs.

  coherent-lens : Traditionalᴱ.Coherent-lens A B
  coherent-lens = record
    { lens        = traditional-lens
    ; get-set-get = get-set-get
    ; get-set-set = get-set-set
    }

instance

  -- Higher lenses have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Equivalences with erased proofs can be converted to lenses

-- Converts equivalences between a domain and the cartesian product of
-- a type and a codomain to lenses.

≃ᴱ×→Lens :
  {A : Set a} {B : Set b} {R : Set (a ⊔ b)} →
  A ≃ᴱ (R × B) → Lens A B
≃ᴱ×→Lens {A = A} {B = B} {R = R} A≃R×B = record
  { R         = R × Erased ∥ B ∥
  ; equiv     = A                       ↝⟨ A≃R×B ⟩
                R × B                   ↔⟨ F.id ×-cong inverse Erased-∥∥×≃ ⟩
                R × Erased ∥ B ∥ × B    ↔⟨ ×-assoc ⟩□
                (R × Erased ∥ B ∥) × B  □
  ; inhabited = erased ⊚ proj₂
  }

-- Converts equivalences to lenses.

≃ᴱ→Lens :
  {A : Set a} {B : Set b} →
  A ≃ᴱ B → Lens A B
≃ᴱ→Lens {a = a} {A = A} {B = B} A≃B = record
  { R         = Erased ∥ ↑ a B ∥
  ; equiv     = A                     ↝⟨ A≃B ⟩
                B                     ↔⟨ inverse Erased-∥∥×≃ ⟩
                Erased ∥ B ∥ × B      ↔⟨ Erased-cong (∥∥-cong (inverse Bijection.↑↔)) ×-cong F.id ⟩□
                Erased ∥ ↑ a B ∥ × B  □
  ; inhabited = ∥∥-map lower ⊚ erased
  }

-- Converts equivalences between types with the same universe level to
-- lenses.

≃ᴱ→Lens′ :
  {A B : Set a} →
  A ≃ᴱ B → Lens A B
≃ᴱ→Lens′ {a = a} {A = A} {B = B} A≃B = record
  { R         = Erased ∥ B ∥
  ; equiv     = A                 ↝⟨ A≃B ⟩
                B                 ↔⟨ inverse Erased-∥∥×≃ ⟩□
                Erased ∥ B ∥ × B  □
  ; inhabited = erased
  }

------------------------------------------------------------------------
-- Equality characterisation lemmas for lenses

-- An equality characterisation lemma.

equality-characterisation₀ :
  {l₁ l₂ : Lens A B} →
  let open Lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ᴱ (R × B)) eq (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                              ↔⟨ inverse $ Eq.≃-≡ Lens-as-Σ ⟩

  l₁′ ≡ l₂′                                                            ↝⟨ inverse Bijection.Σ-≡,≡↔≡ ⟩

  (∃ λ (eq : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ᴱ (R × B) × Erased (R → ∥ B ∥)) eq (proj₂ l₁′) ≡
     proj₂ l₂′)                                                        ↝⟨ (∃-cong λ _ → inverse $
                                                                           ignore-propositional-component
                                                                             (H-level-Erased 1 (
                                                                              Π-closure ext 1 λ _ →
                                                                              truncation-is-proposition))) ⟩
  (∃ λ (eq : R l₁ ≡ R l₂) →
     proj₁ (subst (λ R → A ≃ᴱ (R × B) × Erased (R → ∥ B ∥))
              eq (proj₂ l₁′)) ≡
     equiv l₂)                                                         ↝⟨ (∃-cong λ eq → ≡⇒↝ _ $
                                                                           cong (λ p → proj₁ p ≡ _) (push-subst-, {y≡z = eq} _ _)) ⟩□
  (∃ λ (eq : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ᴱ (R × B)) eq (equiv l₁) ≡ equiv l₂)              □
  where
  open Lens

  l₁′ = _≃_.to Lens-as-Σ l₁
  l₂′ = _≃_.to Lens-as-Σ l₂

-- Another equality characterisation lemma.

@0 equality-characterisation₁ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
          _≃ᴱ_.to (equiv l₂) x
equality-characterisation₁ {l₁ = l₁} {l₂ = l₂} univ =
  l₁ ≡ l₂                                             ↔⟨ inverse $ Eq.≃-≡ Lens≃Higher-lens ⟩

  high l₁ ≡ high l₂                                   ↝⟨ H.equality-characterisation₁ ⊠ univ ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃ᴱ_.to (equiv l₂) x)                      □
  where
  open Lens

-- And another one.

@0 equality-characterisation₂ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} univ =
  l₁ ≡ l₂                                                 ↔⟨ inverse $ Eq.≃-≡ Lens≃Higher-lens ⟩

  high l₁ ≡ high l₂                                       ↝⟨ H.equality-characterisation₂ univ ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
       ×
     (∀ x → get l₁ x ≡ get l₂ x))                         □
  where
  open Lens

-- And a final one.

@0 equality-characterisation₃ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃ᴱ_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃ᴱ_.from (equiv l₂) p
equality-characterisation₃ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                                            ↔⟨ inverse $ Eq.≃-≡ Lens≃Higher-lens ⟩

  high l₁ ≡ high l₂                                                  ↝⟨ H.equality-characterisation₃ univ ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃ᴱ_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃ᴱ_.from (equiv l₂) p)                                   □
  where
  open Lens

------------------------------------------------------------------------
-- More lens equalities

-- If the forward direction of an equivalence with erased proofs is
-- Lens.get l, then the setter of l can be expressed using the other
-- direction of the equivalence (in erased contexts).

@0 from≡set :
  ∀ (l : Lens A B) is-equiv →
  let open Lens
      A≃B = EEq.⟨ get l , is-equiv ⟩
  in
  ∀ a b → _≃ᴱ_.from A≃B b ≡ set l a b
from≡set l is-equiv =
  H.from≡set (high l) (EEq.Is-equivalenceᴱ→Is-equivalence is-equiv)

-- If two lenses have equal setters, then they also have equal
-- getters (in erased contexts).

@0 getters-equal-if-setters-equal :
  let open Lens in
  (l₁ l₂ : Lens A B) →
  set l₁ ≡ set l₂ →
  get l₁ ≡ get l₂
getters-equal-if-setters-equal l₁ l₂ =
  Lens.set l₁ ≡ Lens.set l₂                    ↔⟨⟩
  H.Lens.set (high l₁) ≡ H.Lens.set (high l₂)  ↝⟨ H.getters-equal-if-setters-equal (high l₁) (high l₂) ⟩
  H.Lens.get (high l₁) ≡ H.Lens.get (high l₂)  ↔⟨⟩
  Lens.get l₁ ≡ Lens.get l₂                    □

-- A generalisation of lenses-equal-if-setters-equal (which is defined
-- below).

@0 lenses-equal-if-setters-equal′ :
  let open Lens in
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b))
  (l₁ l₂ : Lens A B)
  (f : R l₁ → R l₂) →
  (B → ∀ r →
   ∃ λ b′ → remainder l₂ (_≃ᴱ_.from (equiv l₁) (r , b′)) ≡ f r) →
  (∀ a → f (remainder l₁ a) ≡ remainder l₂ a) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal′
  univ l₁ l₂ f ∃≡f f-remainder≡remainder setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal′
                          univ (high l₁) (high l₂) f ∃≡f
                          f-remainder≡remainder setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- If the codomain of a lens is inhabited when it is merely inhabited
-- and the remainder type is inhabited, then this lens is equal to
-- another lens if their setters are equal (in erased contexts,
-- assuming univalence).

@0 lenses-equal-if-setters-equal :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  (Lens.R l₁ → ∥ B ∥ → B) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal univ l₁ l₂ inh′ setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal
                          univ (high l₁) (high l₂) inh′ setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- If a lens has a propositional remainder type, then this lens is
-- equal to another lens if their setters are equal (in erased
-- contexts, assuming univalence).

@0 lenses-equal-if-setters-equal-and-remainder-propositional :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  Is-proposition (Lens.R l₂) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal-and-remainder-propositional
  univ l₁ l₂ R₂-prop setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal-and-remainder-propositional
                          univ (high l₁) (high l₂) R₂-prop setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- The functions ≃ᴱ→Lens and ≃ᴱ→Lens′ are pointwise equal (when
-- applicable, in erased contexts, assuming univalence).

@0 ≃ᴱ→Lens≡≃ᴱ→Lens′ :
  {A B : Set a} →
  Univalence a →
  (A≃B : A ≃ᴱ B) → ≃ᴱ→Lens A≃B ≡ ≃ᴱ→Lens′ A≃B
≃ᴱ→Lens≡≃ᴱ→Lens′ {B = B} univ A≃B =
  _↔_.from (equality-characterisation₂ univ)
    ( (Erased ∥ ↑ _ B ∥  ↔⟨ Erased-cong (∥∥-cong Bijection.↑↔) ⟩□
       Erased ∥ B ∥      □)
    , (λ _ → refl _)
    , (λ _ → refl _)
    )

-- If the getter of a lens is an equivalence with erased proofs, then
-- the lens formed using the equivalence (using ≃ᴱ→Lens) is equal to
-- the lens (in erased contexts, assuming univalence).

@0 get-equivalence→≡≃ᴱ→Lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l : Lens A B) →
  (eq : Is-equivalenceᴱ (Lens.get l)) →
  l ≡ ≃ᴱ→Lens EEq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃ᴱ→Lens {A = A} {B = B} univ l eq =
  lenses-equal-if-setters-equal-and-remainder-propositional
    univ l (≃ᴱ→Lens EEq.⟨ Lens.get l , eq ⟩)
    (H-level-Erased 1 truncation-is-proposition)
    (⟨ext⟩ λ a → ⟨ext⟩ λ b →
     set l a b              ≡⟨ sym $ from≡set l eq a b ⟩
     _≃ᴱ_.from A≃B b        ≡⟨⟩
     set (≃ᴱ→Lens A≃B) a b  ∎)
  where
  open Lens

  A≃B : A ≃ᴱ B
  A≃B = EEq.⟨ _ , eq ⟩

-- A variant of get-equivalence→≡≃ᴱ→Lens.

@0 get-equivalence→≡≃ᴱ→Lens′ :
  {A B : Set a} →
  Univalence a →
  (l : Lens A B) →
  (eq : Is-equivalenceᴱ (Lens.get l)) →
  l ≡ ≃ᴱ→Lens′ EEq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃ᴱ→Lens′ {A = A} {B = B} univ l eq =
  l             ≡⟨ get-equivalence→≡≃ᴱ→Lens univ l eq ⟩
  ≃ᴱ→Lens A≃B   ≡⟨ ≃ᴱ→Lens≡≃ᴱ→Lens′ univ A≃B ⟩∎
  ≃ᴱ→Lens′ A≃B  ∎
  where
  A≃B = EEq.⟨ Lens.get l , eq ⟩

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Lens preserves equivalences with erased
-- proofs.

Lens-cong′ :
  A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ →
  (∃ λ (R : Set r) → A₁ ≃ᴱ (R × B₁) × Erased (R → ∥ B₁ ∥)) ≃ᴱ
  (∃ λ (R : Set r) → A₂ ≃ᴱ (R × B₂) × Erased (R → ∥ B₂ ∥))
Lens-cong′ A₁≃A₂ B₁≃B₂ =
  ∃-cong λ _ →
  EEq.≃ᴱ-cong ext A₁≃A₂ (F.id ×-cong B₁≃B₂)
    ×-cong
  Erased-cong (→-cong ext F.id (∥∥-cong B₁≃B₂))

-- Lens preserves level-preserving equivalences with erased proofs.

Lens-cong :
  {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
  A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ →
  Lens A₁ B₁ ≃ᴱ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁≃A₂ B₁≃B₂ =
  Lens A₁ B₁                                      ↔⟨ Lens-as-Σ ⟩
  (∃ λ R → A₁ ≃ᴱ (R × B₁) × Erased (R → ∥ B₁ ∥))  ↝⟨ Lens-cong′ A₁≃A₂ B₁≃B₂ ⟩
  (∃ λ R → A₂ ≃ᴱ (R × B₂) × Erased (R → ∥ B₂ ∥))  ↔⟨ inverse Lens-as-Σ ⟩□
  Lens A₂ B₂                                      □

-- If B is a proposition, then Lens A B is equivalent (with erased
-- proofs) to A → B (assuming univalence).

lens-to-proposition≃ᴱget :
  {A : Set a} {B : Set b} →
  @0 Univalence (a ⊔ b) →
  @0 Is-proposition B →
  Lens A B ≃ᴱ (A → B)
lens-to-proposition≃ᴱget {b = b} {A = A} {B = B} univ prop = EEq.↔→≃ᴱ
  get
  from
  refl
  (λ l →
     let lemma =
           ↑ b A    ↔⟨ Bijection.↑↔ ⟩
           A        ↝⟨ EEq.≃ᴱ→≃ (equiv l) ⟩
           R l × B  ↝⟨ (EEq.≃ᴱ→≃ $ drop-⊤-right λ r → _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
                        PT.rec
                          (EEq.Contractibleᴱ-propositional ext)
                          (λ b → EEq.inhabited→Is-proposition→Contractibleᴱ b prop)
                          (inhabited l r)) ⟩□
           R l      □
     in
     _↔_.from (equality-characterisation₁ univ)
        (lemma , λ _ → refl _))
  where
  open Lens

  from = λ get → record
    { R         = ↑ b A
    ; equiv     = A          ↔⟨ inverse Bijection.↑↔ ⟩
                  ↑ b A      ↝⟨ (inverse $ drop-⊤-right λ (lift a) →
                                 EEq.inhabited→Is-proposition→≃ᴱ⊤ (get a) prop) ⟩□
                  ↑ b A × B  □
    ; inhabited = ∣_∣ ⊚ get ⊚ lower
    }

_ :
  {A : Set a} {B : Set b}
  (@0 univ : Univalence (a ⊔ b))
  (@0 prop : Is-proposition B)
  (l : Lens A B) →
  _≃ᴱ_.to (lens-to-proposition≃ᴱget univ prop) l ≡ Lens.get l
_ = λ _ _ _ → refl _

-- If B is contractible (with an erased proof), then Lens A B is
-- equivalent (with erased proofs) to ⊤ (assuming univalence).

lens-to-contractible≃ᴱ⊤ :
  {A : Set a} {B : Set b} →
  @0 Univalence (a ⊔ b) →
  Contractibleᴱ B →
  Lens A B ≃ᴱ ⊤
lens-to-contractible≃ᴱ⊤ {A = A} {B} univ cB =
  Lens A B  ↝⟨ lens-to-proposition≃ᴱget univ (mono₁ 0 (EEq.Contractibleᴱ→Contractible cB)) ⟩
  (A → B)   ↝⟨ →-cong ext F.id $ _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ cB ⟩
  (A → ⊤)   ↔⟨ →-right-zero ⟩□
  ⊤         □

-- Lens A ⊥ is equivalent (with erased proofs) to ¬ A (assuming
-- univalence).

lens-to-⊥≃ᴱ¬ :
  {A : Set a} →
  @0 Univalence (a ⊔ b) →
  Lens A (⊥ {ℓ = b}) ≃ᴱ (¬ A)
lens-to-⊥≃ᴱ¬ {A = A} univ =
  Lens A ⊥  ↝⟨ lens-to-proposition≃ᴱget univ ⊥-propositional ⟩
  (A → ⊥)   ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A       □

-- If A is contractible (with an erased proof), then Lens A B is
-- equivalent (with erased proofs) to Contractibleᴱ B (assuming
-- univalence).

lens-from-contractible≃ᴱcodomain-contractible :
  {A : Set a} {B : Set b} →
  @0 Univalence (a ⊔ b) →
  Contractibleᴱ A →
  Lens A B ≃ᴱ Contractibleᴱ B
lens-from-contractible≃ᴱcodomain-contractible {A = A} {B} univ cA =
  Lens A B                                                            ↔⟨ Lens-as-Σ ⟩
  (∃ λ R → A ≃ᴱ (R × B) × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ →
                                                                          EEq.≃ᴱ-cong ext (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ cA) F.id) ⟩
  (∃ λ R → ⊤ ≃ᴱ (R × B) × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → EEq.inverse-equivalence ext) ⟩
  (∃ λ R → (R × B) ≃ᴱ ⊤ × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → inverse $ EEq.Contractibleᴱ≃ᴱ≃ᴱ⊤ ext) ⟩
  (∃ λ R → Contractibleᴱ (R × B) × Erased (R → ∥ B ∥))                ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → EEq.Contractibleᴱ-commutes-with-× ext) ⟩
  (∃ λ R → (Contractibleᴱ R × Contractibleᴱ B) × Erased (R → ∥ B ∥))  ↔⟨ (∃-cong λ _ → inverse ×-assoc) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased (R → ∥ B ∥))    ↝⟨ (∃-cong λ _ → ∃-cong λ cR → ∃-cong λ _ → Erased-cong (
                                                                          →-cong ext (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ cR) F.id)) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased (⊤ → ∥ B ∥))    ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → Erased-cong Π-left-identity) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased ∥ B ∥)          ↔⟨ (∃-cong λ _ → ×-comm) ⟩
  (∃ λ R → (Contractibleᴱ B × Erased ∥ B ∥) × Contractibleᴱ R)        ↔⟨ ∃-comm ⟩
  (Contractibleᴱ B × Erased ∥ B ∥) × (∃ λ R → Contractibleᴱ R)        ↝⟨ (drop-⊤-right λ _ → EEq.∃Contractibleᴱ≃ᴱ⊤ ext univ) ⟩
  Contractibleᴱ B × Erased ∥ B ∥                                      ↔⟨ (∃-cong λ cB → Erased-cong (inhabited⇒∥∥↔⊤ ∣ proj₁ cB ∣)) ⟩
  Contractibleᴱ B × Erased ⊤                                          ↔⟨ (drop-⊤-right λ _ → Erased-⊤↔⊤) ⟩□
  Contractibleᴱ B                                                     □

-- Lens ⊥ B is equivalent (with erased proofs) to the unit type
-- (assuming univalence).

lens-from-⊥↔⊤ :
  {B : Set b} →
  @0 Univalence (a ⊔ b) →
  Lens (⊥ {ℓ = a}) B ≃ᴱ ⊤
lens-from-⊥↔⊤ {B = B} univ =
  _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
      ≃ᴱ×→Lens
        (⊥      ↔⟨ inverse ×-left-zero ⟩□
         ⊥ × B  □)
    , [ (λ l → _↔_.from (equality-characterisation₁ univ)
                 ( (⊥ × Erased ∥ B ∥  ↔⟨ ×-left-zero ⟩
                    ⊥₀                ↝⟨ lemma l ⟩□
                    R l               □)
                 , λ x → ⊥-elim x
                 ))
      ]
  where
  open Lens

  @0 lemma : (l : Lens ⊥ B) → ⊥₀ ≃ R l
  lemma l = Eq.↔→≃ ⊥-elim whatever whatever (λ x → ⊥-elim x)
    where
    whatever : (r : R l) → P r
    whatever r = ⊥-elim {ℓ = lzero} $ PT.rec
      ⊥-propositional
      (λ b → ⊥-elim (_≃ᴱ_.from (equiv l) (r , b)))
      (inhabited l r)

-- There is an equivalence with erased proofs between A ≃ᴱ B and
-- ∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l) (assuming
-- univalence).
--
-- See also ≃≃≊ below.

≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get :
  {A : Set a} {B : Set b} →
  @0 Univalence (a ⊔ b) →
  (A ≃ᴱ B) ≃ᴱ (∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l))
≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get univ = EEq.↔→≃ᴱ
  (λ A≃B → ≃ᴱ→Lens A≃B , _≃ᴱ_.is-equivalence A≃B)
  (λ (l , eq) → EEq.⟨ Lens.get l , eq ⟩)
  (λ (l , eq) → Σ-≡,≡→≡
     (sym $ get-equivalence→≡≃ᴱ→Lens univ l eq)
     (EEq.Is-equivalenceᴱ-propositional ext _ _ _))
  (λ _ → EEq.to≡to→≡ ext (refl _))

-- The right-to-left direction of ≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get
-- returns the lens's getter (and some proof).

to-from-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get≡get :
  {A : Set a} {B : Set b} →
  (@0 univ : Univalence (a ⊔ b))
  (p@(l , _) : ∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l)) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get univ) p) ≡
  Lens.get l
to-from-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get≡get _ _ = refl _

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- In general there is no split surjection from Lens A B to
-- Traditionalᴱ.Lens A B (assuming univalence).

¬Lens↠Traditional-lens :
  @0 Univalence lzero →
  ¬ (Lens 𝕊¹ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ ⊤)
¬Lens↠Traditional-lens univ =
  Stable-¬ _
    [ (Lens 𝕊¹ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ ⊤)  ↝⟨ (λ f → from-equivalence Traditionalᴱ.Lens≃Traditional-lens F.∘
                                                      f F.∘
                                                      from-equivalence (inverse Lens≃Higher-lens)) ⟩
      (H.Lens 𝕊¹ ⊤ ↠ T.Lens 𝕊¹ ⊤)           ↝⟨ H.¬Lens↠Traditional-lens univ ⟩□
      ⊥                                     □
    ]

-- In general there is no equivalence with erased proofs between
-- Lens A B and Traditionalᴱ.Lens A B (assuming univalence).

¬Lens≃ᴱTraditional-lens :
  @0 Univalence lzero →
  ¬ (Lens 𝕊¹ ⊤ ≃ᴱ Traditionalᴱ.Lens 𝕊¹ ⊤)
¬Lens≃ᴱTraditional-lens univ =
  Stable-¬ _
    [ (Lens 𝕊¹ ⊤ ≃ᴱ Traditionalᴱ.Lens 𝕊¹ ⊤)  ↝⟨ from-equivalence ⊚ EEq.≃ᴱ→≃ ⟩
      (Lens 𝕊¹ ⊤ ↠  Traditionalᴱ.Lens 𝕊¹ ⊤)  ↝⟨ ¬Lens↠Traditional-lens univ ⟩□
      ⊥                                      □
    ]

-- Some lemmas used in Lens↠Traditional-lens and
-- Lens≃ᴱTraditional-lens below.

private

  module Lens≃ᴱTraditional-lens
    {A : Set a} {B : Set b}
    (@0 A-set : Is-set A)
    where

    from : Block "conversion" → Traditionalᴱ.Lens A B → Lens A B
    from ⊠ l = ≃ᴱ×→Lens
      {R = ∃ λ (f : B → A) → Erased (∀ b b′ → set (f b) b′ ≡ f b′)}
      (EEq.↔→≃ᴱ
         (λ a → (set a , [ set-set a ]) , get a)
         (λ ((f , _) , b) → f b)
         (λ ((f , [ h ]) , b) →

              let
                irr = {p q : Erased (∀ b b′ → set (f b) b′ ≡ f b′)} →
                      p ≡ q
                irr =
                  (H-level-Erased 1 (
                   Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   A-set)) _ _

                lemma =
                  get (f b)          ≡⟨ cong get (sym (h b b)) ⟩
                  get (set (f b) b)  ≡⟨ get-set (f b) b ⟩∎
                  b                  ∎
              in
              (set (f b) , [ set-set (f b) ]) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ (⟨ext⟩ (h b)) irr) lemma ⟩∎
              (f         , [ h             ]) , b          ∎)
         (λ a →
            set a (get a)  ≡⟨ set-get a ⟩∎
            a              ∎))
      where
      open Traditionalᴱ.Lens l

    to∘from : ∀ bc l → Lens.traditional-lens (from bc l) ≡ l
    to∘from ⊠ l = _↔_.from Traditionalᴱ.equality-characterisation₁
      ( refl _
      , refl _
      , [ (λ a _ → B-set a _ _)
        , (λ _ → A-set _ _)
        , (λ _ _ _ → A-set _ _)
        ]
      )
      where
      open Traditionalᴱ.Lens l

      @0 B-set : A → Is-set B
      B-set a =
        Traditionalᴱ.h-level-respects-lens-from-inhabited 2 l a A-set

    @0 from∘to :
      Univalence (a ⊔ b) →
      ∀ bc l → from bc (Lens.traditional-lens l) ≡ l
    from∘to univ ⊠ l′ =
      _↔_.from (equality-characterisation₃ univ)
        ( lemma
        , λ p →
            _≃ᴱ_.from l (subst (λ _ → R) (refl _) (proj₁ p) , proj₂ p)  ≡⟨ cong (λ r → _≃ᴱ_.from l (r , proj₂ p)) $ subst-refl _ _ ⟩∎
            _≃ᴱ_.from l p                                               ∎
        )
      where
      open Lens l′ renaming (equiv to l)

      B-set : (B → R) → ∥ B ∥ → Is-set B
      B-set f = PT.rec
        (H-level-propositional ext 2)
        (λ b →            $⟨ (λ {_ _} → A-set) ⟩
          Is-set A        ↝⟨ H-level-cong _ 2 (EEq.≃ᴱ→≃ l) ⟩
          Is-set (R × B)  ↝⟨ proj₂-closure (f b) 2 ⟩□
          Is-set B        □)

      R-set : ∥ B ∥ → Is-set R
      R-set = PT.rec
        (H-level-propositional ext 2)
        (λ b →            $⟨ (λ {_ _} → A-set) ⟩
          Is-set A        ↝⟨ H-level-cong _ 2 (EEq.≃ᴱ→≃ l) ⟩
          Is-set (R × B)  ↝⟨ proj₁-closure (const b) 2 ⟩□
          Is-set R        □)

      lemma′ : (∥ B ∥ × (∥ B ∥ → R)) ≃ R
      lemma′ = Eq.↔→≃
        (λ (b , f) → f b)
        (λ r → inhabited r , λ _ → r)
        refl
        (λ (b , f) → curry (_↔_.to ≡×≡↔≡)
           (PT.truncation-is-proposition _ _)
           (⟨ext⟩ λ b′ →
              f b   ≡⟨ cong f (PT.truncation-is-proposition _ _) ⟩∎
              f b′  ∎))

      lemma =
        (∃ λ (f : B → A) →
           Erased (∀ b b′ →
                   _≃ᴱ_.from l (proj₁ (_≃ᴱ_.to l (f b)) , b′) ≡
                   f b′)) ×
        Erased ∥ B ∥                                                ↔⟨ (∃-cong λ _ → erased Erased↔) ×-cong erased Erased↔ ⟩

        (∃ λ (f : B → A) → ∀ b b′ →
             _≃ᴱ_.from l (proj₁ (_≃ᴱ_.to l (f b)) , b′) ≡ f b′) ×
        ∥ B ∥                                                       ↔⟨ ×-comm ⟩

        (∥ B ∥ ×
         ∃ λ (f : B → A) → ∀ b b′ →
             _≃ᴱ_.from l (proj₁ (_≃ᴱ_.to l (f b)) , b′) ≡ f b′)     ↝⟨ (∃-cong λ _ →
                                                                        Σ-cong (→-cong ext F.id (EEq.≃ᴱ→≃ l)) λ f →
                                                                        ∀-cong ext λ b → ∀-cong ext λ b′ →
                                                                        ≡⇒↝ _ $ cong (_≃ᴱ_.from l (proj₁ (_≃ᴱ_.to l (f b)) , b′) ≡_) $ sym $
                                                                        _≃ᴱ_.left-inverse-of l _) ⟩
        (∥ B ∥ ×
         ∃ λ (f : B → R × B) → ∀ b b′ →
             _≃ᴱ_.from l (proj₁ (f b) , b′) ≡ _≃ᴱ_.from l (f b′))   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        Eq.≃-≡ (inverse (EEq.≃ᴱ→≃ l))) ⟩
        (∥ B ∥ ×
         ∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)  ↔⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        inverse $ ≡×≡↔≡) ⟩
        (∥ B ∥ ×
         ∃ λ (p : (B → R) × (B → B)) →
           ∀ b b′ → proj₁ p b ≡ proj₁ p b′ × b′ ≡ proj₂ p b′)       ↔⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

        (∥ B ∥ ×
         ∃ λ (f : B → R) → ∃ λ (g : B → B) →
           ∀ b b′ → f b ≡ f b′ × b′ ≡ g b′)                         ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                        ΠΣ-comm) ⟩
        (∥ B ∥ ×
         ∃ λ (f : B → R) → ∃ λ (g : B → B) →
           ∀ b → (∀ b′ → f b ≡ f b′) × (∀ b′ → b′ ≡ g b′))          ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ΠΣ-comm) ⟩

        (∥ B ∥ ×
         ∃ λ (f : B → R) → ∃ λ (g : B → B) →
           Constant f × (B → ∀ b → b ≡ g b))                        ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

        (∥ B ∥ ×
         ∃ λ (f : B → R) → Constant f ×
         ∃ λ (g : B → B) → B → ∀ b → b ≡ g b)                       ↔⟨ (∃-cong λ _ → Σ-assoc) ⟩

        (∥ B ∥ ×
         (∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → B → ∀ b → b ≡ g b))                     ↔⟨ (∃-cong λ ∥b∥ → ∃-cong $ uncurry λ f _ → ∃-cong λ _ → inverse $
                                                                        →-intro ext (λ _ → B-set f ∥b∥)) ⟩
        (∥ B ∥ ×
         (∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → ∀ b → b ≡ g b))                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                        Eq.extensionality-isomorphism ext) ⟩
        (∥ B ∥ ×
         (∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → F.id ≡ g))                              ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                                        _⇔_.to contractible⇔↔⊤ $
                                                                        other-singleton-contractible _) ⟩

        (∥ B ∥ × ∃ λ (f : B → R) → Constant f)                      ↝⟨ (∃-cong λ ∥b∥ → PT.constant-function≃∥inhabited∥⇒inhabited (R-set ∥b∥)) ⟩

        (∥ B ∥ × (∥ B ∥ → R))                                       ↔⟨ lemma′ ⟩□

        R                                                           □

    equiv :
      Block "conversion" →
      @0 Univalence (a ⊔ b) →
      Lens A B ≃ᴱ Traditionalᴱ.Lens A B
    equiv bc univ = EEq.↔→≃ᴱ
      _
      (from bc)
      (to∘from bc)
      (from∘to univ bc)

-- If the domain A is a set, then there is a split surjection from
-- Lens A B to Traditionalᴱ.Lens A B.

Lens↠Traditional-lens :
  Block "conversion" →
  @0 Is-set A →
  Lens A B ↠ Traditionalᴱ.Lens A B
Lens↠Traditional-lens {A = A} {B = B} bc A-set = record
  { logical-equivalence = record
    { to   = Lens.traditional-lens
    ; from = Lens≃ᴱTraditional-lens.from A-set bc
    }
  ; right-inverse-of = Lens≃ᴱTraditional-lens.to∘from A-set bc
  }

-- The split surjection above preserves getters and setters.

Lens↠Traditional-lens-preserves-getters-and-setters :
  {A : Set a}
  (b : Block "conversion")
  (@0 s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_↠_.logical-equivalence (Lens↠Traditional-lens b s))
Lens↠Traditional-lens-preserves-getters-and-setters ⊠ _ =
  (λ _ → refl _ , refl _) , (λ _ → refl _ , refl _)

-- If the domain A is a set, then there is an equivalence with erased
-- proofs between Traditionalᴱ.Lens A B and Lens A B (assuming
-- univalence).

Lens≃ᴱTraditional-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  @0 Univalence (a ⊔ b) →
  @0 Is-set A →
  Lens A B ≃ᴱ Traditionalᴱ.Lens A B
Lens≃ᴱTraditional-lens bc univ A-set =
  Lens≃ᴱTraditional-lens.equiv A-set bc univ

-- The equivalence preserves getters and setters.

Lens≃ᴱTraditional-lens-preserves-getters-and-setters :
  {A : Set a} {B : Set b}
  (bc : Block "conversion")
  (@0 univ : Univalence (a ⊔ b))
  (@0 s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱTraditional-lens bc univ s))
Lens≃ᴱTraditional-lens-preserves-getters-and-setters bc _ =
  Lens↠Traditional-lens-preserves-getters-and-setters bc

-- If the codomain B is an inhabited set, then Lens A B and
-- Traditionalᴱ.Lens A B are logically equivalent.
--
-- This definition is inspired by the statement of Corollary 13 from
-- "Algebras and Update Strategies" by Johnson, Rosebrugh and Wood.

Lens⇔Traditional-lens :
  @0 Is-set B →
  B →
  Lens A B ⇔ Traditionalᴱ.Lens A B
Lens⇔Traditional-lens {B = B} {A = A} B-set b₀ = record
  { to   = Lens.traditional-lens
  ; from = from
  }
  where
  from : Traditionalᴱ.Lens A B → Lens A B
  from l = ≃ᴱ×→Lens
    {R = ∃ λ (a : A) → Erased (get a ≡ b₀)}
    (EEq.↔→≃ᴱ
       (λ a → (set a b₀ , [ get-set a b₀ ]) , get a)
       (λ ((a , _) , b) → set a b)
       (λ ((a , [ h ]) , b) →
          let lemma =
                set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
                set a b₀          ≡⟨ cong (set a) (sym h) ⟩
                set a (get a)     ≡⟨ set-get a ⟩∎
                a                 ∎
          in
          ( (set (set a b) b₀ , [ get-set (set a b) b₀ ])
          , get (set a b)
          )                                                ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma (H-level-Erased 1 B-set _ _)) (get-set a b) ⟩∎
          ((a , [ h ]) , b)                                ∎)
       (λ a →
          set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
          set a (get a)           ≡⟨ set-get a ⟩∎
          a                       ∎))
    where
    open Traditionalᴱ.Lens l

-- The logical equivalence preserves getters and setters (in an erased
-- context).

@0 Lens⇔Traditional-lens-preserves-getters-and-setters :
  {B : Set b}
  (s : Is-set B)
  (b₀ : B) →
  Preserves-getters-and-setters-⇔ A B (Lens⇔Traditional-lens s b₀)
Lens⇔Traditional-lens-preserves-getters-and-setters _ b₀ =
    (λ _ → refl _ , refl _)
  , (λ l → refl _
         , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
           set l (set l a b₀) b  ≡⟨ set-set l _ _ _ ⟩∎
           set l a b             ∎)
  where
  open Traditionalᴱ.Lens

------------------------------------------------------------------------
-- Some results related to h-levels

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n (in erased contexts).

@0 h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited n l =
  H.h-level-respects-lens-from-inhabited n (high l)

-- This is not necessarily true for arbitrary domains (assuming
-- univalence).

¬-h-level-respects-lens :
  @0 Univalence lzero →
  ¬ (∀ n → Lens ⊥₀ Bool → H-level n ⊥₀ → H-level n Bool)
¬-h-level-respects-lens univ =
  Stable-¬ _
    [ (∀ n → Lens ⊥ Bool → H-level n ⊥ → H-level n Bool)    ↝⟨ (λ hyp n l → hyp n (Higher-lens→Lens l)) ⟩
      (∀ n → H.Lens ⊥ Bool → H-level n ⊥ → H-level n Bool)  ↝⟨ H.¬-h-level-respects-lens univ ⟩□
      ⊥                                                     □
    ]

-- In fact, there is a lens with a proposition as its domain and a
-- non-set as its codomain (assuming univalence).

lens-from-proposition-to-non-set :
  @0 Univalence (# 0) →
  ∃ λ (A : Set a) → ∃ λ (B : Set b) →
  Lens A B × Is-proposition A × ¬ Is-set B
lens-from-proposition-to-non-set {a = a} {b = b} univ =
    ⊥
  , ↑ b 𝕊¹
  , record
      { R         = ⊥
      ; equiv     = ⊥           ↔⟨ inverse ×-left-zero ⟩□
                    ⊥ × ↑ _ 𝕊¹  □
      ; inhabited = ⊥-elim
      }
  , ⊥-propositional
  , Stable-¬ _
      [ Is-set (↑ b 𝕊¹)  ↝⟨ proj₂ $ proj₂ $ proj₂ $ proj₂ $ H.lens-from-proposition-to-non-set {a = a} univ ⟩□
        ⊥₀               □
      ]

-- Lenses with contractible domains have contractible codomains (in
-- erased contexts).

@0 contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l =
  H.contractible-to-contractible (high l)

-- A variant for Contractibleᴱ.

Contractibleᴱ→Contractibleᴱ :
  Lens A B → Contractibleᴱ A → Contractibleᴱ B
Contractibleᴱ→Contractibleᴱ =
  Traditionalᴱ.Contractibleᴱ→Contractibleᴱ ⊚
  Lens.traditional-lens

-- If the domain type of a lens is contractible with an erased proof,
-- then the remainder type is also contractible with an erased proof.

domain-Contractibleᴱ⇒remainder-Contractibleᴱ :
  (l : Lens A B) → Contractibleᴱ A → Contractibleᴱ (Lens.R l)
domain-Contractibleᴱ⇒remainder-Contractibleᴱ {A = A} {B = B} l =
  Contractibleᴱ A                    ↝⟨ EEq.Contractibleᴱ-respects-surjection
                                          (_≃ᴱ_.to equiv) (_≃_.split-surjective (EEq.≃ᴱ→≃ equiv)) ⟩
  Contractibleᴱ (R × B)              ↝⟨ _≃ᴱ_.to (EEq.Contractibleᴱ-commutes-with-× ext) ⟩
  Contractibleᴱ R × Contractibleᴱ B  ↝⟨ proj₁ ⟩□
  Contractibleᴱ R                    □
  where
  open Lens l

-- If the domain type of a lens has h-level n, then the remainder type
-- also has h-level n (in erased contexts).

@0 remainder-has-same-h-level-as-domain :
  (l : Lens A B) → ∀ n → H-level n A → H-level n (Lens.R l)
remainder-has-same-h-level-as-domain l n =
  H.remainder-has-same-h-level-as-domain (high l) n

-- If the getter function is an equivalence, then the remainder type
-- is propositional (in erased contexts).

@0 get-equivalence→remainder-propositional :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) →
  Is-proposition (Lens.R l)
get-equivalence→remainder-propositional =
  H.get-equivalence→remainder-propositional ⊚ high

-- If the getter function is pointwise equal to the identity function,
-- then the remainder type is propositional (in erased contexts).

@0 get≡id→remainder-propositional :
  (l : Lens A A) →
  (∀ a → Lens.get l a ≡ a) →
  Is-proposition (Lens.R l)
get≡id→remainder-propositional =
  H.get≡id→remainder-propositional ⊚ high

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Lens A B (assuming univalence).

¬-Contractible-closed-domain :
  ∀ {a b} →
  @0 Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Contractible A → Contractible (Lens A B))
¬-Contractible-closed-domain univ =
  Stable-¬ _
    [ (∀ {A B} → Contractible A → Contractible (Lens A B))    ↝⟨ (λ hyp c → H-level-cong _ 0 Lens≃Higher-lens (hyp c)) ⟩
      (∀ {A B} → Contractible A → Contractible (H.Lens A B))  ↝⟨ H.¬-Contractible-closed-domain univ ⟩□
      ⊥                                                       □
    ]

-- Contractibleᴱ is closed under Lens A (assuming univalence).

Contractibleᴱ-closed-codomain :
  {A : Set a} {B : Set b} →
  @0 Univalence (a ⊔ b) →
  Contractibleᴱ B → Contractibleᴱ (Lens A B)
Contractibleᴱ-closed-codomain {A = A} {B} univ cB =
                            $⟨ lens-to-contractible≃ᴱ⊤ univ cB ⟩
  Lens A B ≃ᴱ ⊤             ↝⟨ _⇔_.from EEq.Contractibleᴱ⇔≃ᴱ⊤ ⟩□
  Contractibleᴱ (Lens A B)  □

-- If B is a proposition, then Lens A B is also a proposition
-- (in erased contexts, assuming univalence).

@0 Is-proposition-closed-codomain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B → Is-proposition (Lens A B)
Is-proposition-closed-codomain {A = A} {B = B} univ =
  Is-proposition B             ↝⟨ H.Is-proposition-closed-codomain univ ⟩
  Is-proposition (H.Lens A B)  ↝⟨ H-level-cong _ 1 (inverse Lens≃Higher-lens) ⟩□
  Is-proposition (Lens A B)    □

-- If A is a proposition, then Lens A B is also a proposition
-- (in erased contexts, assuming univalence).

@0 Is-proposition-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Lens A B)
Is-proposition-closed-domain {A = A} {B = B} univ =
  Is-proposition A             ↝⟨ H.Is-proposition-closed-domain univ ⟩
  Is-proposition (H.Lens A B)  ↝⟨ H-level-cong _ 1 (inverse Lens≃Higher-lens) ⟩□
  Is-proposition (Lens A B)    □

-- If A is a set, then Lens A B is also a set (in erased contexts,
-- assuming univalence).

@0 Is-set-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-set A → Is-set (Lens A B)
Is-set-closed-domain {A = A} {B = B} univ =
  Is-set A             ↝⟨ H.Is-set-closed-domain univ ⟩
  Is-set (H.Lens A B)  ↝⟨ H-level-cong _ 2 (inverse Lens≃Higher-lens) ⟩□
  Is-set (Lens A B)    □

-- If A has h-level n, then Lens A B has h-level 1 + n (in erased
-- contexts, assuming univalence).

@0 domain-0+⇒lens-1+ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Lens A B)
domain-0+⇒lens-1+ {A = A} {B = B} univ n =
  H-level n A                   ↝⟨ H.domain-0+⇒lens-1+ univ n ⟩
  H-level (1 + n) (H.Lens A B)  ↝⟨ H-level-cong _ (1 + n) (inverse Lens≃Higher-lens) ⟩□
  H-level (1 + n) (Lens A B)    □

-- If B is inhabited when it is merely inhabited and A has positive
-- h-level n, then Lens A B also has h-level n (in erased contexts,
-- assuming univalence).

@0 lens-preserves-h-level-of-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (∥ B ∥ → B) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain {A = A} {B = B} univ ∥B∥→B n =
  H-level (1 + n) A             ↝⟨ EP.higher-lens-preserves-h-level-of-domain univ ∥B∥→B n ⟩
  H-level (1 + n) (H.Lens A B)  ↝⟨ H-level-cong _ (1 + n) (inverse Lens≃Higher-lens) ⟩□
  H-level (1 + n) (Lens A B)    □

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ¬ Lens (∃ λ (b : Bool) → b ≡ true) Bool
no-first-projection-lens =
  Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

------------------------------------------------------------------------
-- Some results related to the remainder type

-- The remainder type of a lens l : Lens A B is, for every b : B,
-- equivalent (with erased proofs) to the preimage (with an erased
-- proof) of the getter with respect to b.
--
-- The corresponding result in Lens.Non-dependent.Higher was pointed
-- out to me by Andrea Vezzosi.

remainder≃ᴱget⁻¹ᴱ :
  (l : Lens A B) (b : B) → Lens.R l ≃ᴱ Lens.get l ⁻¹ᴱ b
remainder≃ᴱget⁻¹ᴱ l b = EEq.↔→≃ᴱ
  (λ r → _≃ᴱ_.from equiv (r , b)
       , [ get (_≃ᴱ_.from equiv (r , b))                    ≡⟨⟩
           proj₂ (_≃ᴱ_.to equiv (_≃ᴱ_.from equiv (r , b)))  ≡⟨ cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _ ⟩∎
           b                                                ∎
         ])
  (λ (a , _) → remainder a)
  (λ (a , [ get-a≡b ]) →
     let lemma₁ =
           cong get
             (trans (cong (set a) (sym get-a≡b))
                (_≃ᴱ_.left-inverse-of equiv _))                           ≡⟨ cong-trans _ _ (_≃ᴱ_.left-inverse-of equiv _) ⟩

           trans (cong get (cong (set a) (sym get-a≡b)))
             (cong get (_≃ᴱ_.left-inverse-of equiv _))                    ≡⟨ cong₂ trans
                                                                              (cong-∘ _ _ (sym get-a≡b))
                                                                              (sym $ cong-∘ _ _ (_≃ᴱ_.left-inverse-of equiv _)) ⟩
           trans (cong (get ⊚ set a) (sym get-a≡b))
             (cong proj₂ (cong (_≃ᴱ_.to equiv)
                            (_≃ᴱ_.left-inverse-of equiv _)))              ≡⟨ cong₂ (λ p q → trans p (cong proj₂ q))
                                                                              (cong-sym _ get-a≡b)
                                                                              (_≃ᴱ_.left-right-lemma equiv _) ⟩
           trans (sym (cong (get ⊚ set a) get-a≡b))
             (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _))                 ≡⟨ sym $ sym-sym _ ⟩

           sym (sym (trans (sym (cong (get ⊚ set a) get-a≡b))
                       (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _))))     ≡⟨ cong sym $
                                                                            sym-trans _ (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)) ⟩
           sym (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                  (sym (sym (cong (get ⊚ set a) get-a≡b))))              ≡⟨ cong (λ eq → sym (trans (sym (cong proj₂
                                                                                                            (_≃ᴱ_.right-inverse-of equiv _)))
                                                                                                eq)) $
                                                                            sym-sym (cong (get ⊚ set a) get-a≡b) ⟩∎
           sym (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                  (cong (get ⊚ set a) get-a≡b))                          ∎

         lemma₂ =
           subst (λ a → get a ≡ b)
             (trans (cong (set a) (sym get-a≡b)) (set-get a))
             (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv (remainder a , b))     ≡⟨⟩

           subst (λ a → get a ≡ b)
             (trans (cong (set a) (sym get-a≡b))
                (_≃ᴱ_.left-inverse-of equiv _))
             (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                     ≡⟨ subst-∘ _ _ (trans _ (_≃ᴱ_.left-inverse-of equiv _)) ⟩

            subst (_≡ b)
              (cong get
                 (trans (cong (set a) (sym get-a≡b))
                    (_≃ᴱ_.left-inverse-of equiv _)))
              (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                    ≡⟨ cong (λ eq → subst (_≡ b) eq
                                                                                                (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _))
                                                                                 lemma₁ ⟩
            subst (_≡ b)
              (sym (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                      (cong (get ⊚ set a) get-a≡b)))
              (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                    ≡⟨ subst-trans (trans _ (cong (get ⊚ set a) get-a≡b)) ⟩

            trans
              (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                 (cong (get ⊚ set a) get-a≡b))
              (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                    ≡⟨ elim¹
                                                                                   (λ eq →
                                                                                      trans
                                                                                        (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                                                                                           (cong (get ⊚ set a) eq))
                                                                                        (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _) ≡
                                                                                      eq)
                                                                                   (
                trans
                  (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                     (cong (get ⊚ set a) (refl _)))
                  (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                      ≡⟨ cong
                                                                                         (λ eq → trans
                                                                                                   (trans (sym (cong proj₂
                                                                                                                  (_≃ᴱ_.right-inverse-of equiv _)))
                                                                                                      eq)
                                                                                                   (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)) $
                                                                                      cong-refl _ ⟩
                trans
                  (trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                     (refl _))
                  (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                      ≡⟨ cong (flip trans _) $ trans-reflʳ _ ⟩

                trans (sym (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)))
                  (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv _)                      ≡⟨ trans-symˡ (cong proj₂ (_≃ᴱ_.right-inverse-of equiv _)) ⟩∎

                refl _                                                              ∎)
                                                                                   get-a≡b ⟩∎
            get-a≡b                                                           ∎
     in
     Σ-≡,≡→≡
       (_≃ᴱ_.from equiv (remainder a , b)  ≡⟨⟩
        set a b                            ≡⟨ cong (set a) (sym get-a≡b) ⟩
        set a (get a)                      ≡⟨ set-get a ⟩∎
        a                                  ∎)
       (subst (λ a → Erased (get a ≡ b))
          (trans (cong (set a) (sym get-a≡b)) (set-get a))
          [ cong proj₂ $ _≃ᴱ_.right-inverse-of equiv (remainder a , b) ]  ≡⟨ push-subst-[] ⟩

        [ subst (λ a → get a ≡ b)
          (trans (cong (set a) (sym get-a≡b)) (set-get a))
          (cong proj₂ $ _≃ᴱ_.right-inverse-of equiv (remainder a , b))
        ]                                                                 ≡⟨ []-cong [ lemma₂ ] ⟩∎

        [ get-a≡b ]                                                       ∎))
  (λ r →
     remainder (_≃ᴱ_.from equiv (r , b))              ≡⟨⟩
     proj₁ (_≃ᴱ_.to equiv (_≃ᴱ_.from equiv (r , b)))  ≡⟨ cong proj₁ $ _≃ᴱ_.right-inverse-of equiv _ ⟩∎
     r                                                ∎)
  where
  open Lens l

-- A corollary: Lens.get l ⁻¹ᴱ_ is constant (up to _≃ᴱ_).
--
-- Paolo Capriotti discusses this kind of property
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

get⁻¹ᴱ-constant :
  (l : Lens A B) (b₁ b₂ : B) → Lens.get l ⁻¹ᴱ b₁ ≃ᴱ Lens.get l ⁻¹ᴱ b₂
get⁻¹ᴱ-constant l b₁ b₂ =
  Lens.get l ⁻¹ᴱ b₁  ↝⟨ inverse $ remainder≃ᴱget⁻¹ᴱ l b₁ ⟩
  Lens.R l           ↝⟨ remainder≃ᴱget⁻¹ᴱ l b₂ ⟩□
  Lens.get l ⁻¹ᴱ b₂  □

-- The set function can be expressed using get⁻¹ᴱ-constant and get.
--
-- Paolo Capriotti defines set in a similar way
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

set-in-terms-of-get⁻¹ᴱ-constant :
  (l : Lens A B) →
  Lens.set l ≡
  λ a b → proj₁ (_≃ᴱ_.to (get⁻¹ᴱ-constant l (Lens.get l a) b)
                   (a , [ refl _ ]))
set-in-terms-of-get⁻¹ᴱ-constant l = refl _

-- The remainder function can be expressed using remainder≃ᴱget⁻¹ᴱ and
-- get.

remainder-in-terms-of-remainder≃ᴱget⁻¹ᴱ :
  (l : Lens A B) →
  Lens.remainder l ≡
  λ a → _≃ᴱ_.from (remainder≃ᴱget⁻¹ᴱ l (Lens.get l a)) (a , [ refl _ ])
remainder-in-terms-of-remainder≃ᴱget⁻¹ᴱ l = refl _

-- The lemma get⁻¹ᴱ-constant satisfies some coherence properties.
--
-- The first and third properties are discussed by Paolo Capriotti
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

@0 get⁻¹ᴱ-constant-∘ :
  (l : Lens A B) (b₁ b₂ b₃ : B) (p : Lens.get l ⁻¹ᴱ b₁) →
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b₂ b₃)
    (_≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₂) p) ≡
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₃) p
get⁻¹ᴱ-constant-∘ l _ b₂ b₃ p =
  from (r₂ , b₃) , [ cong proj₂ (right-inverse-of (r₂ , b₃)) ]  ≡⟨ cong (λ r → from (r , b₃) , [ cong proj₂ (right-inverse-of (r , b₃)) ]) $
                                                                   cong proj₁ $ right-inverse-of _ ⟩∎
  from (r₁ , b₃) , [ cong proj₂ (right-inverse-of (r₁ , b₃)) ]  ∎
  where
  open Lens l
  open _≃ᴱ_ equiv

  r₁ r₂ : R
  r₁ = proj₁ (to (proj₁ p))
  r₂ = proj₁ (to (from (r₁ , b₂)))

get⁻¹ᴱ-constant-inverse :
  (l : Lens A B) (b₁ b₂ : B) (p : Lens.get l ⁻¹ᴱ b₁) →
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₂) p ≡
  _≃ᴱ_.from (get⁻¹ᴱ-constant l b₂ b₁) p
get⁻¹ᴱ-constant-inverse _ _ _ _ = refl _

@0 get⁻¹ᴱ-constant-id :
  (l : Lens A B) (b : B) (p : Lens.get l ⁻¹ᴱ b) →
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b b) p ≡ p
get⁻¹ᴱ-constant-id l b p =
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b b) p                                      ≡⟨ sym $ get⁻¹ᴱ-constant-∘ l b _ _ p ⟩
  _≃ᴱ_.to (get⁻¹ᴱ-constant l b b) (_≃ᴱ_.to (get⁻¹ᴱ-constant l b b) p)    ≡⟨⟩
  _≃ᴱ_.from (get⁻¹ᴱ-constant l b b) (_≃ᴱ_.to (get⁻¹ᴱ-constant l b b) p)  ≡⟨ _≃ᴱ_.left-inverse-of (get⁻¹ᴱ-constant l b b) _ ⟩∎
  p                                                                      ∎

-- Another kind of coherence property does not hold for
-- get⁻¹ᴱ-constant.
--
-- This kind of property came up in a discussion with Andrea Vezzosi.

get⁻¹ᴱ-constant-not-coherent :
  ¬ ({A B : Set} (l : Lens A B) (b₁ b₂ : B)
     (f : ∀ b → Lens.get l ⁻¹ᴱ b) →
     _≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₂) (f b₁) ≡ f b₂)
get⁻¹ᴱ-constant-not-coherent =
  ({A B : Set} (l : Lens A B) (b₁ b₂ : B)
   (f : ∀ b → Lens.get l ⁻¹ᴱ b) →
   _≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₂) (f b₁) ≡ f b₂)          ↝⟨ (λ hyp → hyp l true false f) ⟩

  _≃ᴱ_.to (get⁻¹ᴱ-constant l true false) (f true) ≡ f false  ↝⟨ cong (proj₁ ⊚ proj₁) ⟩

  true ≡ false                                               ↝⟨ Bool.true≢false ⟩□

  ⊥                                                          □
  where
  l : Lens (Bool × Bool) Bool
  l = record
    { R         = Bool
    ; equiv     = F.id
    ; inhabited = ∣_∣
    }

  f : ∀ b → Lens.get l ⁻¹ᴱ b
  f b = (b , b) , [ refl _ ]

-- If B is inhabited whenever it is merely inhabited, then the
-- remainder type of a lens of type Lens A B can be expressed in terms
-- of preimages of the lens's getter (in erased contexts).
--
-- TODO: Perhaps a non-erased variant of this result could be proved
-- if the inhabited field were made non-erased, possibly with ∥_∥
-- replaced by ∥_∥ᴱ.

@0 remainder≃∃get⁻¹ :
  (l : Lens A B) (∥B∥→B : ∥ B ∥ → B) →
  Lens.R l ≃ ∃ λ (b : ∥ B ∥) → Lens.get l ⁻¹ (∥B∥→B b)
remainder≃∃get⁻¹ = H.remainder≃∃get⁻¹ ⊚ high

------------------------------------------------------------------------
-- Lens combinators

private
  module HLC = H.Lens-combinators

module Lens-combinators where

  -- The definition of the identity lens is unique (in erased
  -- contexts), if the get function is required to be the identity
  -- (assuming univalence).

  @0 id-unique :
    {A : Set a} →
    Univalence a →
    (l₁ l₂ : Lens A A) →
    Lens.get l₁ ≡ P.id →
    Lens.get l₂ ≡ P.id →
    l₁ ≡ l₂
  id-unique {A = A} univ l₁ l₂ g₁ g₂ =
                       $⟨ HLC.id-unique univ (high l₁) (high l₂) g₁ g₂ ⟩
    high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
    l₁ ≡ l₂            □

  -- The result of composing two lenses is unique (in erased contexts)
  -- if the codomain type is inhabited whenever it is merely
  -- inhabited, and we require that the resulting setter function is
  -- defined in a certain way (assuming univalence).

  @0 ∘-unique :
    let open Lens in
    {A : Set a} {C : Set c} →
    Univalence (a ⊔ c) →
    (∥ C ∥ → C) →
    ((comp₁ , _) (comp₂ , _) :
       ∃ λ (comp : Lens B C → Lens A B → Lens A C) →
         ∀ l₁ l₂ a c →
           set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp₁ ≡ comp₂
  ∘-unique {A = A} {C = C} univ ∥C∥→C
           (comp₁ , set₁) (comp₂ , set₂) =
    ⟨ext⟩ λ l₁ → ⟨ext⟩ λ l₂ →
      lenses-equal-if-setters-equal univ
        (comp₁ l₁ l₂) (comp₂ l₁ l₂) (λ _ → ∥C∥→C) $
        ⟨ext⟩ λ a → ⟨ext⟩ λ c →
          set (comp₁ l₁ l₂) a c           ≡⟨ set₁ _ _ _ _ ⟩
          set l₂ a (set l₁ (get l₂ a) c)  ≡⟨ sym $ set₂ _ _ _ _ ⟩∎
          set (comp₂ l₁ l₂) a c           ∎
    where
    open Lens

  -- Identity lens.

  id : Block "id" → Lens A A
  id {A = A} ⊠ = record
    { R         = Erased ∥ A ∥
    ; equiv     = A                 ↔⟨ inverse Erased-∥∥×≃ ⟩□
                  Erased ∥ A ∥ × A  □
    ; inhabited = erased
    }

  -- The identity lens is equal to the one obtained from the identity
  -- lens for higher lenses without erased proofs (in erased
  -- contexts, assuming univalence).

  @0 Higher-lens-id≡id :
    {A : Set a}
    (b : Block "id")
    (univ : Univalence a) →
    Higher-lens→Lens (HLC.id b) ≡ id {A = A} b
  Higher-lens-id≡id {A = A} ⊠ univ =
    _↔_.from (equality-characterisation₁ univ)
      ( (∥ A ∥         ↔⟨ inverse $ erased Erased↔ ⟩□
         Erased ∥ A ∥  □)
      , λ _ → refl _
      )

  -- Composition of lenses.
  --
  -- Note that the domains are required to be at least as large as the
  -- codomains.
  --
  -- The composition operation matches on the lenses to ensure that it
  -- does not unfold when applied to neutral lenses.

  infix 9 ⟨_,_⟩_∘_

  ⟨_,_⟩_∘_ :
    ∀ a b {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Lens B C → Lens A B → Lens A C
  ⟨_,_⟩_∘_ _ _ {A = A} {B} {C} l₁@(⟨ _ , _ , _ ⟩) l₂@(⟨ _ , _ , _ ⟩) =
    record
      { R         = R l₂ × R l₁
      ; equiv     = A                  ↝⟨ equiv l₂ ⟩
                    R l₂ × B           ↝⟨ F.id ×-cong equiv l₁ ⟩
                    R l₂ × (R l₁ × C)  ↔⟨ ×-assoc ⟩□
                    (R l₂ × R l₁) × C  □
      ; inhabited = ∥∥-map (get l₁) ⊚ inhabited l₂ ⊚ proj₁
      }
    where
    open Lens

  -- Higher-lens→Lens commutes with composition (in erased contexts,
  -- assuming univalence).

  @0 Higher-lens-∘≡∘ :
    ∀ a b {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Univalence (a ⊔ b ⊔ c) →
    (l₁ : H.Lens B C) (l₂ : H.Lens A B) →
    Higher-lens→Lens (HLC.⟨ a , b ⟩ l₁ ∘ l₂) ≡
    ⟨ a , b ⟩ Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂
  Higher-lens-∘≡∘ _ _ univ (H.⟨ _ , _ , _ ⟩) (H.⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₁ univ)
      ( F.id
      , λ _ → refl _
      )

  -- A variant of composition for lenses between types with the same
  -- universe level.

  infixr 9 _∘_

  _∘_ :
    {A B C : Set a} →
    Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = ⟨ lzero , lzero ⟩ l₁ ∘ l₂

  -- Other definitions of composition match ⟨_,_⟩_∘_ (in erased
  -- contexts), if the codomain type is inhabited whenever it is
  -- merely inhabited, and the resulting setter function is defined in
  -- a certain way (assuming univalence).

  @0 composition≡∘ :
    let open Lens in
    {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Univalence (a ⊔ b ⊔ c) →
    (∥ C ∥ → C) →
    (comp : Lens B C → Lens A B → Lens A C) →
    (∀ l₁ l₂ a c →
       set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp ≡ ⟨ a , b ⟩_∘_
  composition≡∘ univ ∥C∥→C comp set-comp =
    ∘-unique univ ∥C∥→C (comp , set-comp)
      (_ , λ { ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ → refl _ })

  -- Identity and composition form a kind of precategory (in erased
  -- contexts, assuming univalence).

  @0 associativity :
    ∀ a b c
      {A : Set (a ⊔ b ⊔ c ⊔ d)} {B : Set (b ⊔ c ⊔ d)}
      {C : Set (c ⊔ d)} {D : Set d} →
    Univalence (a ⊔ b ⊔ c ⊔ d) →
    (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ univ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ =
    _↔_.from (equality-characterisation₁ univ)
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl _)

  @0 left-identity :
    ∀ bi a {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ a , lzero ⟩ id bi ∘ l ≡ l
  left-identity ⊠ _ {B = B} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₁ univ)
      ( (R × Erased ∥ B ∥  ↔⟨ lemma ⟩□
         R                 □)
      , λ _ → refl _
      )
    where
    open Lens l

    lemma : R × Erased ∥ B ∥ ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₁
          ; from = λ r → r , [ inhabited r ]
          }
        ; right-inverse-of = λ _ → refl _
        }
      ; left-inverse-of = λ (r , _) →
          cong (r ,_) $ []-cong [ truncation-is-proposition _ _ ]
      }

  @0 right-identity :
    ∀ bi a {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ lzero , a ⟩ l ∘ id bi ≡ l
  right-identity ⊠ _ {A = A} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₁ univ)
      ( (Erased ∥ A ∥ × R  ↔⟨ lemma ⟩□
         R                 □)
      , λ _ → refl _
      )
    where
    open Lens l

    lemma : Erased ∥ A ∥ × R ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₂
          ; from = λ r → [ ∥∥-map (λ b → _≃ᴱ_.from equiv (r , b))
                                  (inhabited r)
                         ]
                       , r
          }
        ; right-inverse-of = λ _ → refl _
        }
      ; left-inverse-of = λ (_ , r) →
          cong (_, r) $ []-cong [ truncation-is-proposition _ _ ]
      }

open Lens-combinators

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private
  module B {a} (b : Block "id") =
    Bi-invertibility.Erased equality-with-J (Set a) Lens (id b) _∘_
  module BM {a} (b : Block "id") (@0 univ : Univalence a) = B.More
    b
    (left-identity b _ univ)
    (right-identity b _ univ)
    (associativity _ _ _ univ)

-- A form of isomorphism between types, expressed using lenses.

open B public renaming (_≅ᴱ_ to [_]_≅ᴱ_) using (Has-quasi-inverseᴱ)

private

  -- Some lemmas used below.

  @0 ∘≡id→∘≡id :
    {A B : Set a}
    (b : Block "id") →
    Univalence a →
    (l₁ : H.Lens B A) (l₂ : H.Lens A B) →
    l₁ HLC.∘ l₂ ≡ HLC.id b →
    Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂ ≡ id b
  ∘≡id→∘≡id b univ l₁ l₂ hyp =
    Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂  ≡⟨ sym $ Higher-lens-∘≡∘ lzero lzero univ l₁ l₂ ⟩
    Higher-lens→Lens (l₁ HLC.∘ l₂)             ≡⟨ cong Higher-lens→Lens hyp ⟩
    Higher-lens→Lens (HLC.id b)                ≡⟨ Higher-lens-id≡id b univ ⟩∎
    id b                                       ∎

  @0 l∘l⁻¹≡l∘l⁻¹ :
    {A B : Set a} →
    Univalence a →
    (l : H.Lens B A) (l⁻¹ : Lens A B) →
    Higher-lens→Lens (l HLC.∘ high l⁻¹) ≡ Higher-lens→Lens l ∘ l⁻¹
  l∘l⁻¹≡l∘l⁻¹ univ l l⁻¹ =
    Higher-lens→Lens (l HLC.∘ high l⁻¹)               ≡⟨ Higher-lens-∘≡∘ lzero lzero univ l (high l⁻¹) ⟩
    Higher-lens→Lens l ∘ Higher-lens→Lens (high l⁻¹)  ≡⟨ cong (Higher-lens→Lens l ∘_) $
                                                         _≃_.left-inverse-of Lens≃Higher-lens l⁻¹ ⟩∎
    Higher-lens→Lens l ∘ l⁻¹                          ∎

  @0 l⁻¹∘l≡l⁻¹∘l :
    {A B : Set a} →
    Univalence a →
    (l⁻¹ : Lens B A) (l : H.Lens A B) →
    Higher-lens→Lens (high l⁻¹ HLC.∘ l) ≡ l⁻¹ ∘ Higher-lens→Lens l
  l⁻¹∘l≡l⁻¹∘l univ l⁻¹ l =
    Higher-lens→Lens (high l⁻¹ HLC.∘ l)               ≡⟨ Higher-lens-∘≡∘ lzero lzero univ (high l⁻¹) l ⟩
    Higher-lens→Lens (high l⁻¹) ∘ Higher-lens→Lens l  ≡⟨ cong (_∘ Higher-lens→Lens l) $
                                                         _≃_.left-inverse-of Lens≃Higher-lens l⁻¹ ⟩∎
    l⁻¹ ∘ Higher-lens→Lens l                          ∎

-- H.Has-quasi-inverse b l implies
-- Has-quasi-inverseᴱ b (Higher-lens→Lens l) (assuming univalence).

Has-quasi-inverse→Has-quasi-inverseᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : H.Lens A B) →
  H.Has-quasi-inverse b l → Has-quasi-inverseᴱ b (Higher-lens→Lens l)
Has-quasi-inverse→Has-quasi-inverseᴱ {a = a} b univ l =
  (∃ λ l⁻¹ →         l  HLC.∘ l⁻¹ ≡ HLC.id b × l⁻¹ HLC.∘ l  ≡ HLC.id b )  ↝⟨ (Σ-map Higher-lens→Lens λ {l⁻¹} (p , q) →
                                                                              [ ∘≡id→∘≡id b univ l l⁻¹ p
                                                                              , ∘≡id→∘≡id b univ l⁻¹ l q
                                                                              ]) ⟩
  (∃ λ l⁻¹ → Erased (l′     ∘ l⁻¹ ≡     id b × l⁻¹     ∘ l′ ≡     id b))  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Has-quasi-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to H.Has-quasi-inverse b l (assuming univalence).

@0 Has-quasi-inverseᴱ≃Has-quasi-inverse :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (l : H.Lens A B) →
  Has-quasi-inverseᴱ b (Higher-lens→Lens l) ≃ H.Has-quasi-inverse b l
Has-quasi-inverseᴱ≃Has-quasi-inverse b univ l =
  (∃ λ l⁻¹ → Erased (l′    ∘ l⁻¹ ≡     id b × l⁻¹     ∘ l′ ≡     id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′    ∘ l⁻¹ ≡     id b × l⁻¹     ∘ l′ ≡     id b )  ↝⟨ (inverse $
                                                                             Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                                             (≡⇒↝ _ (cong₂ _≡_ (l∘l⁻¹≡l∘l⁻¹ univ l l⁻¹)
                                                                                               (Higher-lens-id≡id b univ)) F.∘
                                                                              inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens))
                                                                               ×-cong
                                                                             (≡⇒↝ _ (cong₂ _≡_ (l⁻¹∘l≡l⁻¹∘l univ l⁻¹ l)
                                                                                               (Higher-lens-id≡id b univ)) F.∘
                                                                              inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens))) ⟩□
  (∃ λ l⁻¹ →         l HLC.∘ l⁻¹ ≡ HLC.id b × l⁻¹ HLC.∘ l  ≡ HLC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- H.[ b ] A ≅ B implies [ b ] A ≅ᴱ B (assuming univalence).

≅→≅ᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  H.[ b ] A ≅ B → [ b ] A ≅ᴱ B
≅→≅ᴱ {A = A} {B = B} b univ =
  (∃ λ (l : H.Lens A B) → H.Has-quasi-inverse b l)  ↝⟨ (Σ-map Higher-lens→Lens λ {l} →
                                                        Has-quasi-inverse→Has-quasi-inverseᴱ b univ l) ⟩□
  (∃ λ (l : Lens A B) → Has-quasi-inverseᴱ b l)     □

-- In erased contexts [ b ] A ≅ᴱ B is equivalent to H.[ b ] A ≅ B
-- (assuming univalence).

@0 ≅ᴱ≃≅ :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  ([ b ] A ≅ᴱ B) ≃ (H.[ b ] A ≅ B)
≅ᴱ≃≅ {A = A} {B = B} b univ =
  (∃ λ (l : Lens A B) → Has-quasi-inverseᴱ b l)     ↝⟨ Σ-cong-contra (inverse Lens≃Higher-lens) $
                                                       Has-quasi-inverseᴱ≃Has-quasi-inverse b univ ⟩□
  (∃ λ (l : H.Lens A B) → H.Has-quasi-inverse b l)  □

-- Lenses with quasi-inverses can be converted to equivalences with
-- erased proofs.

≅ᴱ→≃ᴱ : ∀ b → [ b ] A ≅ᴱ B → A ≃ᴱ B
≅ᴱ→≃ᴱ
  ⊠
  (l@(⟨ _ , _ , _ ⟩) , l⁻¹@(⟨ _ , _ , _ ⟩) , [ l∘l⁻¹≡id , l⁻¹∘l≡id ]) =
  EEq.↔→≃ᴱ
    (get l)
    (get l⁻¹)
    (λ b → cong (λ l → get l b) l∘l⁻¹≡id)
    (λ a → cong (λ l → get l a) l⁻¹∘l≡id)
  where
  open Lens

-- There is a logical equivalence between [ b ] A ≅ᴱ B and A ≃ᴱ B
-- (assuming univalence).

≅ᴱ⇔≃ᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  ([ b ] A ≅ᴱ B) ⇔ (A ≃ᴱ B)
≅ᴱ⇔≃ᴱ {A = A} {B = B} b univ = record
  { to   = ≅ᴱ→≃ᴱ b
  ; from = from b
  }
  where
  from : ∀ b → A ≃ᴱ B → [ b ] A ≅ᴱ B
  from b A≃B = l , l⁻¹ , [ l∘l⁻¹≡id b , l⁻¹∘l≡id b ]
    where
    l   = ≃ᴱ→Lens′ A≃B
    l⁻¹ = ≃ᴱ→Lens′ (inverse A≃B)

    @0 l∘l⁻¹≡id : ∀ b → l ∘ l⁻¹ ≡ id b
    l∘l⁻¹≡id ⊠ = _↔_.from (equality-characterisation₁ univ)
      ( (Erased ∥ A ∥ × Erased ∥ B ∥  ↔⟨ inverse Erased-Σ↔Σ ⟩
         Erased (∥ A ∥ × ∥ B ∥)       ↔⟨ Erased-cong (
                                         drop-⊤-left-× λ b →
                                         inhabited⇒∥∥↔⊤ (∥∥-map (_≃ᴱ_.from A≃B) b)) ⟩□
         Erased ∥ B ∥                 □)
      , λ _ → cong₂ _,_
               ([]-cong [ truncation-is-proposition _ _ ])
               (_≃ᴱ_.right-inverse-of A≃B _)
      )

    @0 l⁻¹∘l≡id : ∀ b → l⁻¹ ∘ l ≡ id b
    l⁻¹∘l≡id ⊠ = _↔_.from (equality-characterisation₁ univ)
      ( (Erased ∥ B ∥ × Erased ∥ A ∥  ↔⟨ inverse Erased-Σ↔Σ ⟩
         Erased (∥ B ∥ × ∥ A ∥)       ↔⟨ Erased-cong (
                                         drop-⊤-left-× λ a →
                                         inhabited⇒∥∥↔⊤ (∥∥-map (_≃ᴱ_.to A≃B) a)) ⟩
         Erased ∥ A ∥                 □)
      , λ _ → cong₂ _,_
                ([]-cong [ truncation-is-proposition _ _ ])
                (_≃ᴱ_.left-inverse-of A≃B _)
      )

-- In erased contexts the right-to-left direction of ≅ᴱ⇔≃ᴱ is a right
-- inverse of the left-to-right direction.

@0 ≅ᴱ⇔≃ᴱ∘≅ᴱ⇔≃ᴱ :
  {A B : Set a}
  (b : Block "id")
  (@0 univ : Univalence a)
  (A≃B : A ≃ᴱ B) →
  _⇔_.to (≅ᴱ⇔≃ᴱ b univ) (_⇔_.from (≅ᴱ⇔≃ᴱ b univ) A≃B) ≡ A≃B
≅ᴱ⇔≃ᴱ∘≅ᴱ⇔≃ᴱ ⊠ _ _ = EEq.to≡to→≡ ext (refl _)

-- There is not necessarily a split surjection from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe (assuming univalence).

¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ :
  (b : Block "id") →
  @0 Univalence a →
  ¬ ({A B : Set a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)
¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ {a = a} b univ =
  Stable-¬ _
    [ ({A B : Set a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)    ↝⟨ (λ hyp → lemma hyp) ⟩

      ({A B : Set a}
       (l : H.Lens A B) →
       Is-equivalence (H.Lens.get l) ↠ H.Has-quasi-inverse b l)  ↝⟨ H.¬Is-equivalence-get↠Has-quasi-inverse b univ ⟩□

      ⊥                                                          □
    ]
  where
  @0 lemma : ∀ {A B : Set a} _ (l : H.Lens A B) → _
  lemma hyp l@(H.⟨ _ , _ , _ ⟩) =
    Is-equivalence (Lens.get (Higher-lens→Lens l))   ↝⟨ EEq.Is-equivalence≃Is-equivalenceᴱ ext ⟩
    Is-equivalenceᴱ (Lens.get (Higher-lens→Lens l))  ↝⟨ hyp (Higher-lens→Lens l) ⟩
    Has-quasi-inverseᴱ b (Higher-lens→Lens l)        ↔⟨ Has-quasi-inverseᴱ≃Has-quasi-inverse b univ l ⟩□
    H.Has-quasi-inverse b l                          □

-- There is not necessarily an equivalence with erased proofs from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe (assuming univalence).

¬Is-equivalenceᴱ-get≃ᴱHas-quasi-inverseᴱ :
  (b : Block "id") →
  @0 Univalence a →
  ¬ ({A B : Set a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ b l)
¬Is-equivalenceᴱ-get≃ᴱHas-quasi-inverseᴱ {a = a} b univ =
  Stable-¬ _
    [ ({A B : Set a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ b l)  ↝⟨ (λ hyp l → _≃_.surjection $ EEq.≃ᴱ→≃ $ hyp l) ⟩

      ({A B : Set a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)   ↝⟨ ¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ b univ ⟩□

      ⊥                                                         □
    ]

-- See also ≃ᴱ≃ᴱ≅ᴱ below.

------------------------------------------------------------------------
-- Equivalences expressed using bi-invertibility for lenses

-- A form of equivalence between types, expressed using lenses.

open B public
  renaming (_≊ᴱ_ to [_]_≊ᴱ_)
  using (Has-left-inverseᴱ; Has-right-inverseᴱ; Is-bi-invertibleᴱ)
open BM public using (equality-characterisation-≊ᴱ)

-- H.Has-left-inverse b l implies
-- Has-left-inverseᴱ b (Higher-lens→Lens l) (assuming univalence).

Has-left-inverse→Has-left-inverseᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : H.Lens A B) →
  H.Has-left-inverse b l → Has-left-inverseᴱ b (Higher-lens→Lens l)
Has-left-inverse→Has-left-inverseᴱ b univ l =
  (∃ λ l⁻¹ →         l⁻¹ HLC.∘ l  ≡ HLC.id b )  ↝⟨ (Σ-map Higher-lens→Lens λ {l⁻¹} eq →
                                                    [ ∘≡id→∘≡id b univ l⁻¹ l eq ]) ⟩□
  (∃ λ l⁻¹ → Erased (l⁻¹     ∘ l′ ≡     id b))  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Has-left-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to H.Has-left-inverse b l (assuming univalence).

@0 Has-left-inverseᴱ≃Has-left-inverse :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (l : H.Lens A B) →
  Has-left-inverseᴱ b (Higher-lens→Lens l) ≃ H.Has-left-inverse b l
Has-left-inverseᴱ≃Has-left-inverse b univ l =
  (∃ λ l⁻¹ → Erased (l⁻¹     ∘ l′ ≡     id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l⁻¹     ∘ l′ ≡     id b )  ↝⟨ (inverse $
                                                    Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                    ≡⇒↝ _ (cong₂ _≡_ (l⁻¹∘l≡l⁻¹∘l univ l⁻¹ l)
                                                                     (Higher-lens-id≡id b univ)) F.∘
                                                    inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens)) ⟩□
  (∃ λ l⁻¹ →         l⁻¹ HLC.∘ l  ≡ HLC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- H.Has-right-inverse b l implies
-- Has-right-inverseᴱ b (Higher-lens→Lens l) (assuming univalence).

Has-right-inverse→Has-right-inverseᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : H.Lens A B) →
  H.Has-right-inverse b l → Has-right-inverseᴱ b (Higher-lens→Lens l)
Has-right-inverse→Has-right-inverseᴱ b univ l =
  (∃ λ l⁻¹ →         l  HLC.∘ l⁻¹ ≡ HLC.id b )  ↝⟨ (Σ-map Higher-lens→Lens λ {l⁻¹} eq →
                                                    [ ∘≡id→∘≡id b univ l l⁻¹ eq ]) ⟩□
  (∃ λ l⁻¹ → Erased (l′     ∘ l⁻¹ ≡     id b))  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Has-right-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to H.Has-right-inverse b l (assuming univalence).

@0 Has-right-inverseᴱ≃Has-right-inverse :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (l : H.Lens A B) →
  Has-right-inverseᴱ b (Higher-lens→Lens l) ≃ H.Has-right-inverse b l
Has-right-inverseᴱ≃Has-right-inverse b univ l =
  (∃ λ l⁻¹ → Erased (l′     ∘ l⁻¹ ≡     id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′     ∘ l⁻¹ ≡     id b )  ↝⟨ (inverse $
                                                    Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                    ≡⇒↝ _ (cong₂ _≡_ (l∘l⁻¹≡l∘l⁻¹ univ l l⁻¹)
                                                                     (Higher-lens-id≡id b univ)) F.∘
                                                    inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens)) ⟩□
  (∃ λ l⁻¹ →         l  HLC.∘ l⁻¹ ≡ HLC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- H.Is-bi-invertible b l implies
-- Is-bi-invertibleᴱ b (Higher-lens→Lens l) (assuming univalence).

Is-bi-invertible→Is-bi-invertibleᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : H.Lens A B) →
  H.Is-bi-invertible b l → Is-bi-invertibleᴱ b (Higher-lens→Lens l)
Is-bi-invertible→Is-bi-invertibleᴱ b univ l =
  H.Is-bi-invertible b l                            ↔⟨⟩
  H.Has-left-inverse b l × H.Has-right-inverse b l  ↝⟨ Σ-map (Has-left-inverse→Has-left-inverseᴱ b univ l)
                                                             (Has-right-inverse→Has-right-inverseᴱ b univ l) ⟩
  Has-left-inverseᴱ b l′ × Has-right-inverseᴱ b l′  ↔⟨⟩
  Is-bi-invertibleᴱ b l′                            □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Is-bi-invertibleᴱ b (Higher-lens→Lens l) is
-- equivalent to H.Is-bi-invertible b l (assuming univalence).

@0 Is-bi-invertibleᴱ≃Is-bi-invertible :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (l : H.Lens A B) →
  Is-bi-invertibleᴱ b (Higher-lens→Lens l) ≃ H.Is-bi-invertible b l
Is-bi-invertibleᴱ≃Is-bi-invertible b univ l =
  Is-bi-invertibleᴱ b l′                            ↔⟨⟩
  Has-left-inverseᴱ b l′ × Has-right-inverseᴱ b l′  ↝⟨ Has-left-inverseᴱ≃Has-left-inverse b univ l
                                                         ×-cong
                                                       Has-right-inverseᴱ≃Has-right-inverse b univ l ⟩
  H.Has-left-inverse b l × H.Has-right-inverse b l  ↔⟨⟩
  H.Is-bi-invertible b l                            □
  where
  l′ = Higher-lens→Lens l

-- H.[ b ] A ≊ B implies [ b ] A ≊ᴱ B (assuming univalence).

≊→≊ᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  H.[ b ] A ≊ B → [ b ] A ≊ᴱ B
≊→≊ᴱ {A = A} {B = B} b univ =
  (∃ λ (l : H.Lens A B) → H.Is-bi-invertible b l)  ↝⟨ (Σ-map Higher-lens→Lens λ {l} →
                                                       Is-bi-invertible→Is-bi-invertibleᴱ b univ l) ⟩□
  (∃ λ (l : Lens A B) → Is-bi-invertibleᴱ b l)     □

-- In erased contexts [ b ] A ≊ᴱ B is equivalent to H.[ b ] A ≊ B
-- (assuming univalence).

@0 ≊ᴱ≃≊ :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  ([ b ] A ≊ᴱ B) ≃ (H.[ b ] A ≊ B)
≊ᴱ≃≊ {A = A} {B = B} b univ =
  (∃ λ (l : Lens A B) → Is-bi-invertibleᴱ b l)     ↝⟨ Σ-cong-contra (inverse Lens≃Higher-lens) $
                                                      Is-bi-invertibleᴱ≃Is-bi-invertible b univ ⟩□
  (∃ λ (l : H.Lens A B) → H.Is-bi-invertible b l)  □

-- Lenses with left inverses have propositional remainder types (in
-- erased contexts).

@0 Has-left-inverseᴱ→remainder-propositional :
  (b : Block "id")
  (l : Lens A B) →
  Has-left-inverseᴱ b l →
  Is-proposition (Lens.R l)
Has-left-inverseᴱ→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , [ l⁻¹∘l≡id ]) =
                                $⟨ get≡id→remainder-propositional
                                     (l⁻¹ ∘ l)
                                     (λ a → cong (flip get a) l⁻¹∘l≡id) ⟩
  Is-proposition (R (l⁻¹ ∘ l))  ↔⟨⟩
  Is-proposition (R l × R l⁻¹)  ↝⟨ H-level-×₁ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Lens

-- Lenses with right inverses have propositional remainder types (in
-- erased contexts).

@0 Has-right-inverseᴱ→remainder-propositional :
  (b : Block "id")
  (l : Lens A B) →
  Has-right-inverseᴱ b l →
  Is-proposition (Lens.R l)
Has-right-inverseᴱ→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , [ l∘l⁻¹≡id ]) =
                                $⟨ get≡id→remainder-propositional
                                     (l ∘ l⁻¹)
                                     (λ a → cong (flip get a) l∘l⁻¹≡id) ⟩
  Is-proposition (R (l ∘ l⁻¹))  ↔⟨⟩
  Is-proposition (R l⁻¹ × R l)  ↝⟨ H-level-×₂ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Lens

-- There is an equivalence with erased proofs between A ≃ᴱ B and
-- [ b ] A ≊ᴱ B (assuming univalence).

≃ᴱ≃ᴱ≊ᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (A ≃ᴱ B) ≃ᴱ ([ b ] A ≊ᴱ B)
≃ᴱ≃ᴱ≊ᴱ {A = A} {B = B} b univ =
  EEq.↔→≃ᴱ (to b) (from b) (to∘from b) (from∘to b)
  where
  open Lens

  to : ∀ b → A ≃ᴱ B → [ b ] A ≊ᴱ B
  to b = B.≅ᴱ→≊ᴱ b ⊚ _⇔_.from (≅ᴱ⇔≃ᴱ b univ)

  from : ∀ b → [ b ] A ≊ᴱ B → A ≃ᴱ B
  from b = _⇔_.to (≅ᴱ⇔≃ᴱ b univ) ⊚ _⇔_.from (BM.≅ᴱ⇔≊ᴱ b univ)

  @0 to∘from : ∀ b A≊ᴱB → to b (from b A≊ᴱB) ≡ A≊ᴱB
  to∘from b A≊ᴱB =
    _≃_.from (equality-characterisation-≊ᴱ b univ _ _) $
    _↔_.from (equality-characterisation₂ univ)
      ( ∥B∥≃R  b A≊ᴱB
      , lemma₁ b A≊ᴱB
      , lemma₂ b A≊ᴱB
      )
    where
    l′ : ∀ b (A≊ᴱB : [ b ] A ≊ᴱ B) → Lens A B
    l′ b A≊ᴱB = proj₁ (to b (from b A≊ᴱB))

    ∥B∥≃R : ∀ b (A≊ᴱB@(l , _) : [ b ] A ≊ᴱ B) → Erased ∥ B ∥ ≃ R l
    ∥B∥≃R b (l , (l-inv@(l⁻¹ , _) , _)) = Eq.⇔→≃
      (H-level-Erased 1 truncation-is-proposition)
      R-prop
      (PT.rec R-prop (remainder l ⊚ get l⁻¹) ⊚ erased)
      (λ r → [ inhabited l r ])
      where
      R-prop = Has-left-inverseᴱ→remainder-propositional b l l-inv

    lemma₁ :
      ∀ b (A≊ᴱB@(l , _) : [ b ] A ≊ᴱ B) a →
      _≃_.to (∥B∥≃R b A≊ᴱB) (remainder (l′ b A≊ᴱB) a) ≡ remainder l a
    lemma₁
      ⊠
      ( l@(⟨ _ , _ , _ ⟩)
      , (l⁻¹@(⟨ _ , _ , _ ⟩) , [ l⁻¹∘l≡id ])
      , (⟨ _ , _ , _ ⟩ , _)
      ) a =
      remainder l (get l⁻¹ (get l a))  ≡⟨⟩
      remainder l (get (l⁻¹ ∘ l) a)    ≡⟨ cong (λ l′ → remainder l (get l′ a)) l⁻¹∘l≡id ⟩
      remainder l (get (id ⊠) a)       ≡⟨⟩
      remainder l a                    ∎

    lemma₂ :
      ∀ b (A≊ᴱB@(l , _) : [ b ] A ≊ᴱ B) a →
      get (l′ b A≊ᴱB) a ≡ get l a
    lemma₂ ⊠
      (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) _ =
      refl _

  @0 from∘to :
    ∀ b A≃B →
    _⇔_.to (≅ᴱ⇔≃ᴱ b univ) (_⇔_.from (BM.≅ᴱ⇔≊ᴱ b univ)
      (B.≅ᴱ→≊ᴱ b (_⇔_.from (≅ᴱ⇔≃ᴱ b univ) A≃B))) ≡
    A≃B
  from∘to ⊠ _ = EEq.to≡to→≡ ext (refl _)

-- The right-to-left direction of ≃ᴱ≃ᴱ≊ᴱ maps bi-invertible lenses to
-- their getter functions.

to-from-≃ᴱ≃ᴱ≊ᴱ≡get :
  (b : Block "id")
  (@0 univ : Univalence a)
  (A≊ᴱB@(l , _) : [ b ] A ≊ᴱ B) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ b univ) A≊ᴱB) ≡ Lens.get l
to-from-≃ᴱ≃ᴱ≊ᴱ≡get
  ⊠ _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl _

-- A variant of ≃ᴱ≃ᴱ≊ᴱ that works even if A and B live in different
-- universes.
--
-- This kind of variant came up in a discussion with Andrea Vezzosi.

≃ᴱ≃ᴱ≊ᴱ′ :
  {A : Set a} {B : Set b}
  (b-id : Block "id") →
  @0 Univalence (a ⊔ b) →
  (A ≃ᴱ B) ≃ᴱ ([ b-id ] ↑ b A ≊ᴱ ↑ a B)
≃ᴱ≃ᴱ≊ᴱ′ {a = a} {b = b} {A = A} {B = B} b-id univ =
  A ≃ᴱ B                   ↝⟨ inverse $ EEq.≃ᴱ-cong ext (from-isomorphism Bijection.↑↔)
                                                        (from-isomorphism Bijection.↑↔) ⟩
  ↑ b A ≃ᴱ ↑ a B           ↝⟨ ≃ᴱ≃ᴱ≊ᴱ b-id univ ⟩□
  [ b-id ] ↑ b A ≊ᴱ ↑ a B  □

-- The right-to-left direction of ≃ᴱ≃ᴱ≊ᴱ′ maps bi-invertible lenses to a
-- variant of their getter functions.

to-from-≃ᴱ≃ᴱ≊ᴱ′≡get :
  {A : Set a} {B : Set b}
  (b-id : Block "id")
  (@0 univ : Univalence (a ⊔ b)) →
  (A≊ᴱB@(l , _) : [ b-id ] ↑ b A ≊ᴱ ↑ a B) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ′ b-id univ) A≊ᴱB) ≡
  lower ⊚ Lens.get l ⊚ lift
to-from-≃ᴱ≃ᴱ≊ᴱ′≡get
  ⊠ _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl _

-- The getter function of a bi-invertible lens is an equivalence with
-- erased proofs (assuming univalence).

Is-bi-invertibleᴱ→Is-equivalenceᴱ-get :
  {A : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : Lens A B) →
  Is-bi-invertibleᴱ b l → Is-equivalenceᴱ (Lens.get l)
Is-bi-invertibleᴱ→Is-equivalenceᴱ-get
  b@⊠ univ l@(⟨ _ , _ , _ ⟩)
  is-bi-inv@((⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  _≃ᴱ_.is-equivalence (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ b univ) (l , is-bi-inv))

-- If l is a lens between types in the same universe, then there is an
-- equivalence with erased proofs between "l is bi-invertible (with
-- erased proofs)" and "the getter of l is an equivalence (with erased
-- proofs)" (assuming univalence).

Is-bi-invertible≃Is-equivalence-get :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  (l : Lens A B) →
  Is-bi-invertibleᴱ b l ≃ᴱ Is-equivalenceᴱ (Lens.get l)
Is-bi-invertible≃Is-equivalence-get b univ l = EEq.⇔→≃ᴱ
  (BM.Is-bi-invertibleᴱ-propositional b univ l)
  (EEq.Is-equivalenceᴱ-propositional ext _)
  (Is-bi-invertibleᴱ→Is-equivalenceᴱ-get b univ l)
  (λ is-equiv →

     let l′ = ≃ᴱ→Lens′ EEq.⟨ get l , is-equiv ⟩ in

                             $⟨ proj₂ (_≃ᴱ_.to (≃ᴱ≃ᴱ≊ᴱ b univ) EEq.⟨ _ , is-equiv ⟩) ⟩
     Is-bi-invertibleᴱ b l′  ↝⟨ subst (λ ([ l ]) → Is-bi-invertibleᴱ b l) $ sym $
                                []-cong [ get-equivalence→≡≃ᴱ→Lens′ univ l is-equiv ] ⟩□
     Is-bi-invertibleᴱ b l   □)
  where
  open Lens

-- If A is a set, then there is an equivalence with erased proofs
-- between [ b ] A ≊ᴱ B and [ b ] A ≅ᴱ B (assuming univalence).

≊ᴱ≃ᴱ≅ᴱ :
  {A B : Set a}
  (b : Block "id") →
  @0 Univalence a →
  @0 Is-set A →
  ([ b ] A ≊ᴱ B) ≃ᴱ ([ b ] A ≅ᴱ B)
≊ᴱ≃ᴱ≅ᴱ b univ A-set =
  ∃-cong λ _ →
    BM.Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-domain
      b univ
      (Is-set-closed-domain univ A-set)

-- If A is a set, then there is an equivalence with erased proofs between A ≃ᴱ B and
-- [ b ] A ≅ᴱ B (assuming univalence).

≃ᴱ≃ᴱ≅ᴱ :
  {A B : Set a}
  (b : Block "≃ᴱ≃ᴱ≅ᴱ") →
  @0 Univalence a →
  @0 Is-set A →
  (A ≃ᴱ B) ≃ᴱ ([ b ] A ≅ᴱ B)
≃ᴱ≃ᴱ≅ᴱ {A = A} {B = B} b@⊠ univ A-set =
  A ≃ᴱ B        ↝⟨ ≃ᴱ≃ᴱ≊ᴱ b univ ⟩
  [ b ] A ≊ᴱ B  ↝⟨ ≊ᴱ≃ᴱ≅ᴱ b univ A-set ⟩□
  [ b ] A ≅ᴱ B  □

-- In erased contexts one can prove that ≃ᴱ≃ᴱ≅ᴱ maps identity to
-- identity.

@0 ≃ᴱ≃ᴱ≅ᴱ-id≡id :
  {A : Set a}
  (b : Block "≃ᴱ≃ᴱ≅ᴱ")
  (univ : Univalence a)
  (A-set : Is-set A) →
  proj₁ (_≃ᴱ_.to (≃ᴱ≃ᴱ≅ᴱ b univ A-set) F.id) ≡ id b
≃ᴱ≃ᴱ≅ᴱ-id≡id ⊠ univ _ =
  _↔_.from (equality-characterisation₁ univ)
    (F.id , λ _ → refl _)

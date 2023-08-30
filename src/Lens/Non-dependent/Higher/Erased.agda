------------------------------------------------------------------------
-- Higher lenses with erased proofs
------------------------------------------------------------------------

import Equality.Path as P

module Lens.Non-dependent.Higher.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Bi-invertibility.Erased
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bijection using (_↔_)
import Bool equality-with-J as Bool
open import Circle eq using (𝕊¹)
open import Circle.Erased eq as CE using (𝕊¹ᴱ)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
  using () renaming (opaque-univ to univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages equality-with-J
  as ECP using (Contractibleᴱ; _⁻¹ᴱ_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT
open import H-level.Truncation.Propositional.Erased eq as TE
  using (∥_∥ᴱ)
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)
import Lens.Non-dependent.Equivalent-preimages eq as EP
import Lens.Non-dependent.Higher eq as H
import Lens.Non-dependent.Higher.Combinators eq as HC
import Lens.Non-dependent.Traditional eq as T
import Lens.Non-dependent.Traditional.Erased eq as Traditionalᴱ

private
  variable
    a b c d p r       : Level
    A A₁ A₂ B B₁ B₂ C : Type a
    P                 : A → Type p
    x x′ y y′         : A
    n                 : ℕ

------------------------------------------------------------------------
-- Higher lenses

private

 module Temporarily-private where

  -- Higher lenses with erased "proofs".

  record Lens (A : Type a) (B : Type b) : Type (lsuc (a ⊔ b)) where
    constructor ⟨_,_,_⟩
    pattern
    no-eta-equality
    field
      -- Remainder type.
      R : Type (a ⊔ b)

      -- Equivalence (with erased proofs).
      equiv : A ≃ᴱ (R × B)

      -- The proof of (mere) inhabitance.
      @0 inhabited : R → ∥ B ∥

open Temporarily-private public hiding (module Lens)

-- An η-law for lenses.

η :
  (l : Lens A B)
  (open Temporarily-private.Lens l) →
  ⟨ R , equiv , inhabited ⟩ ≡ l
η ⟨ _ , _ , _ ⟩ = refl _

-- Lens can be expressed as a nested Σ-type.

Lens-as-Σ :
  {A : Type a} {B : Type b} →
  Lens A B ≃
  ∃ λ (R : Type (a ⊔ b)) →
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
  η
  where
  open Temporarily-private.Lens

-- An equality rearrangement lemma.

left-inverse-of-Lens-as-Σ :
  (l : Lens A B) →
  _≃_.left-inverse-of Lens-as-Σ l ≡ η l
left-inverse-of-Lens-as-Σ l@(⟨ _ , _ , _ ⟩) =
  _≃_.left-inverse-of Lens-as-Σ l                          ≡⟨⟩

  _≃_.left-inverse-of Lens-as-Σ
    (_≃_.from Lens-as-Σ (_≃_.to Lens-as-Σ l))              ≡⟨ sym $ _≃_.right-left-lemma Lens-as-Σ _ ⟩

  cong (_≃_.from Lens-as-Σ)
    (_≃_.right-inverse-of Lens-as-Σ (_≃_.to Lens-as-Σ l))  ≡⟨⟩

  cong (_≃_.from Lens-as-Σ) (refl _)                       ≡⟨ cong-refl _ ⟩∎

  refl _                                                   ∎

-- Lenses without erased proofs can be turned into lenses with erased
-- proofs (in erased contexts).

@0 Higher-lens→Lens : H.Lens A B → Lens A B
Higher-lens→Lens {A = A} {B = B} l@(H.⟨ _ , _ , _ ⟩) =      $⟨ l ⟩
  H.Lens A B                                                ↔⟨ H.Lens-as-Σ ⟩
  (∃ λ (R : Type _) → (A ≃ (R × B)) × (R → ∥ B ∥))          ↝⟨ Σ-map P.id (Σ-map EEq.≃→≃ᴱ [_]→) ⟩
  (∃ λ (R : Type _) → (A ≃ᴱ (R × B)) × Erased (R → ∥ B ∥))  ↔⟨ inverse Lens-as-Σ ⟩□
  Lens A B                                                  □

-- In erased contexts Lens A B is equivalent to H.Lens A B.

@0 Lens≃Higher-lens : Lens A B ≃ H.Lens A B
Lens≃Higher-lens {A = A} {B = B} =
  Eq.with-other-inverse
    (Lens A B                                                  ↝⟨ Lens-as-Σ ⟩
     (∃ λ (R : Type _) → (A ≃ᴱ (R × B)) × Erased (R → ∥ B ∥))  ↝⟨ (∃-cong λ _ →
                                                                   inverse EEq.≃≃≃ᴱ ×-cong Eq.↔⇒≃ (erased Erased↔)) ⟩
     (∃ λ (R : Type _) → (A ≃ (R × B)) × (R → ∥ B ∥))          ↔⟨ inverse H.Lens-as-Σ ⟩□
     H.Lens A B                                                □)
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
  {A : Type a} {B : Type b} {R : Type (a ⊔ b)} →
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
  {A : Type a} {B : Type b} →
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
  {A B : Type a} →
  A ≃ᴱ B → Lens A B
≃ᴱ→Lens′ {a = a} {A = A} {B = B} A≃B = record
  { R         = Erased ∥ B ∥
  ; equiv     = A                 ↝⟨ A≃B ⟩
                B                 ↔⟨ inverse Erased-∥∥×≃ ⟩□
                Erased ∥ B ∥ × B  □
  ; inhabited = erased
  }

------------------------------------------------------------------------
-- Some example lenses

-- A lens for the first projection.

fst :
  {A : Type a} {B : Type b} →
  Lens (A × B) A
fst {a = a} {A = A} {B = B} =
  ≃ᴱ×→Lens
    (A × B      ↔⟨ ×-comm ⟩
     B × A      ↔⟨ inverse Bijection.↑↔ ×-cong F.id ⟩□
     ↑ a B × A  □)

_ : Lens.get fst (x , y) ≡ x
_ = refl _

_ : Lens.set fst (x , y) x′ ≡ (x′ , y)
_ = refl _

-- A lens for the second projection.

snd :
  {A : Type a} {B : Type b} →
  Lens (A × B) B
snd {b = b} {A = A} {B = B} =
  ≃ᴱ×→Lens
    (A × B      ↔⟨ inverse Bijection.↑↔ ×-cong F.id ⟩□
     ↑ b A × B  □)

_ : Lens.get snd (x , y) ≡ y
_ = refl _

_ : Lens.set snd (x , y) y′ ≡ (x , y′)
_ = refl _

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
  {l₁ l₂ : Lens A B} →
  let open Lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
          _≃ᴱ_.to (equiv l₂) x
equality-characterisation₁ {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                             ↔⟨ inverse $ Eq.≃-≡ Lens≃Higher-lens ⟩

  high l₁ ≡ high l₂                                   ↝⟨ H.equality-characterisation₁ ⊠ univ ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃ᴱ_.to (equiv l₂) x)                      □
  where
  open Lens

-- And another one.

@0 equality-characterisation₂ :
  {l₁ l₂ : Lens A B} →
  let open Lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                 ↔⟨ inverse $ Eq.≃-≡ Lens≃Higher-lens ⟩

  high l₁ ≡ high l₂                                       ↝⟨ H.equality-characterisation₂ ⊠ univ ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
       ×
     (∀ x → get l₁ x ≡ get l₂ x))                         □
  where
  open Lens

-- And a final one.

@0 equality-characterisation₃ :
  {l₁ l₂ : Lens A B} →
  let open Lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃ᴱ_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃ᴱ_.from (equiv l₂) p
equality-characterisation₃ {l₁ = l₁} {l₂} =
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
  (l₁ l₂ : Lens A B)
  (f : R l₁ → R l₂) →
  (B → ∀ r →
   ∃ λ b′ → remainder l₂ (_≃ᴱ_.from (equiv l₁) (r , b′)) ≡ f r) →
  (∀ a → f (remainder l₁ a) ≡ remainder l₂ a) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal′
  l₁ l₂ f ∃≡f f-remainder≡remainder setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal′
                          univ (high l₁) (high l₂) f ∃≡f
                          f-remainder≡remainder setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- If the codomain of a lens is inhabited when it is merely inhabited
-- and the remainder type is inhabited, then this lens is equal to
-- another lens if their setters are equal (in erased contexts).

@0 lenses-equal-if-setters-equal :
  (l₁ l₂ : Lens A B) →
  (Lens.R l₁ → ∥ B ∥ → B) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal l₁ l₂ inh′ setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal
                          univ (high l₁) (high l₂) inh′ setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- If a lens has a propositional remainder type, then this lens is
-- equal to another lens if their setters are equal (in erased
-- contexts).

@0 lenses-equal-if-setters-equal-and-remainder-propositional :
  (l₁ l₂ : Lens A B) →
  Is-proposition (Lens.R l₂) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal-and-remainder-propositional
  l₁ l₂ R₂-prop setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal-and-remainder-propositional
                          univ (high l₁) (high l₂) R₂-prop setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- A generalisation of the previous result: If a lens has a remainder
-- type that is a set, then this lens is equal to another lens if
-- their setters are equal.
--
-- The corresponding result in Lens.Non-dependent.Higher is due to
-- Andrea Vezzosi.

@0 lenses-equal-if-setters-equal-and-remainder-set :
  (l₁ l₂ : Lens A B) →
  Is-set (Lens.R l₂) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal-and-remainder-set
  l₁ l₂ R₂-prop setters-equal =
                     $⟨ H.lenses-equal-if-setters-equal-and-remainder-set
                          univ (high l₁) (high l₂) R₂-prop setters-equal ⟩
  high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
  l₁ ≡ l₂            □

-- The functions ≃ᴱ→Lens and ≃ᴱ→Lens′ are pointwise equal (when
-- applicable, in erased contexts).

@0 ≃ᴱ→Lens≡≃ᴱ→Lens′ :
  {A B : Type a} →
  (A≃B : A ≃ᴱ B) → ≃ᴱ→Lens A≃B ≡ ≃ᴱ→Lens′ A≃B
≃ᴱ→Lens≡≃ᴱ→Lens′ {B = B} A≃B =
  _↔_.from equality-characterisation₂
    ( (Erased ∥ ↑ _ B ∥  ↔⟨ Erased-cong (∥∥-cong Bijection.↑↔) ⟩□
       Erased ∥ B ∥      □)
    , (λ _ → refl _)
    , (λ _ → refl _)
    )

-- If the getter of a lens is an equivalence with erased proofs, then
-- the lens formed using the equivalence (using ≃ᴱ→Lens) is equal to
-- the lens (in erased contexts).

@0 get-equivalence→≡≃ᴱ→Lens :
  {A : Type a} {B : Type b} →
  (l : Lens A B) →
  (eq : Is-equivalenceᴱ (Lens.get l)) →
  l ≡ ≃ᴱ→Lens EEq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃ᴱ→Lens {A = A} {B = B} l eq =
  lenses-equal-if-setters-equal-and-remainder-propositional
    l (≃ᴱ→Lens EEq.⟨ Lens.get l , eq ⟩)
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
  {A B : Type a} →
  (l : Lens A B) →
  (eq : Is-equivalenceᴱ (Lens.get l)) →
  l ≡ ≃ᴱ→Lens′ EEq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃ᴱ→Lens′ {A = A} {B = B} l eq =
  l             ≡⟨ get-equivalence→≡≃ᴱ→Lens l eq ⟩
  ≃ᴱ→Lens A≃B   ≡⟨ ≃ᴱ→Lens≡≃ᴱ→Lens′ A≃B ⟩∎
  ≃ᴱ→Lens′ A≃B  ∎
  where
  A≃B = EEq.⟨ Lens.get l , eq ⟩

------------------------------------------------------------------------
-- Some equivalences

-- "The getter is an equivalence" is equivalent to "the remainder type
-- is equivalent to the propositional truncation of the codomain" (in
-- erased contexts).

@0 get-equivalence≃inhabited-equivalence :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) ≃ Is-equivalence (Lens.inhabited l)
get-equivalence≃inhabited-equivalence l =
  H.get-equivalence≃inhabited-equivalence (high l)

-- "The getter is an equivalence" is equivalent to "the remainder type
-- is equivalent to the propositional truncation of the codomain" (in
-- erased contexts).

@0 get-equivalence≃remainder≃∥codomain∥ :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) ≃ (Lens.R l ≃ ∥ B ∥)
get-equivalence≃remainder≃∥codomain∥ l =
  H.get-equivalence≃remainder≃∥codomain∥ (high l)

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Lens preserves equivalences with erased
-- proofs.

Lens-cong′ :
  A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ →
  (∃ λ (R : Type r) → A₁ ≃ᴱ (R × B₁) × Erased (R → ∥ B₁ ∥)) ≃ᴱ
  (∃ λ (R : Type r) → A₂ ≃ᴱ (R × B₂) × Erased (R → ∥ B₂ ∥))
Lens-cong′ A₁≃A₂ B₁≃B₂ =
  ∃-cong λ _ →
  EEq.≃ᴱ-cong ext A₁≃A₂ (F.id ×-cong B₁≃B₂)
    ×-cong
  Erased-cong (→-cong [ ext ] F.id (∥∥-cong B₁≃B₂))

-- Lens preserves level-preserving equivalences with erased proofs.

Lens-cong :
  {A₁ A₂ : Type a} {B₁ B₂ : Type b} →
  A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ →
  Lens A₁ B₁ ≃ᴱ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁≃A₂ B₁≃B₂ =
  Lens A₁ B₁                                      ↔⟨ Lens-as-Σ ⟩
  (∃ λ R → A₁ ≃ᴱ (R × B₁) × Erased (R → ∥ B₁ ∥))  ↝⟨ Lens-cong′ A₁≃A₂ B₁≃B₂ ⟩
  (∃ λ R → A₂ ≃ᴱ (R × B₂) × Erased (R → ∥ B₂ ∥))  ↔⟨ inverse Lens-as-Σ ⟩□
  Lens A₂ B₂                                      □

-- If B is a proposition (when A is inhabited), then Lens A B is
-- equivalent (with erased proofs) to A → B.

lens-to-proposition≃ᴱget :
  {A : Type a} {B : Type b} →
  @0 (A → Is-proposition B) →
  Lens A B ≃ᴱ (A → B)
lens-to-proposition≃ᴱget {b = b} {A = A} {B = B} prop = EEq.↔→≃ᴱ
  get
  from
  refl
  (λ l →
     let lemma =
           ↑ b A    ↔⟨ Bijection.↑↔ ⟩
           A        ↝⟨ EEq.≃ᴱ→≃ (equiv l) ⟩
           R l × B  ↝⟨ (EEq.≃ᴱ→≃ $ drop-⊤-right λ r → _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
                        PT.rec
                          (ECP.Contractibleᴱ-propositional ext)
                          (λ b → ECP.inhabited→Is-proposition→Contractibleᴱ
                                   b
                                   (prop (_≃ᴱ_.from (equiv l) (r , b))))
                          (inhabited l r)) ⟩□
           R l      □
     in
     _↔_.from equality-characterisation₁
        (lemma , λ _ → refl _))
  where
  open Lens

  from = λ get → record
    { R         = ↑ b A
    ; equiv     = A          ↔⟨ inverse Bijection.↑↔ ⟩
                  ↑ b A      ↝⟨ (inverse $ drop-⊤-right λ (lift a) →
                                 EEq.inhabited→Is-proposition→≃ᴱ⊤ (get a) (prop a)) ⟩□
                  ↑ b A × B  □
    ; inhabited = ∣_∣ ⊚ get ⊚ lower
    }

_ :
  (@0 prop : A → Is-proposition B)
  (l : Lens A B) →
  _≃ᴱ_.to (lens-to-proposition≃ᴱget prop) l ≡ Lens.get l
_ = λ _ _ → refl _

-- If B is contractible (with an erased proof, assuming that A is
-- inhabited), then Lens A B is equivalent (with erased proofs) to ⊤.

lens-to-contractible≃ᴱ⊤ :
  (A → Contractibleᴱ B) →
  Lens A B ≃ᴱ ⊤
lens-to-contractible≃ᴱ⊤ {A = A} {B = B} cB =
  Lens A B  ↝⟨ lens-to-proposition≃ᴱget (λ a → mono₁ 0 (ECP.Contractibleᴱ→Contractible (cB a))) ⟩
  (A → B)   ↝⟨ ∀-cong [ ext ] (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ ⊚ cB) ⟩
  (A → ⊤)   ↔⟨ →-right-zero ⟩□
  ⊤         □

-- Lens A ⊥ is equivalent (with erased proofs) to ¬ A.

lens-to-⊥≃ᴱ¬ : Lens A (⊥ {ℓ = b}) ≃ᴱ (¬ A)
lens-to-⊥≃ᴱ¬ {A = A} =
  Lens A ⊥  ↝⟨ lens-to-proposition≃ᴱget (λ _ → ⊥-propositional) ⟩
  (A → ⊥)   ↝⟨ inverse $ ¬↔→⊥ [ ext ] ⟩□
  ¬ A       □

-- If A is contractible (with an erased proof), then Lens A B is
-- equivalent (with erased proofs) to Contractibleᴱ B.

lens-from-contractible≃ᴱcodomain-contractible :
  Contractibleᴱ A →
  Lens A B ≃ᴱ Contractibleᴱ B
lens-from-contractible≃ᴱcodomain-contractible {A = A} {B = B} cA =
  Lens A B                                                            ↔⟨ Lens-as-Σ ⟩
  (∃ λ R → A ≃ᴱ (R × B) × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ →
                                                                          EEq.≃ᴱ-cong ext (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ cA) F.id) ⟩
  (∃ λ R → ⊤ ≃ᴱ (R × B) × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → EEq.inverse-equivalence ext) ⟩
  (∃ λ R → (R × B) ≃ᴱ ⊤ × Erased (R → ∥ B ∥))                         ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → inverse $ EEq.Contractibleᴱ≃ᴱ≃ᴱ⊤ ext) ⟩
  (∃ λ R → Contractibleᴱ (R × B) × Erased (R → ∥ B ∥))                ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → EEq.Contractibleᴱ-commutes-with-× ext) ⟩
  (∃ λ R → (Contractibleᴱ R × Contractibleᴱ B) × Erased (R → ∥ B ∥))  ↔⟨ (∃-cong λ _ → inverse ×-assoc) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased (R → ∥ B ∥))    ↝⟨ (∃-cong λ _ → ∃-cong λ cR → ∃-cong λ _ → Erased-cong (
                                                                          →-cong [ ext ] (_⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ cR) F.id)) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased (⊤ → ∥ B ∥))    ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → Erased-cong Π-left-identity) ⟩
  (∃ λ R → Contractibleᴱ R × Contractibleᴱ B × Erased ∥ B ∥)          ↔⟨ (∃-cong λ _ → ×-comm) ⟩
  (∃ λ R → (Contractibleᴱ B × Erased ∥ B ∥) × Contractibleᴱ R)        ↔⟨ ∃-comm ⟩
  (Contractibleᴱ B × Erased ∥ B ∥) × (∃ λ R → Contractibleᴱ R)        ↝⟨ (drop-⊤-right λ _ → EEq.∃Contractibleᴱ≃ᴱ⊤ ext univ) ⟩
  Contractibleᴱ B × Erased ∥ B ∥                                      ↔⟨ (∃-cong λ cB → Erased-cong (inhabited⇒∥∥↔⊤ ∣ proj₁ cB ∣)) ⟩
  Contractibleᴱ B × Erased ⊤                                          ↔⟨ (drop-⊤-right λ _ → Erased-⊤↔⊤) ⟩□
  Contractibleᴱ B                                                     □

-- Lens ⊥ B is equivalent (with erased proofs) to the unit type.

lens-from-⊥↔⊤ : Lens (⊥ {ℓ = a}) B ≃ᴱ ⊤
lens-from-⊥↔⊤ {B = B} =
  _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
      ≃ᴱ×→Lens
        (⊥      ↔⟨ inverse ×-left-zero ⟩□
         ⊥ × B  □)
    , [ (λ l → _↔_.from equality-characterisation₁
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
-- ∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l).
--
-- See also ≃≃≊ below.

≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get :
  (A ≃ᴱ B) ≃ᴱ (∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l))
≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get = EEq.↔→≃ᴱ
  (λ A≃B → ≃ᴱ→Lens A≃B , _≃ᴱ_.is-equivalence A≃B)
  (λ (l , eq) → EEq.⟨ Lens.get l , eq ⟩)
  (λ (l , eq) → Σ-≡,≡→≡
     (sym $ get-equivalence→≡≃ᴱ→Lens l eq)
     (EEq.Is-equivalenceᴱ-propositional ext _ _ _))
  (λ _ → EEq.to≡to→≡ ext (refl _))

-- The right-to-left direction of ≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get
-- returns the lens's getter (and some proof).

to-from-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get≡get :
  (p@(l , _) : ∃ λ (l : Lens A B) → Is-equivalenceᴱ (Lens.get l)) →
  _≃ᴱ_.to (_≃ᴱ_.from ≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get p) ≡
  Lens.get l
to-from-≃ᴱ-≃ᴱ-Σ-Lens-Is-equivalenceᴱ-get≡get _ = refl _

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- In general there is no split surjection from Lens A B to
-- Traditionalᴱ.Lens A B.

¬Lens↠Traditional-lens : ¬ (Lens 𝕊¹ᴱ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ᴱ ⊤)
¬Lens↠Traditional-lens =
  Stable-¬
    [ (Lens 𝕊¹ᴱ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ᴱ ⊤)  ↔⟨ ≡⇒≃ $ cong (λ A → Lens A ⊤ ↠ Traditionalᴱ.Lens A ⊤) $ ≃⇒≡ univ $ inverse
                                                 CE.𝕊¹≃𝕊¹ᴱ ⟩
      (Lens 𝕊¹ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ ⊤)    ↝⟨ (λ f → from-equivalence Traditionalᴱ.Lens≃Traditional-lens F.∘
                                                        f F.∘
                                                        from-equivalence (inverse Lens≃Higher-lens)) ⟩
      (H.Lens 𝕊¹ ⊤ ↠ T.Lens 𝕊¹ ⊤)             ↝⟨ H.¬Lens↠Traditional-lens univ ⟩□
      ⊥                                       □
    ]

-- In general there is no equivalence with erased proofs between
-- Lens A B and Traditionalᴱ.Lens A B.

¬Lens≃ᴱTraditional-lens : ¬ (Lens 𝕊¹ᴱ ⊤ ≃ᴱ Traditionalᴱ.Lens 𝕊¹ᴱ ⊤)
¬Lens≃ᴱTraditional-lens =
  Stable-¬
    [ (Lens 𝕊¹ᴱ ⊤ ≃ᴱ Traditionalᴱ.Lens 𝕊¹ᴱ ⊤)  ↝⟨ from-equivalence ⊚ EEq.≃ᴱ→≃ ⟩
      (Lens 𝕊¹ᴱ ⊤ ↠ Traditionalᴱ.Lens 𝕊¹ᴱ ⊤)   ↝⟨ ¬Lens↠Traditional-lens ⟩□
      ⊥                                        □
    ]

-- Some lemmas used in Lens↠Traditional-lens and
-- Lens≃ᴱTraditional-lens below.

private

  module Lens≃ᴱTraditional-lens
    {A : Type a} {B : Type b}
    (@0 A-set : Is-set A)
    where

    from : Block "conversion" → Traditionalᴱ.Lens A B → Lens A B
    from ⊠ l = ≃ᴱ×→Lens
      (A                                       ↝⟨ Traditionalᴱ.≃ᴱΣ∥set⁻¹ᴱ∥ᴱ× A-set l ⟩□
       (∃ λ (f : B → A) → ∥ set ⁻¹ᴱ f ∥ᴱ) × B  □)
      where
      open Traditionalᴱ.Lens l

    to∘from : ∀ bc l → Lens.traditional-lens (from bc l) ≡ l
    to∘from ⊠ l = Traditionalᴱ.equal-laws→≡
      (λ a _ → B-set a _ _)
      (λ _ → A-set _ _)
      (λ _ _ _ → A-set _ _)
      where
      open Traditionalᴱ.Lens l

      @0 B-set : A → Is-set B
      B-set a =
        Traditionalᴱ.h-level-respects-lens-from-inhabited 2 l a A-set

    @0 from∘to :
      ∀ bc l → from bc (Lens.traditional-lens l) ≡ l
    from∘to ⊠ l′ =
      _↔_.from equality-characterisation₃
        ( ((∃ λ (f : B → A) → ∥ set ⁻¹ᴱ f ∥ᴱ) × Erased ∥ B ∥  ↔⟨ (∃-cong λ _ → PT.∥∥ᴱ≃∥∥) ×-cong from-bijection (erased Erased↔) ⟩
           (∃ λ (f : B → A) → ∥ set ⁻¹ᴱ f ∥) × ∥ B ∥          ↝⟨ (×-cong₁ lemma₃) ⟩
           (∥ B ∥ → R) × ∥ B ∥                                ↝⟨ lemma₂ ⟩□
           R                                                  □)
        , λ p →
            _≃ᴱ_.from l (subst (λ _ → R) (refl _) (proj₁ p) , proj₂ p)  ≡⟨ cong (λ r → _≃ᴱ_.from l (r , proj₂ p)) $ subst-refl _ _ ⟩∎
            _≃ᴱ_.from l p                                               ∎
        )
      where
      open Lens l′ renaming (equiv to l)

      B-set : A → Is-set B
      B-set a =
        Traditionalᴱ.h-level-respects-lens-from-inhabited
          2
          (Lens.traditional-lens l′)
          a
          A-set

      R-set : Is-set R
      R-set =
        [inhabited⇒+]⇒+ 1 λ r →
        PT.rec
          (H-level-propositional ext 2)
          (λ b → proj₁-closure (const b) 2 $
                 H-level.respects-surjection
                   (_≃_.surjection (EEq.≃ᴱ→≃ l)) 2 A-set)
          (inhabited r)

      lemma₁ :
        ∥ B ∥ →
        (f : B → A) →
        ∥ set ⁻¹ᴱ f ∥ ≃ (∀ b b′ → set (f b) b′ ≡ f b′)
      lemma₁ ∥b∥ f = Eq.⇔→≃
        truncation-is-proposition
        prop
        (PT.rec prop λ (a , [ set-a≡f ]) b b′ →
         set (f b) b′      ≡⟨ cong (λ f → set (f b) b′) $ sym set-a≡f ⟩
         set (set a b) b′  ≡⟨ set-set _ _ _ ⟩
         set a b′          ≡⟨ cong (_$ b′) set-a≡f ⟩∎
         f b′              ∎)
        (λ hyp →
           flip ∥∥-map ∥b∥ λ b →
           f b , [ ⟨ext⟩ (hyp b) ])
        where
        prop =
          Π-closure ext 1 λ _ →
          Π-closure ext 1 λ _ →
          A-set

      lemma₂ : ((∥ B ∥ → R) × ∥ B ∥) ≃ R
      lemma₂ = Eq.↔→≃
        (λ (f , ∥b∥) → f ∥b∥)
        (λ r → (λ _ → r) , inhabited r)
        refl
        (λ (f , ∥b∥) → cong₂ _,_
           (⟨ext⟩ λ ∥b∥′ →
              f ∥b∥   ≡⟨ cong f (truncation-is-proposition _ _) ⟩∎
              f ∥b∥′  ∎)
           (truncation-is-proposition _ _))

      lemma₃ = λ ∥b∥ →
        (∃ λ (f : B → A) → ∥ set ⁻¹ᴱ f ∥)                                   ↝⟨ ∃-cong (lemma₁ ∥b∥) ⟩

        (∃ λ (f : B → A) → ∀ b b′ → set (f b) b′ ≡ f b′)                    ↝⟨ (Σ-cong (→-cong ext F.id (EEq.≃ᴱ→≃ l)) λ f →
                                                                                ∀-cong ext λ b → ∀-cong ext λ b′ →
                                                                                ≡⇒↝ _ $ cong (_≃ᴱ_.from l (proj₁ (_≃ᴱ_.to l (f b)) , b′) ≡_) $ sym $
                                                                                _≃ᴱ_.left-inverse-of l _) ⟩
        (∃ λ (f : B → R × B) →
           ∀ b b′ → _≃ᴱ_.from l (proj₁ (f b) , b′) ≡ _≃ᴱ_.from l (f b′))    ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                                Eq.≃-≡ (inverse (EEq.≃ᴱ→≃ l))) ⟩

        (∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)          ↔⟨ (Σ-cong ΠΣ-comm λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                                inverse $ ≡×≡↔≡) ⟩
        (∃ λ ((f , g) : (B → R) × (B → B)) →
           ∀ b b′ → f b ≡ f b′ × b′ ≡ g b′)                                 ↔⟨ (Σ-assoc F.∘
                                                                                (∃-cong λ _ →
                                                                                 ∃-comm F.∘
                                                                                 ∃-cong λ _ →
                                                                                 ΠΣ-comm F.∘
                                                                                 ∀-cong ext λ _ →
                                                                                 ΠΣ-comm) F.∘
                                                                                inverse Σ-assoc) ⟩
        ((∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → B → ∀ b → b ≡ g b))                             ↔⟨ (∃-cong $ uncurry λ f _ → ∃-cong λ _ → inverse $
                                                                                →-intro ext (λ b → B-set (_≃ᴱ_.from l (f b , b)))) ⟩
        ((∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → ∀ b → b ≡ g b))                                 ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                                Eq.extensionality-isomorphism ext) ⟩

        ((∃ λ (f : B → R) → Constant f) × (∃ λ (g : B → B) → P.id ≡ g))     ↔⟨ (drop-⊤-right λ _ →
                                                                                _⇔_.to contractible⇔↔⊤ $
                                                                                other-singleton-contractible _) ⟩

        (∃ λ (f : B → R) → Constant f)                                      ↝⟨ constant-function≃∥inhabited∥⇒inhabited R-set ⟩□

        (∥ B ∥ → R)                                                         □

    equiv :
      Block "conversion" →
      Lens A B ≃ᴱ Traditionalᴱ.Lens A B
    equiv bc = EEq.↔→≃ᴱ
      _
      (from bc)
      (to∘from bc)
      (from∘to bc)

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
  {A : Type a}
  (b : Block "conversion")
  (@0 s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_↠_.logical-equivalence (Lens↠Traditional-lens b s))
Lens↠Traditional-lens-preserves-getters-and-setters ⊠ _ =
  (λ _ → refl _ , refl _) , (λ _ → refl _ , refl _)

-- If the domain A is a set, then there is an equivalence with erased
-- proofs between Traditionalᴱ.Lens A B and Lens A B.

Lens≃ᴱTraditional-lens :
  Block "conversion" →
  @0 Is-set A →
  Lens A B ≃ᴱ Traditionalᴱ.Lens A B
Lens≃ᴱTraditional-lens bc A-set =
  Lens≃ᴱTraditional-lens.equiv A-set bc

-- The equivalence preserves getters and setters.

Lens≃ᴱTraditional-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bc : Block "conversion")
  (@0 s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_≃ᴱ_.logical-equivalence (Lens≃ᴱTraditional-lens bc s))
Lens≃ᴱTraditional-lens-preserves-getters-and-setters bc =
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
    (A               ↝⟨ Traditionalᴱ.≃ᴱget⁻¹ᴱ× B-set b₀ l ⟩□
     get ⁻¹ᴱ b₀ × B  □)
    where
    open Traditionalᴱ.Lens l

-- The logical equivalence preserves getters and setters (in an erased
-- context).

@0 Lens⇔Traditional-lens-preserves-getters-and-setters :
  {B : Type b}
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

-- This is not necessarily true for arbitrary domains.

¬-h-level-respects-lens :
  ¬ (∀ n → Lens ⊥₀ Bool → H-level n ⊥₀ → H-level n Bool)
¬-h-level-respects-lens =
  Stable-¬
    [ (∀ n → Lens ⊥ Bool → H-level n ⊥ → H-level n Bool)    ↝⟨ (λ hyp n l → hyp n (Higher-lens→Lens l)) ⟩
      (∀ n → H.Lens ⊥ Bool → H-level n ⊥ → H-level n Bool)  ↝⟨ H.¬-h-level-respects-lens univ ⟩□
      ⊥                                                     □
    ]

-- In fact, there is a lens with a proposition as its domain and a
-- non-set as its codomain.

lens-from-proposition-to-non-set :
  ∃ λ (A : Type a) → ∃ λ (B : Type b) →
  Lens A B × Is-proposition A × ¬ Is-set B
lens-from-proposition-to-non-set {a = a} {b = b} =
    ⊥
  , ↑ b 𝕊¹ᴱ
  , record
      { R         = ⊥
      ; equiv     = ⊥            ↔⟨ inverse ×-left-zero ⟩□
                    ⊥ × ↑ _ 𝕊¹ᴱ  □
      ; inhabited = ⊥-elim
      }
  , ⊥-propositional
  , Stable-¬
      [ Is-set (↑ b 𝕊¹ᴱ)  ↝⟨ H-level-cong _ 2 Bijection.↑↔ ⟩
        Is-set 𝕊¹ᴱ        ↝⟨ CE.¬-𝕊¹ᴱ-set ⟩□
        ⊥                 □
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
  Contractibleᴱ A                    ↝⟨ ECP.Contractibleᴱ-respects-surjection
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
-- contractibility of Lens A B.

¬-Contractible-closed-domain :
  ∀ {a b} →
  ¬ ({A : Type a} {B : Type b} →
     Contractible A → Contractible (Lens A B))
¬-Contractible-closed-domain =
  Stable-¬
    [ (∀ {A B} → Contractible A → Contractible (Lens A B))    ↝⟨ (λ hyp c → H-level-cong _ 0 Lens≃Higher-lens (hyp c)) ⟩
      (∀ {A B} → Contractible A → Contractible (H.Lens A B))  ↝⟨ H.¬-Contractible-closed-domain univ ⟩□
      ⊥                                                       □
    ]

-- Contractibleᴱ is closed under Lens A.

Contractibleᴱ-closed-codomain :
  Contractibleᴱ B → Contractibleᴱ (Lens A B)
Contractibleᴱ-closed-codomain {B = B} {A = A} cB =
                            $⟨ lens-to-contractible≃ᴱ⊤ (λ _ → cB) ⟩
  Lens A B ≃ᴱ ⊤             ↝⟨ _⇔_.from EEq.Contractibleᴱ⇔≃ᴱ⊤ ⟩□
  Contractibleᴱ (Lens A B)  □

-- If B is a proposition, then Lens A B is also a proposition (in
-- erased contexts).

@0 Is-proposition-closed-codomain :
  Is-proposition B → Is-proposition (Lens A B)
Is-proposition-closed-codomain {B = B} {A = A} =
  Is-proposition B             ↝⟨ H.Is-proposition-closed-codomain univ ⟩
  Is-proposition (H.Lens A B)  ↝⟨ H-level-cong _ 1 (inverse Lens≃Higher-lens) ⟩□
  Is-proposition (Lens A B)    □

-- If A is a proposition, then Lens A B is also a proposition (in
-- erased contexts).

@0 Is-proposition-closed-domain :
  Is-proposition A → Is-proposition (Lens A B)
Is-proposition-closed-domain {A = A} {B = B} =
  Is-proposition A             ↝⟨ H.Is-proposition-closed-domain univ ⟩
  Is-proposition (H.Lens A B)  ↝⟨ H-level-cong _ 1 (inverse Lens≃Higher-lens) ⟩□
  Is-proposition (Lens A B)    □

-- If A is a set, then Lens A B is also a set (in erased contexts).

@0 Is-set-closed-domain :
  Is-set A → Is-set (Lens A B)
Is-set-closed-domain {A = A} {B = B} =
  Is-set A             ↝⟨ H.Is-set-closed-domain univ ⟩
  Is-set (H.Lens A B)  ↝⟨ H-level-cong _ 2 (inverse Lens≃Higher-lens) ⟩□
  Is-set (Lens A B)    □

-- If A has h-level n, then Lens A B has h-level 1 + n (in erased
-- contexts).

@0 domain-0+⇒lens-1+ :
  ∀ n → H-level n A → H-level (1 + n) (Lens A B)
domain-0+⇒lens-1+ {A = A} {B = B} n =
  H-level n A                   ↝⟨ H.domain-0+⇒lens-1+ univ n ⟩
  H-level (1 + n) (H.Lens A B)  ↝⟨ H-level-cong _ (1 + n) (inverse Lens≃Higher-lens) ⟩□
  H-level (1 + n) (Lens A B)    □

-- If B is inhabited when it is merely inhabited and A has positive
-- h-level n, then Lens A B also has h-level n (in erased contexts).

@0 lens-preserves-h-level-of-domain :
  (∥ B ∥ → B) →
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain {B = B} {A = A} ∥B∥→B n =
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

-- The two directions of get⁻¹ᴱ-constant.

get⁻¹ᴱ-const :
  (l : Lens A B) (b₁ b₂ : B) →
  Lens.get l ⁻¹ᴱ b₁ → Lens.get l ⁻¹ᴱ b₂
get⁻¹ᴱ-const l b₁ b₂ = _≃ᴱ_.to (get⁻¹ᴱ-constant l b₁ b₂)

get⁻¹ᴱ-const⁻¹ :
  (l : Lens A B) (b₁ b₂ : B) →
  Lens.get l ⁻¹ᴱ b₂ → Lens.get l ⁻¹ᴱ b₁
get⁻¹ᴱ-const⁻¹ l b₁ b₂ = _≃ᴱ_.from (get⁻¹ᴱ-constant l b₁ b₂)

-- The set function can be expressed using get⁻¹ᴱ-constant and get.
--
-- Paolo Capriotti defines set in a similar way
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

set-in-terms-of-get⁻¹ᴱ-constant :
  (l : Lens A B) →
  Lens.set l ≡
  λ a b → proj₁ (get⁻¹ᴱ-const l (Lens.get l a) b (a , [ refl _ ]))
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

@0 get⁻¹ᴱ-const-∘ :
  (l : Lens A B) (b₁ b₂ b₃ : B) (p : Lens.get l ⁻¹ᴱ b₁) →
  get⁻¹ᴱ-const l b₂ b₃ (get⁻¹ᴱ-const l b₁ b₂ p) ≡
  get⁻¹ᴱ-const l b₁ b₃ p
get⁻¹ᴱ-const-∘ l _ b₂ b₃ p =
  from (r₂ , b₃) , [ cong proj₂ (right-inverse-of (r₂ , b₃)) ]  ≡⟨ cong (λ r → from (r , b₃) , [ cong proj₂ (right-inverse-of (r , b₃)) ]) $
                                                                   cong proj₁ $ right-inverse-of _ ⟩∎
  from (r₁ , b₃) , [ cong proj₂ (right-inverse-of (r₁ , b₃)) ]  ∎
  where
  open Lens l
  open _≃ᴱ_ equiv

  r₁ r₂ : R
  r₁ = proj₁ (to (proj₁ p))
  r₂ = proj₁ (to (from (r₁ , b₂)))

get⁻¹ᴱ-const-inverse :
  (l : Lens A B) (b₁ b₂ : B) (p : Lens.get l ⁻¹ᴱ b₁) →
  get⁻¹ᴱ-const l b₁ b₂ p ≡ get⁻¹ᴱ-const⁻¹ l b₂ b₁ p
get⁻¹ᴱ-const-inverse _ _ _ _ = refl _

@0 get⁻¹ᴱ-const-id :
  (l : Lens A B) (b : B) (p : Lens.get l ⁻¹ᴱ b) →
  get⁻¹ᴱ-const l b b p ≡ p
get⁻¹ᴱ-const-id l b p =
  get⁻¹ᴱ-const l b b p                          ≡⟨ sym $ get⁻¹ᴱ-const-∘ l b _ _ p ⟩
  get⁻¹ᴱ-const l b b (get⁻¹ᴱ-const l b b p)     ≡⟨⟩
  get⁻¹ᴱ-const⁻¹ l b b (get⁻¹ᴱ-const l b b p)   ≡⟨ _≃ᴱ_.left-inverse-of (get⁻¹ᴱ-constant l b b) _ ⟩∎
  p                                             ∎

-- Another kind of coherence property does not hold for
-- get⁻¹ᴱ-constant.
--
-- This kind of property came up in a discussion with Andrea Vezzosi.

get⁻¹ᴱ-const-not-coherent :
  ¬ ({A B : Type} (l : Lens A B) (b₁ b₂ : B)
     (f : ∀ b → Lens.get l ⁻¹ᴱ b) →
     get⁻¹ᴱ-const l b₁ b₂ (f b₁) ≡ f b₂)
get⁻¹ᴱ-const-not-coherent =
  ({A B : Type} (l : Lens A B) (b₁ b₂ : B)
   (f : ∀ b → Lens.get l ⁻¹ᴱ b) →
   get⁻¹ᴱ-const l b₁ b₂ (f b₁) ≡ f b₂)          ↝⟨ (λ hyp → hyp l true false f) ⟩

  get⁻¹ᴱ-const l true false (f true) ≡ f false  ↝⟨ cong (proj₁ ⊚ proj₁) ⟩

  true ≡ false                                  ↝⟨ Bool.true≢false ⟩□

  ⊥                                             □
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

-- Two lenses of type Lens A B are equal if B is inhabited and the
-- lenses' setters are equal (in erased contexts).
--
-- Note that some results above are more general than this one.

@0 lenses-with-inhabited-codomains-equal-if-setters-equal :
  (l₁ l₂ : Lens A B) →
  B →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-with-inhabited-codomains-equal-if-setters-equal l₁ l₂ b =
  Lens.set l₁ ≡ Lens.set l₂  ↝⟨ H.lenses-with-inhabited-codomains-equal-if-setters-equal univ (high l₁) (high l₂) b ⟩
  high l₁ ≡ high l₂          ↔⟨ Eq.≃-≡ Lens≃Higher-lens ⟩□
  l₁ ≡ l₂                    □

------------------------------------------------------------------------
-- Equal lenses can be "observably different"

-- An example based on one presented in "Shattered lens" by Oleg
-- Grenrus.
--
-- Grenrus states that there are two lenses with equal getters and
-- setters that are "observably different".

-- A lemma used to construct the two lenses of the example.

grenrus-example : (Bool → Bool ↔ Bool) → Lens (Bool × Bool) Bool
grenrus-example eq = record
  { R         = Bool
  ; inhabited = ∣_∣
  ; equiv     = Bool × Bool  ↔⟨ ×-cong₁ eq ⟩□
                Bool × Bool  □
  }

-- The two lenses.

grenrus-example₁ = grenrus-example (if_then F.id else Bool.swap)
grenrus-example₂ = grenrus-example (if_then Bool.swap else F.id)

-- The two lenses have equal setters (in erased contexts).

@0 set-grenrus-example₁≡set-grenrus-example₂ :
  Lens.set grenrus-example₁ ≡ Lens.set grenrus-example₂
set-grenrus-example₁≡set-grenrus-example₂ =
  H.set-grenrus-example₁≡set-grenrus-example₂

-- Thus the lenses are equal (in erased contexts).

@0 grenrus-example₁≡grenrus-example₂ :
  grenrus-example₁ ≡ grenrus-example₂
grenrus-example₁≡grenrus-example₂ =
  lenses-with-inhabited-codomains-equal-if-setters-equal
    _ _ true
    set-grenrus-example₁≡set-grenrus-example₂

-- However, in a certain sense the lenses are "observably different".

grenrus-example₁-true :
  Lens.remainder grenrus-example₁ (true , true) ≡ true
grenrus-example₁-true = refl _

grenrus-example₂-false :
  Lens.remainder grenrus-example₂ (true , true) ≡ false
grenrus-example₂-false = refl _

------------------------------------------------------------------------
-- Lens combinators

module Lens-combinators where

  -- The definition of the identity lens is unique (in erased
  -- contexts), if the get function is required to be the identity.

  @0 id-unique :
    (l₁ l₂ : Lens A A) →
    Lens.get l₁ ≡ P.id →
    Lens.get l₂ ≡ P.id →
    l₁ ≡ l₂
  id-unique {A = A} l₁ l₂ g₁ g₂ =
                       $⟨ HC.id-unique univ (high l₁) (high l₂) g₁ g₂ ⟩
    high l₁ ≡ high l₂  ↝⟨ Eq.≃-≡ Lens≃Higher-lens {x = l₁} {y = l₂} ⟩□
    l₁ ≡ l₂            □

  -- The result of composing two lenses is unique (in erased contexts)
  -- if the codomain type is inhabited whenever it is merely
  -- inhabited, and we require that the resulting setter function is
  -- defined in a certain way.

  @0 ∘-unique :
    let open Lens in
    (∥ C ∥ → C) →
    ((comp₁ , _) (comp₂ , _) :
       ∃ λ (comp : Lens B C → Lens A B → Lens A C) →
         ∀ l₁ l₂ a c →
           set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp₁ ≡ comp₂
  ∘-unique {C = C} {A = A} ∥C∥→C
           (comp₁ , set₁) (comp₂ , set₂) =
    ⟨ext⟩ λ l₁ → ⟨ext⟩ λ l₂ →
      lenses-equal-if-setters-equal
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
  -- contexts).

  @0 Higher-lens-id≡id :
    (b : Block "id") →
    Higher-lens→Lens (HC.id b) ≡ id {A = A} b
  Higher-lens-id≡id {A = A} ⊠ =
    _↔_.from equality-characterisation₁
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
    ∀ a b {A : Type (a ⊔ b ⊔ c)} {B : Type (b ⊔ c)} {C : Type c} →
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

  -- The composition operation implements set in a certain way.

  ∘-set :
    let open Lens in
    ∀ ℓa ℓb {A : Type (ℓa ⊔ ℓb ⊔ c)} {B : Type (ℓb ⊔ c)} {C : Type c}
    (l₁ : Lens B C) (l₂ : Lens A B) a c →
    set (⟨ ℓa , ℓb ⟩ l₁ ∘ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)
  ∘-set _ _ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ = refl _

  -- Higher-lens→Lens commutes with composition (in erased contexts).

  @0 Higher-lens-∘≡∘ :
    ∀ a b {A : Type (a ⊔ b ⊔ c)} {B : Type (b ⊔ c)} {C : Type c} →
    (l₁ : H.Lens B C) (l₂ : H.Lens A B) →
    Higher-lens→Lens (HC.⟨ a , b ⟩ l₁ ∘ l₂) ≡
    ⟨ a , b ⟩ Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂
  Higher-lens-∘≡∘ _ _ (H.⟨ _ , _ , _ ⟩) (H.⟨ _ , _ , _ ⟩) =
    _↔_.from equality-characterisation₁
      ( F.id
      , λ _ → refl _
      )

  -- A variant of composition for lenses between types with the same
  -- universe level.

  infixr 9 _∘_

  _∘_ :
    {A B C : Type a} →
    Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = ⟨ lzero , lzero ⟩ l₁ ∘ l₂

  -- Other definitions of composition match ⟨_,_⟩_∘_ (in erased
  -- contexts), if the codomain type is inhabited whenever it is
  -- merely inhabited, and the resulting setter function is defined in
  -- a certain way.

  @0 composition≡∘ :
    let open Lens in
    {A : Type (a ⊔ b ⊔ c)} {B : Type (b ⊔ c)} {C : Type c} →
    (∥ C ∥ → C) →
    (comp : Lens B C → Lens A B → Lens A C) →
    (∀ l₁ l₂ a c →
       set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp ≡ ⟨ a , b ⟩_∘_
  composition≡∘ ∥C∥→C comp set-comp =
    ∘-unique ∥C∥→C (comp , set-comp)
      (_ , λ { ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ → refl _ })

  -- Identity and composition form a kind of precategory (in erased
  -- contexts).

  @0 associativity :
    ∀ a b c
      {A : Type (a ⊔ b ⊔ c ⊔ d)} {B : Type (b ⊔ c ⊔ d)}
      {C : Type (c ⊔ d)} {D : Type d} →
    (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ =
    _↔_.from equality-characterisation₁
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl _)

  @0 left-identity :
    ∀ bi a {A : Type (a ⊔ b)} {B : Type b} →
    (l : Lens A B) →
    ⟨ a , lzero ⟩ id bi ∘ l ≡ l
  left-identity ⊠ _ {B = B} l@(⟨ _ , _ , _ ⟩) =
    _↔_.from equality-characterisation₁
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
    ∀ bi a {A : Type (a ⊔ b)} {B : Type b} →
    (l : Lens A B) →
    ⟨ lzero , a ⟩ l ∘ id bi ≡ l
  right-identity ⊠ _ {A = A} l@(⟨ _ , _ , _ ⟩) =
    _↔_.from equality-characterisation₁
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
    Bi-invertibility.Erased equality-with-J (Type a) Lens (id b) _∘_
  module BM {a} (b : Block "id") = B.More
    {a = a}
    b
    (left-identity b _)
    (right-identity b _)
    (associativity _ _ _)

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≅ᴱ_ to [_]_≅ᴱ_;
            Has-quasi-inverseᴱ to Has-quasi-inverseᴱ)

private

  -- Some lemmas used below.

  @0 ∘≡id→∘≡id :
    {A B : Type a}
    (b : Block "id") →
    (l₁ : H.Lens B A) (l₂ : H.Lens A B) →
    l₁ HC.∘ l₂ ≡ HC.id b →
    Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂ ≡ id b
  ∘≡id→∘≡id b l₁ l₂ hyp =
    Higher-lens→Lens l₁ ∘ Higher-lens→Lens l₂  ≡⟨ sym $ Higher-lens-∘≡∘ lzero lzero l₁ l₂ ⟩
    Higher-lens→Lens (l₁ HC.∘ l₂)              ≡⟨ cong Higher-lens→Lens hyp ⟩
    Higher-lens→Lens (HC.id b)                 ≡⟨ Higher-lens-id≡id b ⟩∎
    id b                                       ∎

  @0 l∘l⁻¹≡l∘l⁻¹ :
    {A B : Type a} →
    (l : H.Lens B A) (l⁻¹ : Lens A B) →
    Higher-lens→Lens (l HC.∘ high l⁻¹) ≡ Higher-lens→Lens l ∘ l⁻¹
  l∘l⁻¹≡l∘l⁻¹ l l⁻¹ =
    Higher-lens→Lens (l HC.∘ high l⁻¹)                ≡⟨ Higher-lens-∘≡∘ lzero lzero l (high l⁻¹) ⟩
    Higher-lens→Lens l ∘ Higher-lens→Lens (high l⁻¹)  ≡⟨ cong (Higher-lens→Lens l ∘_) $
                                                         _≃_.left-inverse-of Lens≃Higher-lens l⁻¹ ⟩∎
    Higher-lens→Lens l ∘ l⁻¹                          ∎

  @0 l⁻¹∘l≡l⁻¹∘l :
    {A B : Type a} →
    (l⁻¹ : Lens B A) (l : H.Lens A B) →
    Higher-lens→Lens (high l⁻¹ HC.∘ l) ≡ l⁻¹ ∘ Higher-lens→Lens l
  l⁻¹∘l≡l⁻¹∘l l⁻¹ l =
    Higher-lens→Lens (high l⁻¹ HC.∘ l)                ≡⟨ Higher-lens-∘≡∘ lzero lzero (high l⁻¹) l ⟩
    Higher-lens→Lens (high l⁻¹) ∘ Higher-lens→Lens l  ≡⟨ cong (_∘ Higher-lens→Lens l) $
                                                         _≃_.left-inverse-of Lens≃Higher-lens l⁻¹ ⟩∎
    l⁻¹ ∘ Higher-lens→Lens l                          ∎

-- In erased contexts Has-quasi-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to HC.Has-quasi-inverse b l.

@0 Has-quasi-inverseᴱ≃Has-quasi-inverse :
  {A B : Type a}
  (b : Block "id") →
  (l : H.Lens A B) →
  Has-quasi-inverseᴱ b (Higher-lens→Lens l) ≃ HC.Has-quasi-inverse b l
Has-quasi-inverseᴱ≃Has-quasi-inverse b l =
  (∃ λ l⁻¹ → Erased (l′    ∘ l⁻¹ ≡    id b × l⁻¹    ∘ l′ ≡    id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′    ∘ l⁻¹ ≡    id b × l⁻¹    ∘ l′ ≡    id b )  ↝⟨ (inverse $
                                                                          Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                                          (≡⇒↝ _ (cong₂ _≡_ (l∘l⁻¹≡l∘l⁻¹ l l⁻¹) (Higher-lens-id≡id b)) F.∘
                                                                           inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens))
                                                                            ×-cong
                                                                          (≡⇒↝ _ (cong₂ _≡_ (l⁻¹∘l≡l⁻¹∘l l⁻¹ l) (Higher-lens-id≡id b)) F.∘
                                                                           inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens))) ⟩□
  (∃ λ l⁻¹ →         l  HC.∘ l⁻¹ ≡ HC.id b × l⁻¹ HC.∘ l  ≡ HC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts [ b ] A ≅ᴱ B is equivalent to HC.[ b ] A ≅ B.

@0 ≅ᴱ≃≅ :
  {A B : Type a}
  (b : Block "id") →
  ([ b ] A ≅ᴱ B) ≃ (HC.[ b ] A ≅ B)
≅ᴱ≃≅ {A = A} {B = B} b =
  (∃ λ (l : Lens A B) → Has-quasi-inverseᴱ b l)      ↝⟨ Σ-cong-contra (inverse Lens≃Higher-lens) $
                                                        Has-quasi-inverseᴱ≃Has-quasi-inverse b ⟩□
  (∃ λ (l : H.Lens A B) → HC.Has-quasi-inverse b l)  □

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

-- There is a logical equivalence between [ b ] A ≅ᴱ B and A ≃ᴱ B.

≅ᴱ⇔≃ᴱ :
  {A B : Type a}
  (b : Block "id") →
  ([ b ] A ≅ᴱ B) ⇔ (A ≃ᴱ B)
≅ᴱ⇔≃ᴱ {A = A} {B = B} b = record
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
    l∘l⁻¹≡id ⊠ = _↔_.from equality-characterisation₁
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
    l⁻¹∘l≡id ⊠ = _↔_.from equality-characterisation₁
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
  {A B : Type a}
  (b : Block "id")
  (A≃B : A ≃ᴱ B) →
  _⇔_.to (≅ᴱ⇔≃ᴱ b) (_⇔_.from (≅ᴱ⇔≃ᴱ b) A≃B) ≡ A≃B
≅ᴱ⇔≃ᴱ∘≅ᴱ⇔≃ᴱ ⊠ _ = EEq.to≡to→≡ ext (refl _)

-- There is not necessarily a split surjection from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe.

¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ :
  (b : Block "id") →
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)
¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ {a = a} b =
  Stable-¬
    [ ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)     ↝⟨ (λ hyp → lemma hyp) ⟩

      ({A B : Type a}
       (l : H.Lens A B) →
       Is-equivalence (H.Lens.get l) ↠ HC.Has-quasi-inverse b l)  ↝⟨ HC.¬Is-equivalence-get↠Has-quasi-inverse b univ ⟩□

      ⊥                                                           □
    ]
  where
  @0 lemma : ∀ {A B : Type a} _ (l : H.Lens A B) → _
  lemma hyp l@(H.⟨ _ , _ , _ ⟩) =
    Is-equivalence (Lens.get (Higher-lens→Lens l))   ↔⟨ EEq.Is-equivalence≃Is-equivalenceᴱ ⟩
    Is-equivalenceᴱ (Lens.get (Higher-lens→Lens l))  ↝⟨ hyp (Higher-lens→Lens l) ⟩
    Has-quasi-inverseᴱ b (Higher-lens→Lens l)        ↔⟨ Has-quasi-inverseᴱ≃Has-quasi-inverse b l ⟩□
    HC.Has-quasi-inverse b l                         □

-- There is not necessarily an equivalence with erased proofs from
-- Is-equivalenceᴱ (Lens.get l) to Has-quasi-inverseᴱ l, if l is a
-- lens between types in the same universe.

¬Is-equivalenceᴱ-get≃ᴱHas-quasi-inverseᴱ :
  (b : Block "id") →
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ b l)
¬Is-equivalenceᴱ-get≃ᴱHas-quasi-inverseᴱ {a = a} b =
  Stable-¬
    [ ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ≃ᴱ Has-quasi-inverseᴱ b l)  ↝⟨ (λ hyp l → _≃_.surjection $ EEq.≃ᴱ→≃ $ hyp l) ⟩

      ({A B : Type a}
       (l : Lens A B) →
       Is-equivalenceᴱ (Lens.get l) ↠ Has-quasi-inverseᴱ b l)   ↝⟨ ¬Is-equivalenceᴱ-get↠Has-quasi-inverseᴱ b ⟩□

      ⊥                                                         □
    ]

-- See also ≃ᴱ≃ᴱ≅ᴱ below.

------------------------------------------------------------------------
-- Equivalences expressed using bi-invertibility for lenses

-- A form of equivalence between types, expressed using lenses.

open B public
  using ()
  renaming (_≊ᴱ_ to [_]_≊ᴱ_;
            Has-left-inverseᴱ to Has-left-inverseᴱ;
            Has-right-inverseᴱ to Has-right-inverseᴱ;
            Is-bi-invertibleᴱ to Is-bi-invertibleᴱ)
open BM public
  using ()
  renaming (equality-characterisation-≊ᴱ to
            equality-characterisation-≊ᴱ)

-- In erased contexts Has-left-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to HC.Has-left-inverse b l.

@0 Has-left-inverseᴱ≃Has-left-inverse :
  {A B : Type a}
  (b : Block "id") →
  (l : H.Lens A B) →
  Has-left-inverseᴱ b (Higher-lens→Lens l) ≃ HC.Has-left-inverse b l
Has-left-inverseᴱ≃Has-left-inverse b l =
  (∃ λ l⁻¹ → Erased (l⁻¹    ∘ l′ ≡    id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l⁻¹    ∘ l′ ≡    id b )  ↝⟨ (inverse $
                                                  Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                  ≡⇒↝ _ (cong₂ _≡_ (l⁻¹∘l≡l⁻¹∘l l⁻¹ l) (Higher-lens-id≡id b)) F.∘
                                                  inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens)) ⟩□
  (∃ λ l⁻¹ →         l⁻¹ HC.∘ l  ≡ HC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Has-right-inverseᴱ b (Higher-lens→Lens l) is
-- equivalent to HC.Has-right-inverse b l.

@0 Has-right-inverseᴱ≃Has-right-inverse :
  {A B : Type a}
  (b : Block "id") →
  (l : H.Lens A B) →
  Has-right-inverseᴱ b (Higher-lens→Lens l) ≃ HC.Has-right-inverse b l
Has-right-inverseᴱ≃Has-right-inverse b l =
  (∃ λ l⁻¹ → Erased (l′    ∘ l⁻¹ ≡    id b))  ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ l⁻¹ →         l′    ∘ l⁻¹ ≡    id b )  ↝⟨ (inverse $
                                                  Σ-cong-contra Lens≃Higher-lens λ l⁻¹ →
                                                  ≡⇒↝ _ (cong₂ _≡_ (l∘l⁻¹≡l∘l⁻¹ l l⁻¹) (Higher-lens-id≡id b)) F.∘
                                                  inverse (Eq.≃-≡ $ inverse Lens≃Higher-lens)) ⟩□
  (∃ λ l⁻¹ →         l  HC.∘ l⁻¹ ≡ HC.id b )  □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts Is-bi-invertibleᴱ b (Higher-lens→Lens l) is
-- equivalent to HC.Is-bi-invertible b l.

@0 Is-bi-invertibleᴱ≃Is-bi-invertible :
  {A B : Type a}
  (b : Block "id") →
  (l : H.Lens A B) →
  Is-bi-invertibleᴱ b (Higher-lens→Lens l) ≃ HC.Is-bi-invertible b l
Is-bi-invertibleᴱ≃Is-bi-invertible b l =
  Is-bi-invertibleᴱ b l′                              ↔⟨⟩
  Has-left-inverseᴱ b l′ × Has-right-inverseᴱ b l′    ↝⟨ Has-left-inverseᴱ≃Has-left-inverse b l
                                                           ×-cong
                                                         Has-right-inverseᴱ≃Has-right-inverse b l ⟩
  HC.Has-left-inverse b l × HC.Has-right-inverse b l  ↔⟨⟩
  HC.Is-bi-invertible b l                             □
  where
  l′ = Higher-lens→Lens l

-- In erased contexts [ b ] A ≊ᴱ B is equivalent to HC.[ b ] A ≊ B.

@0 ≊ᴱ≃≊ :
  {A B : Type a}
  (b : Block "id") →
  ([ b ] A ≊ᴱ B) ≃ (HC.[ b ] A ≊ B)
≊ᴱ≃≊ {A = A} {B = B} b =
  (∃ λ (l : Lens A B) → Is-bi-invertibleᴱ b l)      ↝⟨ Σ-cong-contra (inverse Lens≃Higher-lens) $
                                                       Is-bi-invertibleᴱ≃Is-bi-invertible b ⟩□
  (∃ λ (l : H.Lens A B) → HC.Is-bi-invertible b l)  □

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
-- [ b ] A ≊ᴱ B.

≃ᴱ≃ᴱ≊ᴱ :
  {A B : Type a}
  (b : Block "id") →
  (A ≃ᴱ B) ≃ᴱ ([ b ] A ≊ᴱ B)
≃ᴱ≃ᴱ≊ᴱ {A = A} {B = B} b =
  EEq.↔→≃ᴱ (to b) (from b) (to∘from b) (from∘to b)
  where
  open Lens

  to : ∀ b → A ≃ᴱ B → [ b ] A ≊ᴱ B
  to b = B.≅ᴱ→≊ᴱ b ⊚ _⇔_.from (≅ᴱ⇔≃ᴱ b)

  from : ∀ b → [ b ] A ≊ᴱ B → A ≃ᴱ B
  from b = _⇔_.to (≅ᴱ⇔≃ᴱ b) ⊚ _⇔_.from (BM.≅ᴱ⇔≊ᴱ b)

  @0 to∘from : ∀ b A≊ᴱB → to b (from b A≊ᴱB) ≡ A≊ᴱB
  to∘from b A≊ᴱB =
    _≃_.from (equality-characterisation-≊ᴱ b _ _) $
    _↔_.from equality-characterisation₂
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
    _⇔_.to (≅ᴱ⇔≃ᴱ b) (_⇔_.from (BM.≅ᴱ⇔≊ᴱ b)
      (B.≅ᴱ→≊ᴱ b (_⇔_.from (≅ᴱ⇔≃ᴱ b) A≃B))) ≡
    A≃B
  from∘to ⊠ _ = EEq.to≡to→≡ ext (refl _)

-- The right-to-left direction of ≃ᴱ≃ᴱ≊ᴱ maps bi-invertible lenses to
-- their getter functions.

to-from-≃ᴱ≃ᴱ≊ᴱ≡get :
  (b : Block "id")
  (A≊ᴱB@(l , _) : [ b ] A ≊ᴱ B) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ b) A≊ᴱB) ≡ Lens.get l
to-from-≃ᴱ≃ᴱ≊ᴱ≡get
  ⊠ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl _

-- A variant of ≃ᴱ≃ᴱ≊ᴱ that works even if A and B live in different
-- universes.
--
-- This kind of variant came up in a discussion with Andrea Vezzosi.

≃ᴱ≃ᴱ≊ᴱ′ :
  {A : Type a} {B : Type b}
  (b-id : Block "id") →
  (A ≃ᴱ B) ≃ᴱ ([ b-id ] ↑ b A ≊ᴱ ↑ a B)
≃ᴱ≃ᴱ≊ᴱ′ {a = a} {b = b} {A = A} {B = B} b-id =
  A ≃ᴱ B                   ↝⟨ inverse $ EEq.≃ᴱ-cong ext (from-isomorphism Bijection.↑↔)
                                                        (from-isomorphism Bijection.↑↔) ⟩
  ↑ b A ≃ᴱ ↑ a B           ↝⟨ ≃ᴱ≃ᴱ≊ᴱ b-id ⟩□
  [ b-id ] ↑ b A ≊ᴱ ↑ a B  □

-- The right-to-left direction of ≃ᴱ≃ᴱ≊ᴱ′ maps bi-invertible lenses to a
-- variant of their getter functions.

to-from-≃ᴱ≃ᴱ≊ᴱ′≡get :
  (b-id : Block "id")
  (A≊ᴱB@(l , _) : [ b-id ] ↑ b A ≊ᴱ ↑ a B) →
  _≃ᴱ_.to (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ′ b-id) A≊ᴱB) ≡
  lower ⊚ Lens.get l ⊚ lift
to-from-≃ᴱ≃ᴱ≊ᴱ′≡get
  ⊠ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl _

-- The getter function of a bi-invertible lens is an equivalence with
-- erased proofs.

Is-bi-invertibleᴱ→Is-equivalenceᴱ-get :
  (b : Block "id") →
  (l : Lens A B) →
  Is-bi-invertibleᴱ b l → Is-equivalenceᴱ (Lens.get l)
Is-bi-invertibleᴱ→Is-equivalenceᴱ-get
  b@⊠ l@(⟨ _ , _ , _ ⟩)
  is-bi-inv@((⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  _≃ᴱ_.is-equivalence (_≃ᴱ_.from (≃ᴱ≃ᴱ≊ᴱ b) (l , is-bi-inv))

-- If l is a lens between types in the same universe, then there is an
-- equivalence with erased proofs between "l is bi-invertible (with
-- erased proofs)" and "the getter of l is an equivalence (with erased
-- proofs)".

Is-bi-invertibleᴱ≃ᴱIs-equivalenceᴱ-get :
  {A B : Type a}
  (b : Block "id") →
  (l : Lens A B) →
  Is-bi-invertibleᴱ b l ≃ᴱ Is-equivalenceᴱ (Lens.get l)
Is-bi-invertibleᴱ≃ᴱIs-equivalenceᴱ-get b l = EEq.⇔→≃ᴱ
  (BM.Is-bi-invertibleᴱ-propositional b l)
  (EEq.Is-equivalenceᴱ-propositional ext _)
  (Is-bi-invertibleᴱ→Is-equivalenceᴱ-get b l)
  (λ is-equiv →

     let l′ = ≃ᴱ→Lens′ EEq.⟨ get l , is-equiv ⟩ in

                             $⟨ proj₂ (_≃ᴱ_.to (≃ᴱ≃ᴱ≊ᴱ b) EEq.⟨ _ , is-equiv ⟩) ⟩
     Is-bi-invertibleᴱ b l′  ↝⟨ subst (λ ([ l ]) → Is-bi-invertibleᴱ b l) $ sym $
                                []-cong [ get-equivalence→≡≃ᴱ→Lens′ l is-equiv ] ⟩□
     Is-bi-invertibleᴱ b l   □)
  where
  open Lens

-- If A is a set, then there is an equivalence with erased proofs
-- between [ b ] A ≊ᴱ B and [ b ] A ≅ᴱ B.

≊ᴱ≃ᴱ≅ᴱ :
  {A B : Type a}
  (b : Block "id") →
  @0 Is-set A →
  ([ b ] A ≊ᴱ B) ≃ᴱ ([ b ] A ≅ᴱ B)
≊ᴱ≃ᴱ≅ᴱ b A-set =
  ∃-cong λ _ →
    BM.Is-bi-invertibleᴱ≃ᴱHas-quasi-inverseᴱ-domain
      b (Is-set-closed-domain A-set)

-- If A is a set, then there is an equivalence with erased proofs
-- between A ≃ᴱ B and [ b ] A ≅ᴱ B.

≃ᴱ≃ᴱ≅ᴱ :
  {A B : Type a}
  (b : Block "≃ᴱ≃ᴱ≅ᴱ") →
  @0 Is-set A →
  (A ≃ᴱ B) ≃ᴱ ([ b ] A ≅ᴱ B)
≃ᴱ≃ᴱ≅ᴱ {A = A} {B = B} b@⊠ A-set =
  A ≃ᴱ B        ↝⟨ ≃ᴱ≃ᴱ≊ᴱ b ⟩
  [ b ] A ≊ᴱ B  ↝⟨ ≊ᴱ≃ᴱ≅ᴱ b A-set ⟩□
  [ b ] A ≅ᴱ B  □

-- In erased contexts one can prove that ≃ᴱ≃ᴱ≅ᴱ maps identity to
-- identity.

@0 ≃ᴱ≃ᴱ≅ᴱ-id≡id :
  (b : Block "≃ᴱ≃ᴱ≅ᴱ")
  (A-set : Is-set A) →
  proj₁ (_≃ᴱ_.to (≃ᴱ≃ᴱ≅ᴱ b A-set) F.id) ≡ id b
≃ᴱ≃ᴱ≅ᴱ-id≡id ⊠ _ =
  _↔_.from equality-characterisation₁
    (F.id , λ _ → refl _)

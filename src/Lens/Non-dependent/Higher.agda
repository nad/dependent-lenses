------------------------------------------------------------------------
-- Higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Higher where

import Bi-invertibility
open import Equality.Propositional.Cubical as EP
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Category equality-with-J as C using (Category; Precategory)
open import Circle equality-with-paths as Circle using (𝕊¹)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
import Nat equality-with-J as Nat
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent
import Lens.Non-dependent.Traditional as Traditional

private
  variable
    a b c d r             : Level
    A A₁ A₂ B B₁ B₂ C X Y : Set a
    n                     : ℕ

------------------------------------------------------------------------
-- Higher lenses

-- Higher lenses.
--
-- A little history: The "lenses" in Lens.Non-dependent.Bijection are
-- not very well-behaved. I had previously considered some other
-- variants, when Andrea Vezzosi suggested that I should look at Paolo
-- Capriotti's higher lenses, and that I could perhaps use R → ∥ B ∥.
-- This worked out nicely.
--
-- For performance reasons η-equality is turned off for this record
-- type. One can match on the constructor to block evaluation.

record Lens (A : Set a) (B : Set b) : Set (lsuc (a ⊔ b)) where
  constructor ⟨_,_,_⟩
  pattern
  no-eta-equality
  field
    -- Remainder type.
    R : Set (a ⊔ b)

    -- Equivalence.
    equiv : A ≃ (R × B)

    -- The proof of (mere) inhabitance.
    inhabited : R → ∥ B ∥

  -- Remainder.

  remainder : A → R
  remainder a = proj₁ (_≃_.to equiv a)

  -- Getter.

  get : A → B
  get a = proj₂ (_≃_.to equiv a)

  -- Setter.

  set : A → B → A
  set a b = _≃_.from equiv (remainder a , b)

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    proj₂ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₂ (_≃_.right-inverse-of equiv _) ⟩∎
    proj₂ (remainder a , b)                                  ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    _≃_.from equiv (_≃_.to equiv a)  ≡⟨ _≃_.left-inverse-of equiv _ ⟩∎
    a                                ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    let r = remainder a in

    _≃_.from equiv (remainder (_≃_.from equiv (r , b₁)) , b₂)  ≡⟨⟩

    _≃_.from equiv
      (proj₁ (_≃_.to equiv (_≃_.from equiv (r , b₁))) , b₂)    ≡⟨ cong (λ x → _≃_.from equiv (proj₁ x , b₂))
                                                                       (_≃_.right-inverse-of equiv _) ⟩∎
    _≃_.from equiv (r , b₂)                                    ∎

  -- Another law.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b =
    proj₁ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of equiv _ ⟩∎
    remainder a                                              ∎

  -- The remainder function is surjective.

  remainder-surjective : Surjective remainder
  remainder-surjective r =
    ∥∥-map (λ b → _≃_.from equiv (r , b)
                , (remainder (_≃_.from equiv (r , b))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of equiv _ ⟩∎
                   r                                   ∎))
           (inhabited r)

  -- Traditional lens.

  traditional-lens : Traditional.Lens A B
  traditional-lens = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }

  -- The following coherence law, which does not necessarily hold for
  -- traditional lenses (see
  -- Traditional.bi-invertible-but-not-coherent), holds
  -- unconditionally for higher lenses.

  get-set-get : ∀ a → get-set a (get a) ≡ cong get (set-get a)
  get-set-get a =
    cong proj₂ (_≃_.right-inverse-of equiv _)                       ≡⟨ cong (cong proj₂) $ sym $ _≃_.left-right-lemma equiv _ ⟩
    cong proj₂ (cong (_≃_.to equiv) (_≃_.left-inverse-of equiv _))  ≡⟨ cong-∘ _ _ (_≃_.left-inverse-of equiv _) ⟩∎
    cong (proj₂ ⊚ _≃_.to equiv) (_≃_.left-inverse-of equiv _)       ∎

------------------------------------------------------------------------
-- Simple definitions related to lenses

-- Lens can be expressed as a nested Σ-type.

Lens-as-Σ :
  {A : Set a} {B : Set b} →
  Lens A B ↔
  ∃ λ (R : Set (a ⊔ b)) →
    (A ≃ (R × B)) ×
    (R → ∥ B ∥)
Lens-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ l → R l , equiv l , inhabited l
      ; from = λ (R , equiv , inhabited) → record
                 { R         = R
                 ; equiv     = equiv
                 ; inhabited = inhabited
                 }
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ { ⟨ _ , _ , _ ⟩ → refl }
  }
  where
  open Lens

-- Isomorphisms can be converted into lenses.

isomorphism-to-lens :
  {A : Set a} {B : Set b} {R : Set (a ⊔ b)} →
  A ↔ R × B → Lens A B
isomorphism-to-lens {A = A} {B = B} {R = R} iso = record
  { R         = R × ∥ B ∥
  ; equiv     = A                ↔⟨ iso ⟩
                R × B            ↔⟨ F.id ×-cong inverse ∥∥×↔ ⟩
                R × ∥ B ∥ × B    ↔⟨ ×-assoc ⟩□
                (R × ∥ B ∥) × B  □
  ; inhabited = proj₂
  }

-- Converts equivalences to lenses.

≃→lens :
  {A : Set a} {B : Set b} →
  A ≃ B → Lens A B
≃→lens {a = a} {A = A} {B = B} A≃B = record
  { R         = ∥ ↑ a B ∥
  ; equiv     = A              ↝⟨ A≃B ⟩
                B              ↝⟨ inverse ∥∥×≃ ⟩
                ∥ B ∥ × B      ↔⟨ ∥∥-cong (inverse Bij.↑↔) ×-cong F.id ⟩□
                ∥ ↑ a B ∥ × B  □
  ; inhabited = ∥∥-map lower
  }

-- Converts equivalences between types with the same universe level to
-- lenses.

≃→lens′ :
  {A B : Set a} →
  A ≃ B → Lens A B
≃→lens′ {a = a} {A = A} {B = B} A≃B = record
  { R         = ∥ B ∥
  ; equiv     = A          ↝⟨ A≃B ⟩
                B          ↝⟨ inverse ∥∥×≃ ⟩□
                ∥ B ∥ × B  □
  ; inhabited = P.id
  }

------------------------------------------------------------------------
-- Equality characterisations for lenses

-- Equality of lenses is isomorphic to certain pairs.

equality-characterisation₀ :
  {l₁ l₂ : Lens A B} →
  let open Lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                     ↔⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Lens-as-Σ ⟩

  l₁′ ≡ l₂′                                                   ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B) × (R → ∥ B ∥)) p (proj₂ l₁′) ≡
     proj₂ l₂′)                                               ↝⟨ (∃-cong λ _ → inverse $
                                                                    ignore-propositional-component
                                                                      (Π-closure ext 1 λ _ →
                                                                       truncation-is-proposition)) ⟩
  (∃ λ (p : R l₁ ≡ R l₂) →
     proj₁ (subst (λ R → A ≃ (R × B) × (R → ∥ B ∥))
                  p
                  (proj₂ l₁′)) ≡
     equiv l₂)                                                ↝⟨ (∃-cong λ p → ≡⇒↝ _ $
                                                                    cong (λ x → proj₁ x ≡ _) (push-subst-, {y≡z = p} _ _)) ⟩□
  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)       □
  where
  open Lens

  l₁′ = _↔_.to Lens-as-Σ l₁
  l₂′ = _↔_.to Lens-as-Σ l₂

-- Equality of lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₁ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂
equality-characterisation₁ {A = A} {B} {l₁} {l₂} univ =
  l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₀ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)              ↝⟨ inverse $ Σ-cong (inverse $ ≡≃≃ univ) (λ _ → F.id) ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     subst (λ R → A ≃ (R × B)) (≃⇒≡ univ eq) (equiv l₁) ≡ equiv l₂)  ↝⟨ (∃-cong λ _ → inverse $ ≡⇒↝ _ $ cong (λ p → p ≡ _) $
                                                                           transport-theorem
                                                                             (λ R → A ≃ (R × B)) resp
                                                                             (λ _ → Eq.lift-equality ext refl)
                                                                             univ _ _) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) → resp eq (equiv l₁) ≡ equiv l₂)           □
  where
  open Lens

  resp : X ≃ Y → A ≃ (X × B) → A ≃ (Y × B)
  resp {X = X} {Y = Y} X≃Y A≃X×B =
    A      ↝⟨ A≃X×B ⟩
    X × B  ↝⟨ X≃Y ×-cong F.id ⟩□
    Y × B  □

-- Equality of lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₂ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
          _≃_.to (equiv l₂) x
equality-characterisation₂ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                             ↝⟨ equality-characterisation₁ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)        ↝⟨ (∃-cong λ _ → inverse $ ≃-to-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                       □
  where
  open Lens

-- Equality of lenses is isomorphic to certain triples (assuming
-- univalence).

equality-characterisation₃ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₃ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                                 ↝⟨ equality-characterisation₂ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → (_≃_.to eq (remainder l₁ x) , get l₁ x) ≡
           _≃_.to (equiv l₂) x)                           ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse ≡×≡↔≡) ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x
             ×
           get l₁ x ≡ get l₂ x)                           ↝⟨ (∃-cong λ _ → ΠΣ-comm) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
       ×
     (∀ x → get l₁ x ≡ get l₂ x))                         □
  where
  open Lens

-- Equality of lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₄ :
  {A : Set a} {B : Set b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃_.from (equiv l₂) p
equality-characterisation₄ {l₁ = l₁} {l₂} univ =
  l₁ ≡ l₂                                                           ↝⟨ equality-characterisation₁ univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)                      ↝⟨ (∃-cong λ _ → inverse $ ≃-from-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃_.from (equiv l₂) p)                                   □
  where
  open Lens

------------------------------------------------------------------------
-- More lens equalities

-- If the forward direction of an equivalence is Lens.get l, then the
-- setter of l can be expressed using the other direction of the
-- equivalence.

from≡set :
  ∀ (l : Lens A B) is-equiv →
  let open Lens
      A≃B = Eq.⟨ get l , is-equiv ⟩
  in
  ∀ a b → _≃_.from A≃B b ≡ set l a b
from≡set l is-equiv a b =
  _≃_.to-from Eq.⟨ get , is-equiv ⟩ (
    get (set a b)  ≡⟨ get-set _ _ ⟩∎
    b              ∎)
  where
  open Lens l

-- If two lenses have equal setters, then they also have equal
-- getters.

getters-equal-if-setters-equal :
  let open Lens in
  (l₁ l₂ : Lens A B) →
  set l₁ ≡ set l₂ →
  get l₁ ≡ get l₂
getters-equal-if-setters-equal l₁ l₂ setters-equal = ⟨ext⟩ λ a →
  get l₁ a                      ≡⟨ cong (get l₁) $ sym $ set-get l₂ _ ⟩
  get l₁ (set l₂ a (get l₂ a))  ≡⟨ cong (λ f → get l₁ (f a (get l₂ a))) $ sym setters-equal ⟩
  get l₁ (set l₁ a (get l₂ a))  ≡⟨ get-set l₁ _ _ ⟩∎
  get l₂ a                      ∎
  where
  open Lens

-- A generalisation of lenses-equal-if-setters-equal (which is defined
-- below).

lenses-equal-if-setters-equal′ :
  let open Lens in
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b))
  (l₁ l₂ : Lens A B)
  (f : R l₁ → R l₂) →
  (B → ∀ r →
   ∃ λ b′ → remainder l₂ (_≃_.from (equiv l₁) (r , b′)) ≡ f r) →
  (∀ a → f (remainder l₁ a) ≡ remainder l₂ a) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal′
   {A = A} {B = B} univ l₁ l₂
   f ∃≡f f-remainder≡remainder setters-equal =

  _↔_.from (equality-characterisation₃ univ)
    ( R≃R
    , f-remainder≡remainder
    , ext⁻¹ (getters-equal-if-setters-equal l₁ l₂ setters-equal)
    )
  where
  open Lens
  open _≃_

  BR≃BR =
    B × R l₁  ↔⟨ ×-comm ⟩
    R l₁ × B  ↝⟨ inverse (equiv l₁) ⟩
    A         ↝⟨ equiv l₂ ⟩
    R l₂ × B  ↔⟨ ×-comm ⟩□
    B × R l₂  □

  to-BR≃BR :
    ∀ b b′ r →
    to BR≃BR (b , r) ≡ (b , remainder l₂ (from (equiv l₁) (r , b′)))
  to-BR≃BR b b′ r =
    swap (to (equiv l₂) (from (equiv l₁) (swap (b , r))))      ≡⟨ cong swap lemma ⟩
    swap (swap (b , remainder l₂ (from (equiv l₁) (r , b′))))  ≡⟨⟩
    b , remainder l₂ (from (equiv l₁) (r , b′))                ∎
    where
    lemma =
      to (equiv l₂) (from (equiv l₁) (swap (b , r)))             ≡⟨⟩

      to (equiv l₂) (from (equiv l₁) (r , b))                    ≡⟨ cong (λ r → to (equiv l₂) (from (equiv l₁) (proj₁ r , b))) $ sym $
                                                                    right-inverse-of (equiv l₁) _ ⟩
      to (equiv l₂) (from (equiv l₁)
        (proj₁ (to (equiv l₁) (from (equiv l₁) (r , b′))) , b))  ≡⟨⟩

      to (equiv l₂) (set l₁ (from (equiv l₁) (r , b′)) b)        ≡⟨ cong (to (equiv l₂)) $ ext⁻¹ (ext⁻¹ setters-equal _) _ ⟩

      to (equiv l₂) (set l₂ (from (equiv l₁) (r , b′)) b)        ≡⟨⟩

      to (equiv l₂) (from (equiv l₂)
        (remainder l₂ (from (equiv l₁) (r , b′)) , b))           ≡⟨ right-inverse-of (equiv l₂) _ ⟩

      remainder l₂ (from (equiv l₁) (r , b′)) , b                ≡⟨⟩

      swap (b , remainder l₂ (from (equiv l₁) (r , b′)))         ∎

  id-f≃ : Eq.Is-equivalence (Σ-map P.id f)
  id-f≃ = Eq.respects-extensional-equality
    (λ (b , r) →
       let b′ , ≡fr = ∃≡f b r in
       to BR≃BR (b , r)                             ≡⟨ to-BR≃BR _ _ _ ⟩
       b , remainder l₂ (from (equiv l₁) (r , b′))  ≡⟨ cong (b ,_) ≡fr ⟩
       b , f r                                      ≡⟨⟩
       Σ-map P.id f (b , r)                         ∎)
    (is-equivalence BR≃BR)

  f≃ : Eq.Is-equivalence f
  f≃ r =
    Trunc.rec
      (H-level-propositional ext 0)
      (λ b → Eq.drop-Σ-map-id _ id-f≃ b r)
      (inhabited l₂ r)

  R≃R : R l₁ ≃ R l₂
  R≃R = Eq.⟨ f , f≃ ⟩

-- If the codomain of a lens is inhabited when it is merely inhabited
-- and the remainder type is inhabited, then this lens is equal to
-- another lens if their setters are equal (assuming univalence).

lenses-equal-if-setters-equal :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  (Lens.R l₁ → ∥ B ∥ → B) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal {B = B} univ l₁ l₂ inh′ setters-equal =
  lenses-equal-if-setters-equal′
    univ l₁ l₂ f
    (λ _ r →
         inh r
       , (remainder l₂ (_≃_.from (equiv l₁) (r , inh r))  ≡⟨⟩
          f r                                             ∎))
    (λ a →
       f (remainder l₁ a)                              ≡⟨⟩
       remainder l₂ (set l₁ a (inh (remainder l₁ a)))  ≡⟨ cong (remainder l₂) $ ext⁻¹ (ext⁻¹ setters-equal _) _ ⟩
       remainder l₂ (set l₂ a (inh (remainder l₁ a)))  ≡⟨ remainder-set l₂ _ _ ⟩∎
       remainder l₂ a                                  ∎)
    setters-equal
  where
  open Lens

  inh : Lens.R l₁ → B
  inh r = inh′ r (inhabited l₁ r)

  f : R l₁ → R l₂
  f r = remainder l₂ (_≃_.from (equiv l₁) (r , inh r))

-- If a lens has a propositional remainder type, then this lens is
-- equal to another lens if their setters are equal (assuming
-- univalence).

lenses-equal-if-setters-equal-and-remainder-propositional :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  Is-proposition (Lens.R l₂) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal-and-remainder-propositional
  univ l₁ l₂ R₂-prop =

  lenses-equal-if-setters-equal′
    univ l₁ l₂ f
    (λ b r →
         b
       , (remainder l₂ (_≃_.from (equiv l₁) (r , b))  ≡⟨ R₂-prop _ _ ⟩∎
          f r                                         ∎))
    (λ a →
       f (remainder l₁ a)  ≡⟨ R₂-prop _ _ ⟩
       remainder l₂ a      ∎)
  where
  open Lens

  f : R l₁ → R l₂
  f r =
    Trunc.rec R₂-prop
      (λ b → remainder l₂ (_≃_.from (equiv l₁) (r , b)))
      (inhabited l₁ r)

-- The functions ≃→lens and ≃→lens′ are pointwise equal (when
-- applicable, assuming univalence).

≃→lens≡≃→lens′ :
  {A B : Set a} →
  Univalence a →
  (A≃B : A ≃ B) → ≃→lens A≃B ≡ ≃→lens′ A≃B
≃→lens≡≃→lens′ {A = A} {B = B} univ A≃B =
  _↔_.from (equality-characterisation₃ univ)
    ( (∥ ↑ _ B ∥  ↔⟨ ∥∥-cong Bij.↑↔ ⟩□
       ∥ B ∥      □)
    , (λ _ → refl)
    , (λ _ → refl)
    )

-- If the getter of a lens is an equivalence, then the lens formed
-- using the equivalence (using ≃→lens) is equal to the lens (assuming
-- univalence).

get-equivalence→≡≃→lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l : Lens A B) →
  (eq : Is-equivalence (Lens.get l)) →
  l ≡ ≃→lens Eq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃→lens {A = A} {B = B} univ l eq =
  lenses-equal-if-setters-equal-and-remainder-propositional
    univ l (≃→lens Eq.⟨ Lens.get l , eq ⟩)
    truncation-is-proposition
    (⟨ext⟩ λ a → ⟨ext⟩ λ b →
     set l a b             ≡⟨ sym $ from≡set l eq a b ⟩
     _≃_.from A≃B b        ≡⟨⟩
     set (≃→lens A≃B) a b  ∎)
  where
  open Lens

  A≃B : A ≃ B
  A≃B = Eq.⟨ _ , eq ⟩

-- A variant of get-equivalence→≡≃→lens.

get-equivalence→≡≃→lens′ :
  {A B : Set a} →
  Univalence a →
  (l : Lens A B) →
  (eq : Is-equivalence (Lens.get l)) →
  l ≡ ≃→lens′ Eq.⟨ Lens.get l , eq ⟩
get-equivalence→≡≃→lens′ {A = A} {B = B} univ l eq =
  l            ≡⟨ get-equivalence→≡≃→lens univ _ _ ⟩
  ≃→lens A≃B   ≡⟨ ≃→lens≡≃→lens′ univ _ ⟩∎
  ≃→lens′ A≃B  ∎
  where
  A≃B = Eq.⟨ Lens.get l , eq ⟩

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Lens preserves bijections.

Lens-cong′ :
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  (∃ λ (R : Set r) → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥)) ↔
  (∃ λ (R : Set r) → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))
Lens-cong′ A₁↔A₂ B₁↔B₂ =
  ∃-cong λ _ →
  Eq.≃-preserves-bijections ext A₁↔A₂ (F.id ×-cong B₁↔B₂)
    ×-cong
  →-cong ext F.id (∥∥-cong B₁↔B₂)

-- Lens preserves level-preserving bijections.

Lens-cong :
  {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  Lens A₁ B₁ ↔ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁↔A₂ B₁↔B₂ =
  Lens A₁ B₁                              ↝⟨ Lens-as-Σ ⟩
  (∃ λ R → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥))  ↝⟨ Lens-cong′ A₁↔A₂ B₁↔B₂ ⟩
  (∃ λ R → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))  ↝⟨ inverse Lens-as-Σ ⟩□
  Lens A₂ B₂                              □

-- If B is a proposition, then Lens A B is isomorphic to A → B
-- (assuming univalence).

lens-to-proposition↔get :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Lens A B ↔ (A → B)
lens-to-proposition↔get {b = b} {A = A} {B = B} univ B-prop =
  Lens A B                             ↝⟨ Lens-as-Σ ⟩
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                             ∥∥↔ B-prop) ⟩
  (∃ λ R → A ≃ (R × B) × (R → B))      ↝⟨ (∃-cong λ _ →
                                           ×-cong₁ λ R→B →
                                           Eq.≃-preserves-bijections ext F.id $
                                             drop-⊤-right λ r →
                                               _⇔_.to contractible⇔↔⊤ $
                                                 propositional⇒inhabited⇒contractible B-prop (R→B r)) ⟩
  (∃ λ R → A ≃ R × (R → B))            ↔⟨ (∃-cong λ _ →
                                           ∃-cong λ A≃R →
                                           →-cong {k = equivalence} ext (inverse A≃R) F.id) ⟩
  (∃ λ R → A ≃ R × (A → B))            ↝⟨ Σ-assoc ⟩
  (∃ λ R → A ≃ R) × (A → B)            ↝⟨ (drop-⊤-left-× λ _ → other-singleton-with-≃-↔-⊤ {b = b} ext univ) ⟩□
  (A → B)                              □

_ :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b))
  (prop : Is-proposition B)
  (l : Lens A B) →
  _↔_.to (lens-to-proposition↔get univ prop) l ≡
  rec prop P.id ⊚ Lens.inhabited l ⊚ Lens.remainder l
_ = λ _ _ _ → refl

-- A variant of the previous result.

lens-to-proposition≃get :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Lens A B ≃ (A → B)
lens-to-proposition≃get {b = b} {A = A} {B = B} univ prop = Eq.↔→≃
  get
  from
  (λ _ → refl)
  (λ l →
     let lemma =
           ↑ b A    ↔⟨ Bij.↑↔ ⟩
           A        ↝⟨ equiv l ⟩
           R l × B  ↔⟨ (drop-⊤-right λ r → _⇔_.to contractible⇔↔⊤ $
                        Trunc.rec
                          (Contractible-propositional ext)
                          (propositional⇒inhabited⇒contractible prop)
                          (inhabited l r)) ⟩□
           R l      □
     in
     _↔_.from (equality-characterisation₂ univ)
        (lemma , λ _ → refl))
  where
  open Lens

  from = λ get → record
    { R         = ↑ b A
    ; equiv     = A          ↔⟨ inverse Bij.↑↔ ⟩
                  ↑ b A      ↔⟨ (inverse $ drop-⊤-right {k = bijection} λ (lift a) →
                                 _⇔_.to contractible⇔↔⊤ $
                                 propositional⇒inhabited⇒contractible prop (get a)) ⟩□
                  ↑ b A × B  □
    ; inhabited = ∣_∣ ⊚ get ⊚ lower
    }

_ :
  {A : Set a} {B : Set b}
  (univ : Univalence (a ⊔ b))
  (prop : Is-proposition B)
  (l : Lens A B) →
  _≃_.to (lens-to-proposition≃get univ prop) l ≡ Lens.get l
_ = λ _ _ _ → refl

-- If B is contractible, then Lens A B is isomorphic to ⊤ (assuming
-- univalence).

lens-to-contractible↔⊤ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B →
  Lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} univ cB =
  Lens A B  ↝⟨ lens-to-proposition↔get univ (mono₁ 0 cB) ⟩
  (A → B)   ↝⟨ →-cong ext F.id $ _⇔_.to contractible⇔↔⊤ cB ⟩
  (A → ⊤)   ↝⟨ →-right-zero ⟩□
  ⊤         □

-- Lens A ⊥ is isomorphic to ¬ A (assuming univalence).

lens-to-⊥↔¬ :
  {A : Set a} →
  Univalence (a ⊔ b) →
  Lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔¬ {A = A} univ =
  Lens A ⊥  ↝⟨ lens-to-proposition↔get univ ⊥-propositional ⟩
  (A → ⊥)   ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A       □

-- If A is contractible, then Lens A B is isomorphic to Contractible B
-- (assuming univalence).

lens-from-contractible↔codomain-contractible :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible A →
  Lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible {A = A} {B} univ cA =
  Lens A B                                                   ↝⟨ Lens-as-Σ ⟩
  (∃ λ R → A ≃ (R × B) × (R → ∥ B ∥))                        ↝⟨ ∃-cong (λ _ →
                                                                  Eq.≃-preserves-bijections ext (_⇔_.to contractible⇔↔⊤ cA) F.id
                                                                    ×-cong
                                                                  F.id) ⟩
  (∃ λ R → ⊤ ≃ (R × B) × (R → ∥ B ∥))                        ↝⟨ ∃-cong (λ _ → Eq.inverse-isomorphism ext ×-cong F.id) ⟩
  (∃ λ R → (R × B) ≃ ⊤ × (R → ∥ B ∥))                        ↝⟨ ∃-cong (λ _ → inverse (contractible↔≃⊤ ext) ×-cong F.id) ⟩
  (∃ λ R → Contractible (R × B) × (R → ∥ B ∥))               ↝⟨ ∃-cong (λ _ → Contractible-commutes-with-× ext ×-cong F.id) ⟩
  (∃ λ R → (Contractible R × Contractible B) × (R → ∥ B ∥))  ↝⟨ ∃-cong (λ _ → inverse ×-assoc) ⟩
  (∃ λ R → Contractible R × Contractible B × (R → ∥ B ∥))    ↝⟨ ∃-cong (λ _ → ∃-cong λ cR →
                                                                  F.id
                                                                    ×-cong
                                                                  →-cong ext (_⇔_.to contractible⇔↔⊤ cR) F.id) ⟩
  (∃ λ R → Contractible R × Contractible B × (⊤ → ∥ B ∥))    ↝⟨ ∃-cong (λ _ → F.id ×-cong F.id ×-cong Π-left-identity) ⟩
  (∃ λ R → Contractible R × Contractible B × ∥ B ∥)          ↝⟨ ∃-cong (λ _ → ×-comm) ⟩
  (∃ λ R → (Contractible B × ∥ B ∥) × Contractible R)        ↝⟨ ∃-comm ⟩
  (Contractible B × ∥ B ∥) × (∃ λ R → Contractible R)        ↝⟨ drop-⊤-right (λ _ → ∃Contractible↔⊤ ext univ) ⟩
  Contractible B × ∥ B ∥                                     ↝⟨ drop-⊤-right (λ cB → inhabited⇒∥∥↔⊤ ∣ proj₁ cB ∣) ⟩□
  Contractible B                                             □

-- Lens ⊥ B is isomorphic to the unit type (assuming univalence).

lens-from-⊥↔⊤ :
  {B : Set b} →
  Univalence (a ⊔ b) →
  Lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ {B = B} univ =
  _⇔_.to contractible⇔↔⊤ $
    isomorphism-to-lens
      (⊥      ↝⟨ inverse ×-left-zero ⟩□
       ⊥ × B  □) ,
    λ l → _↔_.from (equality-characterisation₂ univ)
            ( (⊥ × ∥ B ∥  ↔⟨ ×-left-zero ⟩
               ⊥₀         ↔⟨ lemma l ⟩□
               R l        □)
            , λ x → ⊥-elim x
            )
  where
  open Lens

  lemma : (l : Lens ⊥ B) → ⊥₀ ↔ R l
  lemma l = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⊥-elim
        ; from = whatever
        }
      ; right-inverse-of = whatever
      }
    ; left-inverse-of = λ x → ⊥-elim x
    }
    where
    whatever : ∀ {ℓ} {Whatever : R l → Set ℓ} → (r : R l) → Whatever r
    whatever r = ⊥-elim {ℓ = lzero} $
      rec ⊥-propositional
          (λ b → ⊥-elim (_≃_.from (equiv l) (r , b)))
          (inhabited l r)

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- In general there is no split surjection from Lens A B to
-- Traditional.Lens A B (assuming univalence).

¬Lens↠Traditional-lens :
  Univalence lzero →
  Univalence a →
  ∃ λ (A : Set a) →
    ¬ (Lens A ⊤ ↠ Traditional.Lens A ⊤)
¬Lens↠Traditional-lens univ₀ univ =
  let A = _ in

  A ,
  (λ surj →                                 $⟨ _⇔_.from contractible⇔↔⊤ (lens-to-contractible↔⊤ univ ⊤-contractible) ⟩
     Contractible (Lens A ⊤)                ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (Traditional.Lens A ⊤)    ↝⟨ mono₁ 0 ⟩
     Is-proposition (Traditional.Lens A ⊤)  ↝⟨ proj₂ $ Traditional.¬-lens-to-⊤-propositional univ₀ ⟩□
     ⊥                                      □)

-- Some lemmas used in Lens↠Traditional-lens and Lens↔Traditional-lens
-- below.

private

  module Lens↔Traditional-lens
    {A : Set a} {B : Set b}
    (A-set : Is-set A)
    where

    from : Block "conversion" → Traditional.Lens A B → Lens A B
    from ⊠ l = isomorphism-to-lens
      {R = ∃ λ (f : B → A) → ∀ b b′ → set (f b) b′ ≡ f b′}
      (record
         { surjection = record
           { logical-equivalence = record
             { to   = λ a → (set a , set-set a) , get a
             ; from = λ { ((f , _) , b) → f b }
             }
           ; right-inverse-of = λ { ((f , h) , b) →

              let
                irr = {p q : ∀ b b′ → set (f b) b′ ≡ f b′} → p ≡ q
                irr =
                  (Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   A-set) _ _

                lemma =
                  get (f b)          ≡⟨ cong get (sym (h b b)) ⟩
                  get (set (f b) b)  ≡⟨ get-set (f b) b ⟩∎
                  b                  ∎
              in
              (set (f b) , set-set (f b)) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ (⟨ext⟩ (h b)) irr) lemma ⟩∎
              (f         , h            ) , b          ∎ }
           }
         ; left-inverse-of = λ a →
             set a (get a)  ≡⟨ set-get a ⟩∎
             a              ∎
         })
      where
      open Traditional.Lens l

    to∘from : ∀ bc l → Lens.traditional-lens (from bc l) ≡ l
    to∘from ⊠ l = _↔_.from Traditional.equality-characterisation₁
      ( refl
      , refl
      , (λ a _ → B-set a _ _)
      , (λ _ → A-set _ _)
      , (λ _ _ _ → A-set _ _)
      )
      where
      open Traditional.Lens l

      B-set : A → Is-set B
      B-set a =
        Traditional.h-level-respects-lens-from-inhabited 2 l a A-set

    from∘to :
      Univalence (a ⊔ b) →
      ∀ bc l → from bc (Lens.traditional-lens l) ≡ l
    from∘to univ ⊠ l′ =
      _↔_.from (equality-characterisation₄ univ)
               (lemma , λ _ → refl)
      where
      open Lens l′ renaming (equiv to l)

      B-set : (B → R) → ∥ B ∥ → Is-set B
      B-set f =
        rec (H-level-propositional ext 2)
            (λ b → proj₂-closure (f b) 2 $
                   H-level.respects-surjection
                     (_≃_.surjection l) 2 A-set)

      R-set : ∥ B ∥ → Is-set R
      R-set =
        rec (H-level-propositional ext 2)
            (λ b → proj₁-closure (const b) 2 $
                   H-level.respects-surjection
                     (_≃_.surjection l) 2 A-set)

      lemma′ : (∥ B ∥ × (∥ B ∥ → R)) ↔ R
      lemma′ = record
        { surjection = record
          { logical-equivalence = record
            { to   = λ { (∥b∥ , f) → f ∥b∥ }
            ; from = λ r → inhabited r , λ _ → r
            }
          ; right-inverse-of = λ _ → refl
          }
        ; left-inverse-of = λ { (∥b∥ , f) →
            curry (_↔_.to ≡×≡↔≡)
              (truncation-is-proposition _ _)
              (⟨ext⟩ λ ∥b∥′ →
                 f ∥b∥   ≡⟨ cong f (truncation-is-proposition _ _) ⟩∎
                 f ∥b∥′  ∎) }
        }

      lemma =
        (∃ λ (f : B → A) → ∀ b b′ →
             _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′) ×
        ∥ B ∥                                                       ↔⟨ ×-comm ⟩

        (∥ B ∥ ×
         ∃ λ (f : B → A) → ∀ b b′ →
             _≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡ f b′)       ↝⟨ (∃-cong λ _ →
                                                                        Σ-cong (→-cong ext F.id l) λ f →
                                                                               ∀-cong ext λ b → ∀-cong ext λ b′ →
                                                                               ≡⇒↝ _ (cong (_≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡_)
                                                                                           (sym $ _≃_.left-inverse-of l _))) ⟩
        (∥ B ∥ ×
         ∃ λ (f : B → R × B) → ∀ b b′ →
             _≃_.from l (proj₁ (f b) , b′) ≡ _≃_.from l (f b′))     ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                         Eq.≃-≡ (inverse l)) ⟩
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
        (∥ B ∥ × ∃ λ (f : B → R) → Constant f)                      ↝⟨ (∃-cong λ ∥b∥ → constant-function≃∥inhabited∥⇒inhabited (R-set ∥b∥)) ⟩

        (∥ B ∥ × (∥ B ∥ → R))                                       ↔⟨ lemma′ ⟩□

        R                                                           □

    iso :
      Block "conversion" →
      Univalence (a ⊔ b) →
      Lens A B ↔ Traditional.Lens A B
    iso bc univ = record
      { surjection = record
        { logical-equivalence = record { from = from bc }
        ; right-inverse-of    = to∘from bc
        }
      ; left-inverse-of = from∘to univ bc
      }

-- If the domain A is a set, then there is a split surjection from
-- Lens A B to Traditional.Lens A B.

Lens↠Traditional-lens :
  Block "conversion" →
  Is-set A →
  Lens A B ↠ Traditional.Lens A B
Lens↠Traditional-lens {A = A} {B = B} bc A-set = record
  { logical-equivalence = record
    { to   = Lens.traditional-lens
    ; from = Lens↔Traditional-lens.from A-set bc
    }
  ; right-inverse-of = Lens↔Traditional-lens.to∘from A-set bc
  }

-- If the domain A is a set, then Traditional.Lens A B and Lens A B
-- are isomorphic (assuming univalence).

Lens↔Traditional-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Is-set A →
  Lens A B ↔ Traditional.Lens A B
Lens↔Traditional-lens bc univ A-set =
  Lens↔Traditional-lens.iso A-set bc univ

-- If the codomain B is an inhabited set, then Lens A B and
-- Traditional.Lens A B are logically equivalent.
--
-- This definition is inspired by the statement of Corollary 13 from
-- "Algebras and Update Strategies" by Johnson, Rosebrugh and Wood.

Lens⇔Traditional-lens :
  Is-set B →
  B →
  Lens A B ⇔ Traditional.Lens A B
Lens⇔Traditional-lens {B = B} {A = A} B-set b₀ = record
  { to   = Lens.traditional-lens
  ; from = from
  }
  where
  from : Traditional.Lens A B → Lens A B
  from l = isomorphism-to-lens
    {R = ∃ λ (a : A) → get a ≡ b₀}
    (record
       { surjection = record
         { logical-equivalence = record
           { to   = λ a → (set a b₀ , get-set a b₀) , get a
           ; from = λ { ((a , _) , b) → set a b }
           }
         ; right-inverse-of = λ { ((a , h) , b) →
             let
               lemma =
                 set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
                 set a b₀          ≡⟨ cong (set a) (sym h) ⟩
                 set a (get a)     ≡⟨ set-get a ⟩∎
                 a                 ∎
             in
             ((set (set a b) b₀ , get-set (set a b) b₀) , get (set a b))  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma (B-set _ _)) (get-set a b) ⟩∎
             ((a                , h                   ) , b            )  ∎
           }
         }
       ; left-inverse-of = λ a →
           set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
           set a (get a)           ≡⟨ set-get a ⟩∎
           a                       ∎
       })
    where
    open Traditional.Lens l

------------------------------------------------------------------------
-- Some results related to h-levels

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} {n = n} l a =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ proj₂-closure (remainder a) n ⟩□
  H-level n B        □
  where
  open Lens l

-- This is not necessarily true for arbitrary domains (assuming
-- univalence).

¬-h-level-respects-lens :
  Univalence (a ⊔ b) →
  ¬ (∀ n {A : Set a} {B : Set b} →
     Lens A B → H-level n A → H-level n B)
¬-h-level-respects-lens univ resp =
                             $⟨ ⊥-propositional ⟩
  Is-proposition ⊥           ↝⟨ resp 1 (_↔_.from (lens-from-⊥↔⊤ univ) _) ⟩
  Is-proposition (↑ _ Bool)  ↝⟨ ↑⁻¹-closure 1 ⟩
  Is-proposition Bool        ↝⟨ ¬-Bool-propositional ⟩□
  ⊥₀                         □

-- In fact, there is a lens with a proposition as its domain and a
-- non-set as its codomain (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-𝕊¹-set.)

lens-from-proposition-to-non-set :
  Univalence (# 0) →
  ∃ λ (A : Set a) → ∃ λ (B : Set b) →
  Lens A B × Is-proposition A × ¬ Is-set B
lens-from-proposition-to-non-set {b = b} _ =
    ⊥
  , ↑ b 𝕊¹
  , record
      { R         = ⊥
      ; equiv     = ⊥           ↔⟨ inverse ×-left-zero ⟩□
                    ⊥ × ↑ _ 𝕊¹  □
      ; inhabited = ⊥-elim
      }
  , ⊥-propositional
  , Circle.¬-𝕊¹-set ⊚
    H-level.respects-surjection (_↔_.surjection Bij.↑↔) 2

-- Lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited l (proj₁ c) c

-- The remainder type of a lens l : Lens A B is, for every b : B,
-- equivalent to the preimage of the getter with respect to b.
--
-- This result was pointed out to me by Andrea Vezzosi.

remainder≃get⁻¹ :
  (l : Lens A B) (b : B) → Lens.R l ≃ Lens.get l ⁻¹ b
remainder≃get⁻¹ l b = Eq.↔→≃
  (λ r → _≃_.from equiv (r , b)
       , (get (_≃_.from equiv (r , b))                   ≡⟨⟩
          proj₂ (_≃_.to equiv (_≃_.from equiv (r , b)))  ≡⟨ cong proj₂ $ _≃_.right-inverse-of equiv _ ⟩∎
          b                                              ∎))
  (λ (a , _) → remainder a)
  (λ (a , get-a≡b) →
     let lemma =
           cong get
             (trans (cong (set a) (sym get-a≡b))
                (_≃_.left-inverse-of equiv _))                           ≡⟨ cong-trans _ _ (_≃_.left-inverse-of equiv _) ⟩

           trans (cong get (cong (set a) (sym get-a≡b)))
             (cong get (_≃_.left-inverse-of equiv _))                    ≡⟨ cong₂ trans
                                                                              (cong-∘ _ _ (sym get-a≡b))
                                                                              (sym $ cong-∘ _ _ (_≃_.left-inverse-of equiv _)) ⟩
           trans (cong (get ⊚ set a) (sym get-a≡b))
             (cong proj₂ (cong (_≃_.to equiv)
                            (_≃_.left-inverse-of equiv _)))              ≡⟨ cong₂ (λ p q → trans p (cong proj₂ q))
                                                                              (cong-sym _ get-a≡b)
                                                                              (_≃_.left-right-lemma equiv _) ⟩
           trans (sym (cong (get ⊚ set a) get-a≡b))
             (cong proj₂ (_≃_.right-inverse-of equiv _))                 ≡⟨ sym $ sym-sym _ ⟩

           sym (sym (trans (sym (cong (get ⊚ set a) get-a≡b))
                       (cong proj₂ (_≃_.right-inverse-of equiv _))))     ≡⟨ cong sym $
                                                                            sym-trans _ (cong proj₂ (_≃_.right-inverse-of equiv _)) ⟩
           sym (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                  (sym (sym (cong (get ⊚ set a) get-a≡b))))              ≡⟨ cong (λ eq → sym (trans _ eq)) $
                                                                            sym-sym (cong (get ⊚ set a) get-a≡b) ⟩∎
           sym (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                  (cong (get ⊚ set a) get-a≡b))                          ∎
     in
     Σ-≡,≡→≡
       (_≃_.from equiv (remainder a , b)  ≡⟨⟩
        set a b                           ≡⟨ cong (set a) (sym get-a≡b) ⟩
        set a (get a)                     ≡⟨ set-get a ⟩∎
        a                                 ∎)
       (subst (λ a → get a ≡ b)
          (trans (cong (set a) (sym get-a≡b)) (set-get a))
          (cong proj₂ $ _≃_.right-inverse-of equiv (remainder a , b))  ≡⟨⟩

        subst (λ a → get a ≡ b)
          (trans (cong (set a) (sym get-a≡b))
             (_≃_.left-inverse-of equiv _))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ subst-∘ _ _ (trans _ (_≃_.left-inverse-of equiv _)) ⟩

        subst (_≡ b)
          (cong get
             (trans (cong (set a) (sym get-a≡b))
                (_≃_.left-inverse-of equiv _)))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ cong (λ eq → subst (_≡ b) eq
                                                                                           (cong proj₂ $ _≃_.right-inverse-of equiv _))
                                                                            lemma ⟩
        subst (_≡ b)
          (sym (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                  (cong (get ⊚ set a) get-a≡b)))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ subst-trans (trans _ (cong (get ⊚ set a) get-a≡b)) ⟩

        trans
          (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
             (cong (get ⊚ set a) get-a≡b))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ elim¹
                                                                              (λ eq → trans
                                                                                        (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                                                                                           (cong (get ⊚ set a) eq))
                                                                                        (cong proj₂ $ _≃_.right-inverse-of equiv _) ≡
                                                                                      eq)
                                                                              (
            trans
              (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                 (cong (get ⊚ set a) refl))
              (cong proj₂ $ _≃_.right-inverse-of equiv _)                      ≡⟨⟩

            trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
              (cong proj₂ $ _≃_.right-inverse-of equiv _)                      ≡⟨ trans-symˡ (cong proj₂ (_≃_.right-inverse-of equiv _)) ⟩∎

            refl                                                               ∎)
                                                                              get-a≡b ⟩∎
        get-a≡b                                                          ∎))
  (λ r →
     remainder (_≃_.from equiv (r , b))             ≡⟨⟩
     proj₁ (_≃_.to equiv (_≃_.from equiv (r , b)))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of equiv _ ⟩∎
     r                                              ∎)
  where
  open Lens l

-- A corollary: Lens.get l ⁻¹_ is constant (up to equivalence).

get⁻¹-constant :
  (l : Lens A B) (b₁ b₂ : B) → Lens.get l ⁻¹ b₁ ≃ Lens.get l ⁻¹ b₂
get⁻¹-constant l b₁ b₂ =
  Lens.get l ⁻¹ b₁  ↝⟨ inverse $ remainder≃get⁻¹ l b₁ ⟩
  Lens.R l          ↝⟨ remainder≃get⁻¹ l b₂ ⟩□
  Lens.get l ⁻¹ b₂  □

-- The previous lemma satisfies some coherence properties.

get⁻¹-constant-∘ :
  (l : Lens A B) (b₁ b₂ b₃ : B) (p : Lens.get l ⁻¹ b₁) →
  _≃_.to (get⁻¹-constant l b₂ b₃) (_≃_.to (get⁻¹-constant l b₁ b₂) p) ≡
  _≃_.to (get⁻¹-constant l b₁ b₃) p
get⁻¹-constant-∘ l _ b₂ b₃ p =
  from (r₂ , b₃) , cong proj₂ (right-inverse-of (r₂ , b₃))  ≡⟨ cong (λ r → from (r , b₃) , cong proj₂ (right-inverse-of (r , b₃))) $
                                                               cong proj₁ $ right-inverse-of _ ⟩∎
  from (r₁ , b₃) , cong proj₂ (right-inverse-of (r₁ , b₃))  ∎
  where
  open Lens l
  open _≃_ equiv

  r₁ r₂ : R
  r₁ = proj₁ (to (proj₁ p))
  r₂ = proj₁ (to (from (r₁ , b₂)))

get⁻¹-constant-inverse :
  (l : Lens A B) (b₁ b₂ : B) (p : Lens.get l ⁻¹ b₁) →
  _≃_.to (get⁻¹-constant l b₁ b₂) p ≡
  _≃_.from (get⁻¹-constant l b₂ b₁) p
get⁻¹-constant-inverse _ _ _ _ = refl

get⁻¹-constant-id :
  (l : Lens A B) (b : B) (p : Lens.get l ⁻¹ b) →
  _≃_.to (get⁻¹-constant l b b) p ≡ p
get⁻¹-constant-id l b p =
  _≃_.to (get⁻¹-constant l b b) p                                    ≡⟨ sym $ get⁻¹-constant-∘ l b _ _ p ⟩
  _≃_.to (get⁻¹-constant l b b) (_≃_.to (get⁻¹-constant l b b) p)    ≡⟨⟩
  _≃_.from (get⁻¹-constant l b b) (_≃_.to (get⁻¹-constant l b b) p)  ≡⟨ _≃_.left-inverse-of (get⁻¹-constant l b b) _ ⟩∎
  p                                                                  ∎

-- Another kind of coherence property does not hold for
-- get⁻¹-constant.
--
-- This kind of property came up in a discussion with Andrea Vezzosi.

get⁻¹-constant-not-coherent :
  ¬ ({A B : Set} (l : Lens A B) (b₁ b₂ : B)
     (f : ∀ b → Lens.get l ⁻¹ b) →
     _≃_.to (get⁻¹-constant l b₁ b₂) (f b₁) ≡ f b₂)
get⁻¹-constant-not-coherent =
  (({A B : Set} (l : Lens A B) (b₁ b₂ : B) (f : ∀ b → Lens.get l ⁻¹ b) →
   _≃_.to (get⁻¹-constant l b₁ b₂) (f b₁) ≡ f b₂))                        ↝⟨ (λ hyp → hyp l true false f) ⟩

  _≃_.to (get⁻¹-constant l true false) (f true) ≡ f false                 ↝⟨ cong (proj₁ ⊚ proj₁) ⟩

  true ≡ false                                                            ↝⟨ Bool.true≢false ⟩□

  ⊥                                                                       □
  where
  l : Lens (Bool × Bool) Bool
  l = record
    { R         = Bool
    ; equiv     = F.id
    ; inhabited = ∣_∣
    }

  f : ∀ b → Lens.get l ⁻¹ b
  f b = (b , b) , refl

-- If B is inhabited whenever it is merely inhabited, then the
-- remainder type of a lens of type Lens A B can be expressed in terms
-- of preimages of the lens's getter.

remainder≃∃get⁻¹ :
  (l : Lens A B) (∥B∥→B : ∥ B ∥ → B) →
  Lens.R l ≃ ∃ λ (b : ∥ B ∥) → Lens.get l ⁻¹ (∥B∥→B b)
remainder≃∃get⁻¹ {B = B} l ∥B∥→B =
  R                                     ↔⟨ (inverse $ drop-⊤-left-× λ r → _⇔_.to contractible⇔↔⊤ $
                                            propositional⇒inhabited⇒contractible truncation-is-proposition (inhabited r)) ⟩
  ∥ B ∥ × R                             ↝⟨ (∃-cong λ _ → remainder≃get⁻¹ l _) ⟩□
  (∃ λ (b : ∥ B ∥) → get ⁻¹ (∥B∥→B b))  □
  where
  open Lens l

-- If the domain type of a lens is contractible, then the remainder
-- type is also contractible.

domain-contractible⇒remainder-contractible :
  (l : Lens A B) → Contractible A → Contractible (Lens.R l)
domain-contractible⇒remainder-contractible {A = A} {B = B} l =
  Contractible A                   ↔⟨ H-level-cong {k₂ = equivalence} ext 0 equiv ⟩
  Contractible (R × B)             ↔⟨ Contractible-commutes-with-× {k = bijection} ext ⟩
  Contractible R × Contractible B  ↝⟨ proj₁ ⟩□
  Contractible R                   □
  where
  open Lens l

-- If the domain type of a lens has h-level n, then the remainder type
-- also has h-level n.

remainder-has-same-h-level-as-domain :
  (l : Lens A B) → ∀ n → H-level n A → H-level n (Lens.R l)
remainder-has-same-h-level-as-domain l zero =
  domain-contractible⇒remainder-contractible l
remainder-has-same-h-level-as-domain {A = A} {B = B} l (suc n) h =
  [inhabited⇒+]⇒+ n λ r →
                             $⟨ h ⟩
    H-level (1 + n) A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) (1 + n) ⟩
    H-level (1 + n) (R × B)  ↝⟨ rec (Π-closure ext 1 λ _ → H-level-propositional ext (1 + n))
                                    (λ b → proj₁-closure (λ _ → b) (1 + n))
                                    (inhabited r) ⟩□
    H-level (1 + n) R        □
  where
  open Lens l

-- If the getter function is an equivalence, then the remainder type
-- is propositional.

get-equivalence→remainder-propositional :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) →
  Is-proposition (Lens.R l)
get-equivalence→remainder-propositional l is-equiv =
  [inhabited⇒+]⇒+ 0 λ r →
    Trunc.rec
      (H-level-propositional ext 1)
      (λ b r₁ r₂ →
         r₁                      ≡⟨ lemma _ _ ⟩
         remainder (from A≃B b)  ≡⟨ sym $ lemma _ _ ⟩∎
         r₂                      ∎)
      (inhabited r)
  where
  open _≃_
  open Lens l

  A≃B = Eq.⟨ _ , is-equiv ⟩

  lemma : ∀ b r → r ≡ remainder (from A≃B b)
  lemma b r =
    r                                                             ≡⟨ cong proj₁ $ sym $ right-inverse-of equiv _ ⟩
    proj₁ (to equiv (from equiv (r , b)))                         ≡⟨ cong (proj₁ ⊚ to equiv) $ sym $ left-inverse-of A≃B _ ⟩
    proj₁ (to equiv (from A≃B (to A≃B (from equiv (r , b)))))     ≡⟨⟩
    remainder (from A≃B (proj₂ (to equiv (from equiv (r , b)))))  ≡⟨ cong (remainder ⊚ from A≃B ⊚ proj₂) $ right-inverse-of equiv _ ⟩∎
    remainder (from A≃B b)                                        ∎

-- If the getter function is pointwise equal to the identity
-- function, then the remainder type is propositional.

get≡id→remainder-propositional :
  (l : Lens A A) →
  (∀ a → Lens.get l a ≡ a) →
  Is-proposition (Lens.R l)
get≡id→remainder-propositional l =
  (∀ a → Lens.get l a ≡ a)     ↝⟨ (λ hyp → Eq.respects-extensional-equality (sym ⊚ hyp) (_≃_.is-equivalence F.id)) ⟩
  Is-equivalence (Lens.get l)  ↝⟨ get-equivalence→remainder-propositional l ⟩□
  Is-proposition (Lens.R l)    □

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Lens A B (assuming univalence).

¬-Contractible-closed-domain :
  ∀ {a b} →
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Contractible A → Contractible (Lens A B))
¬-Contractible-closed-domain univ closure =
                                 $⟨ ↑⊤-contractible ⟩
  Contractible (↑ _ ⊤)           ↝⟨ closure ⟩
  Contractible (Lens (↑ _ ⊤) ⊥)  ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ lens-from-contractible↔codomain-contractible univ ↑⊤-contractible)
                                      0 ⟩
  Contractible (Contractible ⊥)  ↝⟨ proj₁ ⟩
  Contractible ⊥                 ↝⟨ proj₁ ⟩
  ⊥                              ↝⟨ ⊥-elim ⟩□
  ⊥₀                             □
  where
  ↑⊤-contractible = ↑-closure 0 ⊤-contractible

-- Contractible is closed under Lens A (assuming univalence).

Contractible-closed-codomain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B → Contractible (Lens A B)
Contractible-closed-codomain {A = A} {B} univ cB =
                           $⟨ lens-to-contractible↔⊤ univ cB ⟩
  Lens A B ↔ ⊤             ↝⟨ _⇔_.from contractible⇔↔⊤ ⟩□
  Contractible (Lens A B)  □

-- If B is a proposition, then Lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-codomain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B → Is-proposition (Lens A B)
Is-proposition-closed-codomain {A = A} {B} univ B-prop =
                             $⟨ Π-closure ext 1 (λ _ → B-prop) ⟩
  Is-proposition (A → B)     ↝⟨ H-level.respects-surjection
                                  (_↔_.surjection $ inverse $ lens-to-proposition↔get univ B-prop)
                                  1 ⟩□
  Is-proposition (Lens A B)  □

private

  -- If A has h-level 1 + n and equivalence between certain remainder
  -- types has h-level n, then Lens A B has h-level 1 + n (assuming
  -- univalence).

  domain-1+-remainder-equivalence-0+⇒lens-1+ :
    {A : Set a} {B : Set b} →
    Univalence (a ⊔ b) →
    ∀ n →
    H-level (1 + n) A →
    ((l₁ l₂ : Lens A B) →
       H-level n (Lens.R l₁ ≃ Lens.R l₂)) →
    H-level (1 + n) (Lens A B)
  domain-1+-remainder-equivalence-0+⇒lens-1+
    {A = A} univ n hA hR = ≡↔+ _ _ λ l₁ l₂ →                    $⟨ Σ-closure n (hR l₁ l₂) (λ _ →
                                                                   Π-closure ext n λ _ →
                                                                   +⇒≡ hA) ⟩
    H-level n (∃ λ (eq : R l₁ ≃ R l₂) → ∀ p → _≡_ {A = A} _ _)  ↝⟨ H-level.respects-surjection
                                                                     (_↔_.surjection $ inverse $ equality-characterisation₄ univ)
                                                                     n ⟩□
    H-level n (l₁ ≡ l₂)                                         □
    where
    open Lens

-- If A is a proposition, then Lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Lens A B)
Is-proposition-closed-domain {b = b} {A = A} {B = B} univ A-prop =
                                          $⟨ R₁≃R₂ ⟩
  (∀ l₁ l₂ → R l₁ ≃ R l₂)                 ↝⟨ (λ hyp l₁ l₂ → propositional⇒inhabited⇒contractible
                                                              (Eq.left-closure ext 0 (R-prop l₁))
                                                              (hyp l₁ l₂)) ⟩
  (∀ l₁ l₂ → Contractible (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ 0 A-prop ⟩□
  Is-proposition (Lens A B)               □
  where
  open Lens

  R-prop : (l : Lens A B) → Is-proposition (R l)
  R-prop l =
    remainder-has-same-h-level-as-domain l 1 A-prop

  remainder⁻¹ : (l : Lens A B) → R l → A
  remainder⁻¹ l r =
    rec A-prop
        (λ b → _≃_.from (equiv l) (r , b))
        (inhabited l r)

  R-to-R : (l₁ l₂ : Lens A B) → R l₁ → R l₂
  R-to-R l₁ l₂ = remainder l₂ ⊚ remainder⁻¹ l₁

  involutive : (l : Lens A B) {f : R l → R l} → ∀ r → f r ≡ r
  involutive l _ = R-prop l _ _

  R₁≃R₂ : (l₁ l₂ : Lens A B) → R l₁ ≃ R l₂
  R₁≃R₂ l₁ l₂ = Eq.↔⇒≃ $
    Bij.bijection-from-involutive-family
      R-to-R (λ l _ → involutive l) l₁ l₂

-- An alternative proof.

Is-proposition-closed-domain′ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Lens A B)
Is-proposition-closed-domain′ {A = A} {B} univ A-prop =
                                         $⟨ Traditional.lens-preserves-h-level-of-domain 0 A-prop ⟩
  Is-proposition (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                              (_↔_.surjection $ inverse $ Lens↔Traditional-lens ⊠ univ (mono₁ 1 A-prop))
                                              1 ⟩□
  Is-proposition (Lens A B)              □

-- If A is a set, then Lens A B is also a set (assuming univalence).
--
-- TODO: Can one prove that the corresponding result does not hold for
-- codomains? Are there types A and B such that B is a set, but
-- Lens A B is not?

Is-set-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-set A → Is-set (Lens A B)
Is-set-closed-domain {A = A} {B} univ A-set =
                                 $⟨ (λ {_ _} → Traditional.lens-preserves-h-level-of-domain 1 A-set) ⟩
  Is-set (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ Lens↔Traditional-lens ⊠ univ A-set)
                                      2 ⟩□
  Is-set (Lens A B)              □

-- If A has h-level n, then Lens A B has h-level 1 + n (assuming
-- univalence).
--
-- TODO: Can this be improved? The corresponding result for
-- Traditional.Lens (Traditional.lens-preserves-h-level-of-domain) is
-- stronger.

domain-0+⇒lens-1+ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Lens A B)
domain-0+⇒lens-1+ {A = A} {B} univ n hA =
                                                  $⟨ (λ l₁ l₂ → Eq.h-level-closure ext n (hR l₁) (hR l₂)) ⟩
  ((l₁ l₂ : Lens A B) → H-level n (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ n (mono₁ n hA) ⟩□
  H-level (1 + n) (Lens A B)                      □
  where
  open Lens

  hR : ∀ l → H-level n (R l)
  hR l = remainder-has-same-h-level-as-domain l n hA

-- An alternative proof.

domain-0+⇒lens-1+′ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Lens A B)
domain-0+⇒lens-1+′ {A = A} {B} univ n hA =
                                               $⟨ Σ-closure (1 + n)
                                                    (∃-H-level-H-level-1+ ext univ n)
                                                    (λ _ → ×-closure (1 + n)
                                                             (Eq.left-closure ext n (mono₁ n hA))
                                                             (Π-closure ext (1 + n) λ _ →
                                                              mono (Nat.suc≤suc (Nat.zero≤ n)) $
                                                              truncation-is-proposition)) ⟩
  H-level (1 + n)
    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥))  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse iso) (1 + n) ⟩□

  H-level (1 + n) (Lens A B)                   □
  where
  open Lens

  iso =
    Lens A B                                             ↝⟨ inverse $ drop-⊤-right (λ l →
                                                              _⇔_.to contractible⇔↔⊤ $
                                                                propositional⇒inhabited⇒contractible
                                                                  (H-level-propositional ext n)
                                                                  (remainder-has-same-h-level-as-domain l n hA)) ⟩
    (∃ λ (l : Lens A B) → H-level n (R l))               ↝⟨ inverse Σ-assoc F.∘ Σ-cong Lens-as-Σ (λ _ → F.id) ⟩

    (∃ λ R → (A ≃ (R × B) × (R → ∥ B ∥)) × H-level n R)  ↝⟨ (∃-cong λ _ → ×-comm) ⟩

    (∃ λ R → H-level n R × A ≃ (R × B) × (R → ∥ B ∥))    ↝⟨ Σ-assoc ⟩□

    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥))            □

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens =
  Lens.Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

------------------------------------------------------------------------
-- Lens combinators

module Lens-combinators where

  -- The definition of the identity lens is unique, if the get
  -- function is required to be the identity (assuming univalence).

  id-unique :
    {A : Set a} →
    Univalence a →
    ((l₁ , _) (l₂ , _) :
       ∃ λ (l : Lens A A) → ∀ a → Lens.get l a ≡ a) →
    l₁ ≡ l₂
  id-unique {A = A} univ l₁ l₂ =
    _↔_.from (equality-characterisation₃ univ)
      ( R₁≃R₂
      , (λ _ → uncurry get≡id→remainder-propositional l₂ _ _)
      , λ a →
          get (proj₁ l₁) a  ≡⟨ proj₂ l₁ a ⟩
          a                 ≡⟨ sym $ proj₂ l₂ a ⟩∎
          get (proj₁ l₂) a  ∎
      )
    where
    open Lens

    R→R :
      (l₁ l₂ : ∃ λ (l : Lens A A) → ∀ a → get l a ≡ a) →
      R (proj₁ l₁) → R (proj₁ l₂)
    R→R (l₁ , l₁-id) (l₂ , l₂-id) r =
      Trunc.rec
        (get≡id→remainder-propositional l₂ l₂-id)
        (A         ↔⟨ equiv l₂ ⟩
         R l₂ × A  ↝⟨ proj₁ ⟩□
         R l₂      □)
        (inhabited l₁ r)

    R₁≃R₂ : R (proj₁ l₁) ≃ R (proj₁ l₂)
    R₁≃R₂ =
      _↠_.from (Eq.≃↠⇔ (uncurry get≡id→remainder-propositional l₁)
                       (uncurry get≡id→remainder-propositional l₂))
               (record { to   = R→R l₁ l₂
                       ; from = R→R l₂ l₁
                       })

  -- The result of composing two lenses is unique if the codomain type
  -- is inhabited whenever it is merely inhabited, and we require that
  -- the resulting setter function is defined in a certain way
  -- (assuming univalence).

  ∘-unique :
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
    { R         = ∥ A ∥
    ; equiv     = A          ↔⟨ inverse ∥∥×↔ ⟩□
                  ∥ A ∥ × A  □
    ; inhabited = P.id
    }

  -- Composition of lenses.
  --
  -- Note that the domains are required to be at least as large as the
  -- codomains; this should match many use-cases. Without this
  -- restriction I failed to find a satisfactory definition of
  -- composition. (I suspect that if Agda had had cumulativity, then
  -- the domain and codomain could have lived in the same universe
  -- without any problems.)
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

  -- A variant of composition for lenses between types with the same
  -- universe level.

  infixr 9 _∘_

  _∘_ :
    {A B C : Set a} →
    Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = ⟨ lzero , lzero ⟩ l₁ ∘ l₂

  -- Other definitions of composition match ⟨_,_⟩_∘_, if the codomain
  -- type is inhabited whenever it is merely inhabited, and the
  -- resulting setter function is defined in a certain way (assuming
  -- univalence).

  composition≡∘ :
    let open Lens in
    ∀ a b {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Univalence (a ⊔ b ⊔ c) →
    (∥ C ∥ → C) →
    (comp : Lens B C → Lens A B → Lens A C) →
    (∀ l₁ l₂ a c →
       set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp ≡ ⟨ a , b ⟩_∘_
  composition≡∘ _ _ univ ∥C∥→C comp set-comp =
    ∘-unique univ ∥C∥→C (comp , set-comp)
      (_ , λ { ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ → refl })

  -- Identity and composition form a kind of precategory (assuming
  -- univalence).

  associativity :
    ∀ a b c
      {A : Set (a ⊔ b ⊔ c ⊔ d)} {B : Set (b ⊔ c ⊔ d)}
      {C : Set (c ⊔ d)} {D : Set d} →
    Univalence (a ⊔ b ⊔ c ⊔ d) →
    (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ univ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ =
    _↔_.from (equality-characterisation₂ univ)
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl)

  left-identity :
    ∀ bi a {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ a , lzero ⟩ id bi ∘ l ≡ l
  left-identity ⊠ _ {B = B} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₂ univ)
      ( (R × ∥ B ∥  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl
      )
    where
    open Lens l

    lemma : R × ∥ B ∥ ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₁
          ; from = λ r → r , inhabited r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (r , _) →
          cong (λ x → r , x) $ truncation-is-proposition _ _ }
      }

  right-identity :
    ∀ bi a {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ lzero , a ⟩ l ∘ id bi ≡ l
  right-identity ⊠ _ {A = A} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₂ univ)
      ( (∥ A ∥ × R  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl
      )
    where
    open Lens l

    lemma : ∥ A ∥ × R ↔ R
    lemma = record
      { surjection = record
        { logical-equivalence = record
          { to   = proj₂
          ; from = λ r →   ∥∥-map (λ b → _≃_.from equiv (r , b))
                                  (inhabited r)
                         , r
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ { (_ , r) →
          cong (λ x → x , r) $ truncation-is-proposition _ _ }
      }

open Lens-combinators

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private
  module B {a} (b : Block "id") =
    Bi-invertibility equality-with-J (Set a) Lens (id b) _∘_
  module BM {a} (b : Block "id") (univ : Univalence a) = B.More
    b
    (left-identity b _ univ)
    (right-identity b _ univ)
    (associativity _ _ _ univ)

-- A form of isomorphism between types, expressed using lenses.

open B public using () renaming (_≅_ to [_]_≅_)

-- Lenses with quasi-inverses can be converted to equivalences.

≅→≃ : ∀ b → [ b ] A ≅ B → A ≃ B
≅→≃
  ⊠
  (l@(⟨ _ , _ , _ ⟩) , l⁻¹@(⟨ _ , _ , _ ⟩) , l∘l⁻¹≡id , l⁻¹∘l≡id) =
  Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = get l
        ; from = get l⁻¹
        }
      ; right-inverse-of = λ b → cong (λ l → get l b) l∘l⁻¹≡id
      }
    ; left-inverse-of = λ a → cong (λ l → get l a) l⁻¹∘l≡id
    })
  where
  open Lens

-- There is a split surjection from [ b ] A ≅ B to A ≃ B (assuming
-- univalence).

≅↠≃ :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  ([ b ] A ≅ B) ↠ (A ≃ B)
≅↠≃ {A = A} {B = B} b univ = record
  { logical-equivalence = record
    { to   = ≅→≃ b
    ; from = from b
    }
  ; right-inverse-of = ≅→≃∘from b
  }
  where
  from : ∀ b → A ≃ B → [ b ] A ≅ B
  from b A≃B = l , l⁻¹ , l∘l⁻¹≡id b , l⁻¹∘l≡id b
    where
    l   = ≃→lens′ A≃B
    l⁻¹ = ≃→lens′ (inverse A≃B)

    l∘l⁻¹≡id : ∀ b → l ∘ l⁻¹ ≡ id b
    l∘l⁻¹≡id ⊠ = _↔_.from (equality-characterisation₂ univ)
      ( (∥ A ∥ × ∥ B ∥  ↝⟨ Eq.⇔→≃
                             (×-closure 1 truncation-is-proposition
                                          truncation-is-proposition)
                             truncation-is-proposition
                             proj₂
                             (λ b → ∥∥-map (_≃_.from A≃B) b , b) ⟩
         ∥ B ∥          □)
      , λ _ → cong₂ _,_
               (truncation-is-proposition _ _)
               (_≃_.right-inverse-of A≃B _)
      )

    l⁻¹∘l≡id : ∀ b → l⁻¹ ∘ l ≡ id b
    l⁻¹∘l≡id ⊠ = _↔_.from (equality-characterisation₂ univ)
      ( (∥ B ∥ × ∥ A ∥  ↝⟨ Eq.⇔→≃
                             (×-closure 1 truncation-is-proposition
                                          truncation-is-proposition)
                             truncation-is-proposition
                             proj₂
                             (λ a → ∥∥-map (_≃_.to A≃B) a , a) ⟩
         ∥ A ∥          □)
      , λ _ → cong₂ _,_
                (truncation-is-proposition _ _)
                (_≃_.left-inverse-of A≃B _)
      )

  ≅→≃∘from : ∀ b A≃B → ≅→≃ b (from b A≃B) ≡ A≃B
  ≅→≃∘from ⊠ _ = Eq.lift-equality ext refl

-- There is not necessarily a split surjection from
-- Is-equivalence (Lens.get l) to B.Has-quasi-inverse l, if l is a
-- lens between types in the same universe, even if the codomain of l
-- is required to be inhabited when its remainder type is inhabited
-- (assuming univalence).

¬Is-equivalence-get↠Has-quasi-inverse :
  (b : Block "id") →
  Univalence a →
  ¬ ({A B : Set a}
     (l : Lens A B) →
     (Lens.R l → B) →
     Is-equivalence (Lens.get l) ↠ B.Has-quasi-inverse b l)
¬Is-equivalence-get↠Has-quasi-inverse b univ surj =
                                    $⟨ ⊤-contractible ⟩
  Contractible ⊤                    ↝⟨ H-level.respects-surjection lemma₃ 0 ⟩
  Contractible ((z : Z) → z ≡ z)    ↝⟨ mono₁ 0 ⟩
  Is-proposition ((z : Z) → z ≡ z)  ↝⟨ ¬-prop ⟩□
  ⊥                                 □
  where
  open Lens

  Z,¬-prop = Circle.¬-type-of-refl-propositional
  Z        = proj₁ Z,¬-prop
  ¬-prop   = proj₂ Z,¬-prop

  lemma₂ :
    ∀ b →
    (∃ λ (eq : R (id b) ≃ R (id b)) →
       (∀ z → _≃_.to eq (remainder (id b) z) ≡ remainder (id b) z)
         ×
       ((z : Z) → get (id b) z ≡ get (id b) z)) ≃
    ((z : Z) → z ≡ z)
  lemma₂ ⊠ =
    (∃ λ (eq : ∥ Z ∥ ≃ ∥ Z ∥) →
       ((z : Z) → _≃_.to eq ∣ z ∣ ≡ ∣ z ∣)
         ×
       ((z : Z) → z ≡ z))                   ↔⟨ (∃-cong λ _ → drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                Π-closure ext 0 λ _ →
                                                +⇒≡ truncation-is-proposition) ⟩

    (∥ Z ∥ ≃ ∥ Z ∥) × ((z : Z) → z ≡ z)     ↔⟨ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                               propositional⇒inhabited⇒contractible
                                                 (Eq.left-closure ext 0 truncation-is-proposition)
                                                 F.id ⟩□
    ((z : Z) → z ≡ z)                       □

  lemma₃ =
    ⊤                                                               ↔⟨ inverse $ _⇔_.to contractible⇔↔⊤ $
                                                                       propositional⇒inhabited⇒contractible
                                                                         (Eq.propositional ext _)
                                                                         (_≃_.is-equivalence Eq.id) ⟩

    Is-equivalence P.id                                             ↔⟨ ≡⇒↝ equivalence $ cong Is-equivalence $
                                                                       unblock b (λ b → _ ≡ get (id b)) refl ⟩

    Is-equivalence (get (id b))                                     ↝⟨ surj (id b) (λ _ → lift Circle.base) ⟩

    B.Has-quasi-inverse b (id b)                                    ↔⟨ BM.Has-quasi-inverse≃id≡id-domain b univ
                                                                         (id b , left-identity b _ univ _ , right-identity b _ univ _) ⟩

    id b ≡ id b                                                     ↔⟨ equality-characterisation₃ univ ⟩

    (∃ λ (eq : R (id b) ≃ R (id b)) →
       (∀ z → _≃_.to eq (remainder (id b) z) ≡ remainder (id b) z)
         ×
       (∀ z → get (id b) z ≡ get (id b) z))                         ↔⟨ lemma₂ b ⟩□

    ((z : Z) → z ≡ z)                                               □

-- See also ≃≃≅ below.

------------------------------------------------------------------------
-- Equivalences expressed using bi-invertibility for lenses

-- A form of equivalence between types, expressed using lenses.

open B public using () renaming (_≊_ to [_]_≊_; _≅_ to [_]_≅_)
open BM public using (equality-characterisation-≊)

-- Lenses with left inverses have propositional remainder types.

has-left-inverse→remainder-propositional :
  (b : Block "id")
  (l : Lens A B) →
  B.Has-left-inverse b l →
  Is-proposition (Lens.R l)
has-left-inverse→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l⁻¹∘l≡id) =
                                $⟨ get≡id→remainder-propositional
                                     (l⁻¹ ∘ l)
                                     (λ a → cong (flip get a) l⁻¹∘l≡id) ⟩
  Is-proposition (R (l⁻¹ ∘ l))  ↔⟨⟩
  Is-proposition (R l × R l⁻¹)  ↝⟨ H-level-×₁ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Lens

-- Lenses with right inverses have propositional remainder types.

has-right-inverse→remainder-propositional :
  (b : Block "id")
  (l : Lens A B) →
  B.Has-right-inverse b l →
  Is-proposition (Lens.R l)
has-right-inverse→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l∘l⁻¹≡id) =
                                $⟨ get≡id→remainder-propositional
                                     (l ∘ l⁻¹)
                                     (λ a → cong (flip get a) l∘l⁻¹≡id) ⟩
  Is-proposition (R (l ∘ l⁻¹))  ↔⟨⟩
  Is-proposition (R l⁻¹ × R l)  ↝⟨ H-level-×₂ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Lens

-- There is an equivalence between A ≃ B and [ b ] A ≊ B (assuming
-- univalence).

≃≃≊ :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (A ≃ B) ≃ ([ b ] A ≊ B)
≃≃≊ {A = A} {B = B} b univ = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to b
      ; from = from b
      }
    ; right-inverse-of = to∘from b
    }
  ; left-inverse-of = from∘to b
  })
  where
  open Lens

  to : ∀ b → A ≃ B → [ b ] A ≊ B
  to b = B.≅→≊ b ⊚ _↠_.from (≅↠≃ b univ)

  from : ∀ b → [ b ] A ≊ B → A ≃ B
  from b = _↠_.to (≅↠≃ b univ) ⊚ _↠_.from (BM.≅↠≊ b univ)

  to∘from : ∀ b A≊B → to b (from b A≊B) ≡ A≊B
  to∘from b A≊B =
    _≃_.from (equality-characterisation-≊ b univ _ _) $
    _↔_.from (equality-characterisation₃ univ)
      ( ∥B∥≃R  b A≊B
      , lemma₁ b A≊B
      , lemma₂ b A≊B
      )
    where
    l′ : ∀ b (A≊B : [ b ] A ≊ B) → Lens A B
    l′ b A≊B = proj₁ (to b (from b A≊B))

    ∥B∥≃R : ∀ b (A≊B@(l , _) : [ b ] A ≊ B) → ∥ B ∥ ≃ R l
    ∥B∥≃R b (l , (l-inv@(l⁻¹ , _) , _)) = Eq.⇔→≃
      truncation-is-proposition
      R-prop
      (Trunc.rec R-prop (remainder l ⊚ get l⁻¹))
      (inhabited l)
      where
      R-prop = has-left-inverse→remainder-propositional b l l-inv

    lemma₁ :
      ∀ b (A≊B@(l , _) : [ b ] A ≊ B) a →
      _≃_.to (∥B∥≃R b A≊B) (remainder (l′ b A≊B) a) ≡ remainder l a
    lemma₁
      ⊠
      ( l@(⟨ _ , _ , _ ⟩)
      , (l⁻¹@(⟨ _ , _ , _ ⟩) , l⁻¹∘l≡id)
      , (⟨ _ , _ , _ ⟩ , _)
      ) a =
      remainder l (get l⁻¹ (get l a))  ≡⟨⟩
      remainder l (get (l⁻¹ ∘ l) a)    ≡⟨ cong (λ l′ → remainder l (get l′ a)) l⁻¹∘l≡id ⟩
      remainder l (get (id ⊠) a)       ≡⟨⟩
      remainder l a                    ∎

    lemma₂ :
      ∀ b (A≊B@(l , _) : [ b ] A ≊ B) a →
      get (l′ b A≊B) a ≡ get l a
    lemma₂ ⊠
      (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) _ =
      refl

  from∘to :
    ∀ b A≃B →
    _↠_.to (≅↠≃ b univ) (_↠_.from (BM.≅↠≊ b univ)
      (B.≅→≊ b (_↠_.from (≅↠≃ b univ) A≃B))) ≡
    A≃B
  from∘to ⊠ _ = Eq.lift-equality ext refl

-- The right-to-left direction of ≃≃≊ maps bi-invertible lenses to
-- their getter functions.

to-from-≃≃≊≡get :
  (b : Block "id")
  (univ : Univalence a)
  (A≊B@(l , _) : [ b ] A ≊ B) →
  _≃_.to (_≃_.from (≃≃≊ b univ) A≊B) ≡ Lens.get l
to-from-≃≃≊≡get
  ⊠ _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl

-- A variant of ≃≃≊ that works even if A and B live in different
-- universes.
--
-- This variant came up in a discussion with Andrea Vezzosi.

≃≃≊′ :
  {A : Set a} {B : Set b}
  (b-id : Block "id") →
  Univalence (a ⊔ b) →
  (A ≃ B) ≃ ([ b-id ] ↑ b A ≊ ↑ a B)
≃≃≊′ {a = a} {b = b} {A = A} {B = B} b-id univ =
  A ≃ B                   ↔⟨ inverse $ Eq.≃-preserves-bijections ext Bij.↑↔ Bij.↑↔ ⟩
  ↑ b A ≃ ↑ a B           ↝⟨ ≃≃≊ b-id univ ⟩□
  [ b-id ] ↑ b A ≊ ↑ a B  □

-- The right-to-left direction of ≃≃≊′ maps bi-invertible lenses to a
-- variant of their getter functions.

to-from-≃≃≊′≡get :
  {A : Set a} {B : Set b}
  (b-id : Block "id")
  (univ : Univalence (a ⊔ b)) →
  (A≊B@(l , _) : [ b-id ] ↑ b A ≊ ↑ a B) →
  _≃_.to (_≃_.from (≃≃≊′ b-id univ) A≊B) ≡ lower ⊚ Lens.get l ⊚ lift
to-from-≃≃≊′≡get
  ⊠ _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  refl

-- The getter function of a bi-invertible lens is an equivalence
-- (assuming univalence).

Is-bi-invertible→Is-equivalence-get :
  {A : Set a}
  (b : Block "id") →
  Univalence a →
  (l : Lens A B) →
  B.Is-bi-invertible b l → Is-equivalence (Lens.get l)
Is-bi-invertible→Is-equivalence-get
  b@⊠ univ l@(⟨ _ , _ , _ ⟩)
  is-bi-inv@((⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
  _≃_.is-equivalence (_≃_.from (≃≃≊ b univ) (l , is-bi-inv))

-- If l is a lens between types in the same universe, and the codomain
-- of l is inhabited when its remainder type is inhabited, then there
-- is an equivalence between "l is bi-invertible" and "the getter of l
-- is an equivalence" (assuming univalence).

Is-bi-invertible≃Is-equivalence-get :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  (l : Lens A B) →
  B.Is-bi-invertible b l ≃ Is-equivalence (Lens.get l)
Is-bi-invertible≃Is-equivalence-get b univ l = Eq.⇔→≃
  (BM.Is-bi-invertible-propositional b univ l)
  (Eq.propositional ext _)
  (Is-bi-invertible→Is-equivalence-get b univ l)
  (λ is-equiv →

     let l′ = ≃→lens′ Eq.⟨ get l , is-equiv ⟩ in

                              $⟨ proj₂ (_≃_.to (≃≃≊ b univ) Eq.⟨ _ , is-equiv ⟩) ⟩
     B.Is-bi-invertible b l′  ↝⟨ subst (B.Is-bi-invertible b) (sym $ get-equivalence→≡≃→lens′ univ l is-equiv) ⟩□
     B.Is-bi-invertible b l   □)
  where
  open Lens

-- If A is a set, then there is an equivalence between [ b ] A ≊ B and
-- [ b ] A ≅ B (assuming univalence).

≊≃≅ :
  {A B : Set a}
  (b : Block "id") →
  Univalence a →
  Is-set A →
  ([ b ] A ≊ B) ≃ ([ b ] A ≅ B)
≊≃≅ b univ A-set =
  ∃-cong λ _ →
    BM.Is-bi-invertible≃Has-quasi-inverse-domain
      b univ
      (Is-set-closed-domain univ A-set)

------------------------------------------------------------------------
-- A category

-- If A is a set, then there is an equivalence between A ≃ B and
-- [ b ] A ≅ B (assuming univalence).

≃≃≅ :
  {A B : Set a}
  (b : Block "≃≃≅") →
  Univalence a →
  Is-set A →
  (A ≃ B) ≃ ([ b ] A ≅ B)
≃≃≅ {A = A} {B = B} b@⊠ univ A-set =
  A ≃ B        ↝⟨ ≃≃≊ b univ ⟩
  [ b ] A ≊ B  ↝⟨ ≊≃≅ b univ A-set ⟩□
  [ b ] A ≅ B  □

-- The equivalence ≃≃≅ maps identity to identity.

≃≃≅-id≡id :
  {A : Set a}
  (b : Block "≃≃≅") (univ : Univalence a) (A-set : Is-set A) →
  proj₁ (_≃_.to (≃≃≅ b univ A-set) F.id) ≡ id b
≃≃≅-id≡id ⊠ univ A-set =
  _↔_.from (equality-characterisation₂ univ)
    (F.id , λ _ → refl)

-- Lenses between sets in the same universe form a precategory
-- (assuming univalence).

private

  precategory′ :
    Block "id" →
    Univalence a →
    C.Precategory′ (lsuc a) (lsuc a)
  precategory′ {a = a} b univ =
      SET a
    , (λ (A , A-set) (B , _) →
           Lens A B
         , Is-set-closed-domain univ A-set)
    , id b
    , _∘_
    , left-identity b lzero univ _
    , right-identity b lzero univ _
    , (λ {_ _ _ _ l₁ l₂ l₃} →
         associativity lzero lzero lzero univ l₃ l₂ l₁)

precategory :
  Block "precategory" →
  Univalence a →
  Precategory (lsuc a) (lsuc a)
precategory ⊠ univ .C.Precategory.precategory =
  block λ b → precategory′ b univ

-- Lenses between sets in the same universe form a category
-- (assuming univalence).

category :
  Block "category" →
  Univalence a →
  Category (lsuc a) (lsuc a)
category ⊠ univ =
  block λ b →
  C.precategory-with-SET-to-category
    ext
    (λ _ _ → univ)
    (proj₂ $ precategory′ b univ)
    (λ (_ , A-set) _ → ≃≃≅ b univ A-set)
    (λ (_ , A-set) → ≃≃≅-id≡id b univ A-set)

-- The precategory defined here is equal to the one defined in
-- Traditional, if the latter one is lifted (assuming univalence).

precategory≡precategory :
  (b : Block "precategory") →
  Univalence (lsuc a) →
  (univ : Univalence a) →
  precategory b univ ≡
  C.lift-precategory-Hom _ Traditional.precategory
precategory≡precategory ⊠ univ⁺ univ =
  block λ b →
  _↔_.to (C.equality-characterisation-Precategory ext univ⁺ univ⁺)
    ( F.id
    , (λ (X , X-set) (Y , _) →
         Lens X Y                    ↔⟨ Lens↔Traditional-lens b univ X-set ⟩
         Traditional.Lens X Y        ↔⟨ inverse Bij.↑↔ ⟩□
         ↑ _ (Traditional.Lens X Y)  □)
    , (λ (_ , X-set) → cong lift $ _↔_.from
         (Traditional.equality-characterisation-for-sets X-set)
         refl)
    , (λ (_ , X-set) (_ , Y-set) _ (lift l₁) (lift l₂) →
         cong lift (∘-lemma b X-set Y-set l₁ l₂))
    )
  where
  ∘-lemma :
    ∀ b (A-set : Is-set A) (B-set : Is-set B)
    (l₁ : Traditional.Lens B C) (l₂ : Traditional.Lens A B) →
    Lens.traditional-lens
      (Lens↔Traditional-lens.from B-set b l₁ ∘
       Lens↔Traditional-lens.from A-set b l₂) ≡
    l₁ Traditional.Lens-combinators.∘ l₂
  ∘-lemma ⊠ A-set _ _ _ =
    _↔_.from (Traditional.equality-characterisation-for-sets A-set)
      refl

-- The category defined here is equal to the one defined in
-- Traditional, if the latter one is lifted (assuming univalence).

category≡category :
  (b : Block "category") →
  Univalence (lsuc a) →
  (univ : Univalence a) →
  category b univ ≡
  C.lift-category-Hom _ (Traditional.category univ)
category≡category b univ⁺ univ =
  _↔_.from (C.≡↔precategory≡precategory ext)
    (Category.precategory (category b univ)                  ≡⟨ lemma b ⟩

     precategory b univ                                      ≡⟨ precategory≡precategory b univ⁺ univ ⟩∎

     Category.precategory
       (C.lift-category-Hom _ (Traditional.category univ))  ∎)
  where
  lemma :
    ∀ b →
    Category.precategory (category b univ) ≡
    precategory b univ
  lemma ⊠ = refl

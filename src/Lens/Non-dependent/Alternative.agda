------------------------------------------------------------------------
-- Some alternative formulations of non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lens.Non-dependent.Alternative where

import Bi-invertibility
open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Category equality-with-J as C using (Category; Precategory)
open import Circle equality-with-paths as Circle using (𝕊¹)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
import Nat equality-with-J as Nat
open import Preimage equality-with-J
open import Surjection equality-with-J using (_↠_; module _↠_)
open import Univalence-axiom equality-with-J

import Lens.Non-dependent
import Lens.Non-dependent.Traditional as Traditional

private
  variable
    a b c d r           : Level
    A A₁ A₂ B B₁ B₂ X Y : Set a
    n                   : ℕ

------------------------------------------------------------------------
-- Alternative formulations of lenses

-- Paolo Capriotti has described higher lenses
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

Higher-lens : Set a → Set b → Set (lsuc (a ⊔ b))
Higher-lens {a = a} A B =
  ∃ λ (g : A → B) →
  ∃ λ (H : Pow a ∥ B ∥) →
    (g ⁻¹_) ≡ H ⊚ ∣_∣

-- A more traditional (?) alternative definition that uses a
-- bijection.

Bijection-lens : Set a → Set b → Set (lsuc (a ⊔ b))
Bijection-lens {a = a} {b = b} A B =
  ∃ λ (R : Set (a ⊔ b)) → A ↔ (R × B)

-- However, the definition above is not in general isomorphic to
-- Higher-lens A B or Traditional.Lens A B, not even if A and B are
-- sets (consider the case in which A and B are empty; see
-- ¬Iso-lens↠Bijection-lens below). The following variant of the
-- definition solves this problem.
--
-- (I had previously considered some other variants, when Andrea
-- Vezzosi suggested that I should look at higher lenses, and that I
-- could perhaps use R → ∥ B ∥. This worked out nicely.)
--
-- For performance reasons η-equality is turned off for this record
-- type. One can match on the constructor to block evaluation.

record Iso-lens (A : Set a) (B : Set b) : Set (lsuc (a ⊔ b)) where
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

  -- Traditional lens.

  traditional-lens : Traditional.Lens A B
  traditional-lens = record
    { get     = get
    ; set     = set
    ; get-set = get-set
    ; set-get = set-get
    ; set-set = set-set
    }

-- Yet another alternative definition of lenses. This one replaces the
-- R → ∥ B ∥ function with a requirement that the remainder function
-- should be surjective.

Iso-lens′ : Set a → Set b → Set (lsuc (a ⊔ b))
Iso-lens′ {a = a} {b = b} A B =
  ∃ λ (get       : A → B) →
  ∃ λ (R         : Set (a ⊔ b)) →
  ∃ λ (remainder : A → R) →
    Eq.Is-equivalence (λ a → remainder a , get a) ×
    Surjective remainder

------------------------------------------------------------------------
-- Simple definitions related to Iso-lenses

-- Iso-lens can be expressed as a nested Σ-type.

Iso-lens-as-Σ :
  {A : Set a} {B : Set b} →
  Iso-lens A B ↔
  ∃ λ (R : Set (a ⊔ b)) →
    (A ≃ (R × B)) ×
    (R → ∥ B ∥)
Iso-lens-as-Σ = record
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
  open Iso-lens

-- Isomorphisms can be converted into lenses.

isomorphism-to-lens :
  {A : Set a} {B : Set b} {R : Set (a ⊔ b)} →
  A ↔ R × B → Iso-lens A B
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
  A ≃ B → Iso-lens A B
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
  A ≃ B → Iso-lens A B
≃→lens′ {a = a} {A = A} {B = B} A≃B = record
  { R         = ∥ B ∥
  ; equiv     = A          ↝⟨ A≃B ⟩
                B          ↝⟨ inverse ∥∥×≃ ⟩□
                ∥ B ∥ × B  □
  ; inhabited = P.id
  }

------------------------------------------------------------------------
-- Equality characterisations for Iso-lenses

-- Equality of Iso-lenses is isomorphic to certain pairs.

equality-characterisation₀ :
  {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} =
  l₁ ≡ l₂                                                     ↔⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Iso-lens-as-Σ ⟩

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
  open Iso-lens

  l₁′ = _↔_.to Iso-lens-as-Σ l₁
  l₂′ = _↔_.to Iso-lens-as-Σ l₂

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₁ :
  {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
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
  open Iso-lens

  resp : X ≃ Y → A ≃ (X × B) → A ≃ (Y × B)
  resp {X = X} {Y = Y} X≃Y A≃X×B =
    A      ↝⟨ A≃X×B ⟩
    X × B  ↝⟨ X≃Y ×-cong F.id ⟩□
    Y × B  □

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₂ :
  {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
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
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain triples (assuming
-- univalence).

equality-characterisation₃ :
  {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
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
  open Iso-lens

-- Equality of Iso-lenses is isomorphic to certain pairs (assuming
-- univalence).

equality-characterisation₄ :
  {A : Set a} {B : Set b} {l₁ l₂ : Iso-lens A B} →
  let open Iso-lens in
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
  open Iso-lens

------------------------------------------------------------------------
-- More lens equalities

-- If two lenses have equal setters, then they also have equal
-- getters.

getters-equal-if-setters-equal :
  let open Iso-lens in
  (l₁ l₂ : Iso-lens A B) →
  set l₁ ≡ set l₂ →
  get l₁ ≡ get l₂
getters-equal-if-setters-equal l₁ l₂ setters-equal = ⟨ext⟩ λ a →
  get l₁ a                      ≡⟨ cong (get l₁) $ sym $ set-get l₂ _ ⟩
  get l₁ (set l₂ a (get l₂ a))  ≡⟨ cong (λ f → get l₁ (f a (get l₂ a))) $ sym setters-equal ⟩
  get l₁ (set l₁ a (get l₂ a))  ≡⟨ get-set l₁ _ _ ⟩∎
  get l₂ a                      ∎
  where
  open Iso-lens

-- If the codomain of a lens is inhabited when the remainder type is
-- inhabited, then this lens is equal to another lens if their setters
-- are equal (assuming univalence).

lenses-equal-if-setters-equal :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Iso-lens A B) →
  (Iso-lens.R l₁ → B) →
  Iso-lens.set l₁ ≡ Iso-lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal {A = A} {B = B}
                              univ l₁ l₂ f setters-equal =
  _↔_.from (equality-characterisation₃ univ)
    ( R≃R
    , (λ a →
         remainder l₂ (set l₁ a _)  ≡⟨ cong (remainder l₂) $ ext⁻¹ (ext⁻¹ setters-equal _) _ ⟩
         remainder l₂ (set l₂ a _)  ≡⟨ remainder-set l₂ _ _ ⟩∎
         remainder l₂ a             ∎)
    , ext⁻¹ (getters-equal-if-setters-equal l₁ l₂ setters-equal)
    )
  where
  open Iso-lens
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

  g : R l₁ → R l₂
  g r = remainder l₂ (from (equiv l₁) (r , f r))

  id-g≃ : Eq.Is-equivalence (Σ-map P.id g)
  id-g≃ = Eq.respects-extensional-equality
    (λ (b , r) →
       to BR≃BR (b , r)                              ≡⟨ to-BR≃BR _ _ _ ⟩
       b , remainder l₂ (from (equiv l₁) (r , f r))  ≡⟨⟩
       b , g r                                       ≡⟨⟩
       Σ-map P.id g (b , r)                          ∎)
    (is-equivalence BR≃BR)

  g≃ : Eq.Is-equivalence g
  g≃ r =
    Trunc.rec
      (H-level-propositional ext 0)
      (λ b → Eq.drop-Σ-map-id _ id-g≃ b r)
      (inhabited l₂ r)

  R≃R : R l₁ ≃ R l₂
  R≃R = Eq.⟨ g , g≃ ⟩

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

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Iso-lens preserves bijections.

Iso-lens-cong′ :
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  (∃ λ (R : Set r) → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥)) ↔
  (∃ λ (R : Set r) → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))
Iso-lens-cong′ A₁↔A₂ B₁↔B₂ =
  ∃-cong λ _ →
  Eq.≃-preserves-bijections ext A₁↔A₂ (F.id ×-cong B₁↔B₂)
    ×-cong
  →-cong ext F.id (∥∥-cong B₁↔B₂)

-- Iso-lens preserves level-preserving bijections.

Iso-lens-cong :
  {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  Iso-lens A₁ B₁ ↔ Iso-lens A₂ B₂
Iso-lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁↔A₂ B₁↔B₂ =
  Iso-lens A₁ B₁                          ↝⟨ Iso-lens-as-Σ ⟩
  (∃ λ R → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥))  ↝⟨ Iso-lens-cong′ A₁↔A₂ B₁↔B₂ ⟩
  (∃ λ R → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))  ↝⟨ inverse Iso-lens-as-Σ ⟩□
  Iso-lens A₂ B₂                          □

-- If B is a proposition, then Iso-lens A B is isomorphic to A → B
-- (assuming univalence).

lens-to-proposition↔get :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Iso-lens A B ↔ (A → B)
lens-to-proposition↔get {b = b} {A = A} {B = B} univ B-prop =
  Iso-lens A B                         ↝⟨ Iso-lens-as-Σ ⟩
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

-- If B is contractible, then Iso-lens A B is isomorphic to ⊤
-- (assuming univalence).

lens-to-contractible↔⊤ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B →
  Iso-lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} univ cB =
  Iso-lens A B  ↝⟨ lens-to-proposition↔get univ (mono₁ 0 cB) ⟩
  (A → B)       ↝⟨ →-cong ext F.id $ _⇔_.to contractible⇔↔⊤ cB ⟩
  (A → ⊤)       ↝⟨ →-right-zero ⟩□
  ⊤             □

-- Iso-lens A ⊥ is isomorphic to ¬ A (assuming univalence).

lens-to-⊥↔¬ :
  {A : Set a} →
  Univalence (a ⊔ b) →
  Iso-lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔¬ {A = A} univ =
  Iso-lens A ⊥  ↝⟨ lens-to-proposition↔get univ ⊥-propositional ⟩
  (A → ⊥)       ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A           □

-- If A is contractible, then Iso-lens A B is isomorphic to
-- Contractible B (assuming univalence).

lens-from-contractible↔codomain-contractible :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible A →
  Iso-lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible {A = A} {B} univ cA =
  Iso-lens A B                                               ↝⟨ Iso-lens-as-Σ ⟩
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

-- Iso-lens ⊥ B is isomorphic to the unit type (assuming univalence).

lens-from-⊥↔⊤ :
  {B : Set b} →
  Univalence (a ⊔ b) →
  Iso-lens (⊥ {ℓ = a}) B ↔ ⊤
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
  open Iso-lens

  lemma : (l : Iso-lens ⊥ B) → ⊥₀ ↔ R l
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

-- Bijection-lens ⊥ ⊥ is isomorphic to Set something.

Bijection-lens-⊥-⊥↔Set :
  Bijection-lens (⊥ {ℓ = a}) (⊥ {ℓ = b}) ↔ Set (a ⊔ b)
Bijection-lens-⊥-⊥↔Set =
  Bijection-lens ⊥ ⊥     ↔⟨ (∃-cong λ _ → Eq.↔↔≃ ext (mono₁ 1 ⊥-propositional)) ⟩
  (∃ λ R → ⊥ ≃ (R × ⊥))  ↔⟨ (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id ×-right-zero) ⟩
  (∃ λ R → ⊥ ≃ ⊥₀)       ↔⟨ (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ R → ¬ ⊥)          ↔⟨ drop-⊤-right (λ _ → ¬⊥↔⊤ {k = bijection} ext) ⟩□
  Set _                  □

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- Higher-lens A B is isomorphic to Iso-lens A B (assuming
-- univalence).
--
-- (This proof was simplified following a suggestion by Paolo
-- Capriotti.)

Higher-lens↔Iso-lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Higher-lens A B ↔ Iso-lens A B
Higher-lens↔Iso-lens {a = a} {b = b} {A = A} {B = B} univ =

  (∃ λ (g : A → B) → ∃ λ (H : Pow a ∥ B ∥) →
     (g ⁻¹_) ≡ H ⊚ ∣_∣)                                            ↔⟨ Σ-cong lemma₂ (λ _ → ∃-cong (lemma₃ _)) ⟩

  (∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
   ∃ λ (H : Pow a ∥ B ∥) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ ∃-comm ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (p : ∃ λ (P : Pow a B) → A ≃ ∃ P) →
     proj₁ p ≡ H ⊚ ∣_∣)                                            ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      A ≃ ∃ P × P ≡ H ⊚ ∣_∣)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ P)                                       ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq →
                                                                       Eq.≃-preserves ext F.id (∃-cong λ x → ≡⇒↝ _ (cong (_$ x) eq))) ⟩
  (∃ λ (H : Pow a ∥ B ∥) →
   ∃ λ (P : Pow a B) →
      P ≡ H ⊚ ∣_∣ × A ≃ ∃ (H ⊚ ∣_∣))                               ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (∃ λ (H : Pow a ∥ B ∥) →
   (∃ λ (P : Pow a B) → P ≡ H ⊚ ∣_∣) ×
   A ≃ ∃ (H ⊚ ∣_∣))                                                ↝⟨ (∃-cong λ _ →
                                                                       drop-⊤-left-× λ _ →
                                                                       _⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

  (∃ λ (H : Pow a ∥ B ∥) → A ≃ ∃ (H ⊚ ∣_∣))                        ↔⟨ inverse $
                                                                      Σ-cong (inverse $ Pow↔Fam a ext univ) (λ _ →
                                                                      Eq.≃-preserves ext F.id F.id) ⟩

  (∃ λ (H : Fam a ∥ B ∥) → A ≃ ∃ ((proj₂ H ⁻¹_) ⊚ ∣_∣))            ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (R : Set ℓ) →
   ∃ λ (f : R → ∥ B ∥) → A ≃ ∃ ((f ⁻¹_) ⊚ ∣_∣))                    ↔⟨ (∃-cong λ R → ∃-cong λ f →
                                                                       Eq.≃-preserves ext F.id
                            (∃ ((f ⁻¹_) ⊚ ∣_∣)                           ↔⟨ (∃-cong λ b → drop-⊤-right λ r →
                                                                               _⇔_.to contractible⇔↔⊤ $
                                                                                 +⇒≡ truncation-is-proposition) ⟩
                             B × R                                       ↔⟨ ×-comm ⟩□
                             R × B                                       □)) ⟩

  (∃ λ (R : Set ℓ) → (R → ∥ B ∥) × (A ≃ (R × B)))                  ↝⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (R : Set ℓ) → (A ≃ (R × B)) × (R → ∥ B ∥))                  ↝⟨ inverse Iso-lens-as-Σ ⟩□

  Iso-lens A B                                                     □

  where
  ℓ = a ⊔ b

  lemma₁ : ∀ (g : A → B) b →
           g ⁻¹ b ↔ (g ⊚ lower {ℓ = ℓ}) ⁻¹ b
  lemma₁ g b = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ { (a , ga≡b) → lift a , ga≡b }
        ; from = λ { (lift a , ga≡b) → a , ga≡b }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

  abstract

    lemma₂ : (A → B) ↔ ∃ λ (P : Pow a B) → A ≃ ∃ P
    lemma₂ = →↔Σ≃Σ ℓ ext univ

    lemma₃ :
      (g : A → B) (H : Pow a ∥ B ∥) →
      ((g ⁻¹_) ≡ H ⊚ ∣_∣)
        ≃
      (proj₁ (_↔_.to lemma₂ g) ≡ H ⊚ ∣_∣)
    lemma₃ g H =
      (g ⁻¹_) ≡ H ⊚ ∣_∣                   ↝⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
      (∀ b → g ⁻¹ b ≡ H ∣ b ∣)            ↝⟨ ∀-cong ext (λ _ →
                                               ≡-preserves-≃ ext univ univ
                                                 (Eq.↔⇒≃ $ lemma₁ _ _) F.id) ⟩
      (∀ b → (g ⊚ lower) ⁻¹ b ≡ H ∣ b ∣)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□
      ((g ⊚ lower) ⁻¹_) ≡ H ⊚ ∣_∣         □

-- Iso-lens A B is isomorphic to Iso-lens′ A B.

Iso-lens↔Iso-lens′ :
  {A : Set a} {B : Set b} →
  Iso-lens A B ↔ Iso-lens′ A B
Iso-lens↔Iso-lens′ {A = A} {B} =

  Iso-lens A B                                            ↝⟨ Iso-lens-as-Σ ⟩

  (∃ λ (R : Set _) →
     (A ≃ (R × B)) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Eq.≃-as-Σ ×-cong F.id) ⟩

  (∃ λ (R : Set _) →
     (∃ λ (f : A → R × B) → Eq.Is-equivalence f) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (f : A → R × B) →
     Eq.Is-equivalence f ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → Σ-cong ΠΣ-comm λ _ → F.id) ⟩

  (∃ λ (R  : Set _) →
   ∃ λ (rg : (A → R) × (A → B)) →
     Eq.Is-equivalence (λ a → proj₁ rg a , proj₂ rg a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
   ∃ λ (get       : A → B) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R         : Set _) →
   ∃ λ (get       : A → B) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ ∃-comm ⟩

  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     (R → ∥ B ∥))                                         ↝⟨ (∃-cong λ get → ∃-cong λ R → ∃-cong λ rem → ∃-cong λ eq →
                                                              ∀-cong ext λ _ → ∥∥-cong $
                                                              lemma get R rem eq _) ⟩□
  (∃ λ (get       : A → B) →
   ∃ λ (R         : Set _) →
   ∃ λ (remainder : A → R) →
     Eq.Is-equivalence (λ a → remainder a , get a) ×
     Surjective remainder)                                □

  where
  lemma : ∀ _ _ _ _ _ → _
  lemma = λ _ _ remainder eq r →
    B                            ↝⟨ (inverse $ drop-⊤-right λ _ →
                                     _⇔_.to contractible⇔↔⊤ $
                                     singleton-contractible _) ⟩
    B × Singleton r              ↝⟨ Σ-assoc ⟩
    (∃ λ { (_ , r′) → r′ ≡ r })  ↝⟨ (Σ-cong ×-comm λ _ → F.id) ⟩
    (∃ λ { (r′ , _) → r′ ≡ r })  ↝⟨ (inverse $ Σ-cong Eq.⟨ _ , eq ⟩ λ _ → F.id) ⟩□
    (∃ λ a → remainder a ≡ r)    □

-- The remainder function of an Iso-lens is surjective.

remainder-surjective :
  (l : Iso-lens A B) → Surjective (Iso-lens.remainder l)
remainder-surjective l =
  proj₂ $ proj₂ $ proj₂ $ proj₂ $ _↔_.to Iso-lens↔Iso-lens′ l

-- There is a split surjection from Bijections-lens A B to
-- Iso-lens A B (assuming univalence).

Bijection-lens↠Iso-lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Bijection-lens A B ↠ Iso-lens A B
Bijection-lens↠Iso-lens {A = A} {B} univ = record
  { logical-equivalence = record
    { to   = λ { (R , A↔R×B) → isomorphism-to-lens A↔R×B }
    ; from = λ { l → R l , _≃_.bijection (equiv l) }
    }
  ; right-inverse-of = λ { l →
      _↔_.from (equality-characterisation₂ univ)
        ( (R l × ∥ B ∥  ↔⟨ drop-⊤-right (λ r → inhabited⇒∥∥↔⊤ (inhabited l r)) ⟩□
           R l          □)
        , λ _ → refl
        ) }
  }
  where
  open Iso-lens

-- However, there is in general no split surjection in the other
-- direction, not even for sets (assuming univalence).

¬Iso-lens↠Bijection-lens :
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Is-set A → Is-set B →
     Iso-lens A B ↠ Bijection-lens A B)
¬Iso-lens↠Bijection-lens univ surj =
  ⊥-elim (subst F.id ⊤≡⊥ _)
  where
  ⊥-is-set : ∀ {ℓ} → Is-set (⊥ {ℓ = ℓ})
  ⊥-is-set = mono₁ 1 ⊥-propositional

  ⊤↠Set =
    ⊤                   ↔⟨ inverse $ lens-from-⊥↔⊤ univ ⟩
    Iso-lens ⊥ ⊥        ↝⟨ surj ⊥-is-set ⊥-is-set ⟩
    Bijection-lens ⊥ ⊥  ↔⟨ Bijection-lens-⊥-⊥↔Set ⟩□
    Set _               □

  ⊤≡⊥ : ↑ _ ⊤ ≡ ⊥
  ⊤≡⊥ =
    ↑ _ ⊤              ≡⟨ sym $ right-inverse-of _ ⟩
    to (from (↑ _ ⊤))  ≡⟨⟩
    to (from ⊥)        ≡⟨ right-inverse-of _ ⟩∎
    ⊥                  ∎
    where
    open _↠_ ⊤↠Set

-- In general there is no split surjection from Iso-lens A B to
-- Traditional.Lens A B (assuming univalence).

¬Iso-lens↠Traditional-lens :
  Univalence lzero →
  Univalence a →
  ∃ λ (A : Set a) →
    ¬ (Iso-lens A ⊤ ↠ Traditional.Lens A ⊤)
¬Iso-lens↠Traditional-lens univ₀ univ =
  let A = _ in

  A ,
  (λ surj →                                 $⟨ _⇔_.from contractible⇔↔⊤ (lens-to-contractible↔⊤ univ ⊤-contractible) ⟩
     Contractible (Iso-lens A ⊤)            ↝⟨ H-level.respects-surjection surj 0 ⟩
     Contractible (Traditional.Lens A ⊤)    ↝⟨ mono₁ 0 ⟩
     Is-proposition (Traditional.Lens A ⊤)  ↝⟨ proj₂ $ Traditional.¬-lens-to-⊤-propositional univ₀ ⟩□
     ⊥                                      □)

-- Some lemmas used in Iso-lens↠Traditional-lens and
-- Iso-lens↔Traditional-lens below.

private

  module Iso-lens↔Traditional-lens
    {A : Set a} {B : Set b}
    (A-set : Is-set A)
    where

    from : Block "conversion" → Traditional.Lens A B → Iso-lens A B
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

    to∘from : ∀ bc l → Iso-lens.traditional-lens (from bc l) ≡ l
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
      ∀ bc l → from bc (Iso-lens.traditional-lens l) ≡ l
    from∘to univ ⊠ l′ =
      _↔_.from (equality-characterisation₄ univ)
               (lemma , λ _ → refl)
      where
      open Iso-lens l′ renaming (equiv to l)

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
      Iso-lens A B ↔ Traditional.Lens A B
    iso bc univ = record
      { surjection = record
        { logical-equivalence = record { from = from bc }
        ; right-inverse-of    = to∘from bc
        }
      ; left-inverse-of = from∘to univ bc
      }

-- If the domain A is a set, then there is a split surjection from
-- Iso-lens A B to Traditional.Lens A B.

Iso-lens↠Traditional-lens :
  Block "conversion" →
  Is-set A →
  Iso-lens A B ↠ Traditional.Lens A B
Iso-lens↠Traditional-lens {A = A} {B = B} bc A-set = record
  { logical-equivalence = record
    { to   = Iso-lens.traditional-lens
    ; from = Iso-lens↔Traditional-lens.from A-set bc
    }
  ; right-inverse-of = Iso-lens↔Traditional-lens.to∘from A-set bc
  }

-- If the domain A is a set, then Traditional.Lens A B and
-- Iso-lens A B are isomorphic (assuming univalence).

Iso-lens↔Traditional-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Is-set A →
  Iso-lens A B ↔ Traditional.Lens A B
Iso-lens↔Traditional-lens bc univ A-set =
  Iso-lens↔Traditional-lens.iso A-set bc univ

-- If the domain A is a set, then Traditional.Lens A B and
-- Higher-lens A B are isomorphic (assuming univalence).

Higher-lens↔Traditional-lens :
  {A : Set a} {B : Set b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Is-set A →
  Higher-lens A B ↔ Traditional.Lens A B
Higher-lens↔Traditional-lens {A = A} {B} bc univ A-set =
  Higher-lens A B       ↝⟨ Higher-lens↔Iso-lens univ ⟩
  Iso-lens A B          ↝⟨ Iso-lens↔Traditional-lens bc univ A-set ⟩□
  Traditional.Lens A B  □

-- If the codomain B is an inhabited set, then Iso-lens A B and
-- Traditional.Lens A B are logically equivalent.
--
-- This definition is inspired by the statement of Corollary 13 from
-- "Algebras and Update Strategies" by Johnson, Rosebrugh and Wood.

Iso-lens⇔Traditional-lens :
  Is-set B →
  B →
  Iso-lens A B ⇔ Traditional.Lens A B
Iso-lens⇔Traditional-lens {B = B} {A = A} B-set b₀ = record
  { to   = Iso-lens.traditional-lens
  ; from = from
  }
  where
  from : Traditional.Lens A B → Iso-lens A B
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
-- Some Iso-lens results related to h-levels

-- If the domain of an Iso-lens is inhabited and has h-level n, then
-- the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  Iso-lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} {n = n} l a =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ proj₂-closure (remainder a) n ⟩□
  H-level n B        □
  where
  open Iso-lens l

-- This is not necessarily true for arbitrary domains (assuming
-- univalence).

¬-h-level-respects-lens :
  Univalence (a ⊔ b) →
  ¬ (∀ n {A : Set a} {B : Set b} →
     Iso-lens A B → H-level n A → H-level n B)
¬-h-level-respects-lens univ resp =
                             $⟨ ⊥-propositional ⟩
  Is-proposition ⊥           ↝⟨ resp 1 (_↔_.from (lens-from-⊥↔⊤ univ) _) ⟩
  Is-proposition (↑ _ Bool)  ↝⟨ ↑⁻¹-closure 1 ⟩
  Is-proposition Bool        ↝⟨ ¬-Bool-propositional ⟩□
  ⊥₀                         □

-- In fact, there is an Iso-lens with a proposition as its domain and
-- a non-set as its codomain (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-𝕊¹-set.)

lens-from-proposition-to-non-set :
  Univalence (# 0) →
  ∃ λ (A : Set a) → ∃ λ (B : Set b) →
  Iso-lens A B × Is-proposition A × ¬ Is-set B
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

-- Iso-lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  Iso-lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited l (proj₁ c) c

-- If the domain type of an Iso-lens is contractible, then the
-- remainder type is also contractible.

domain-contractible⇒remainder-contractible :
  (l : Iso-lens A B) → Contractible A → Contractible (Iso-lens.R l)
domain-contractible⇒remainder-contractible {A = A} {B = B} l =
  Contractible A                   ↔⟨ H-level-cong {k₂ = equivalence} ext 0 equiv ⟩
  Contractible (R × B)             ↔⟨ Contractible-commutes-with-× {k = bijection} ext ⟩
  Contractible R × Contractible B  ↝⟨ proj₁ ⟩□
  Contractible R                   □
  where
  open Iso-lens l

-- If the domain type of an Iso-lens has h-level n, then the remainder
-- type also has h-level n.

remainder-has-same-h-level-as-domain :
  (l : Iso-lens A B) → ∀ n → H-level n A → H-level n (Iso-lens.R l)
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
  open Iso-lens l

-- If the getter function is an equivalence and there is a function
-- from the remainder type to the codomain, then the remainder type is
-- propositional.

get-equivalence→remainder-propositional :
  (l : Iso-lens A B) →
  Is-equivalence (Iso-lens.get l) →
  (Iso-lens.R l → B) →
  Is-proposition (Iso-lens.R l)
get-equivalence→remainder-propositional l is-equiv f r₁ r₂ =
  r₁                       ≡⟨ lemma _ ⟩
  remainder (from A≃B b′)  ≡⟨ sym $ lemma _ ⟩∎
  r₂                       ∎
  where
  open _≃_
  open Iso-lens l

  b′ = f r₁

  A≃B = Eq.⟨ _ , is-equiv ⟩

  lemma : ∀ r → r ≡ remainder (from A≃B b′)
  lemma r =
    r                                                              ≡⟨ cong proj₁ $ sym $ right-inverse-of equiv _ ⟩
    proj₁ (to equiv (from equiv (r , b′)))                         ≡⟨ cong (proj₁ ⊚ to equiv) $ sym $ left-inverse-of A≃B _ ⟩
    proj₁ (to equiv (from A≃B (to A≃B (from equiv (r , b′)))))     ≡⟨⟩
    remainder (from A≃B (proj₂ (to equiv (from equiv (r , b′)))))  ≡⟨ cong (remainder ⊚ from A≃B ⊚ proj₂) $ right-inverse-of equiv _ ⟩∎
    remainder (from A≃B b′)                                        ∎

-- When the conditions of the previous lemma are satisfied the lens is
-- equal to a lens formed using the equivalence (assuming univalence).

get-equivalence→≡≃→lens :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  (l : Iso-lens A B) →
  (eq : Is-equivalence (Iso-lens.get l)) →
  (Iso-lens.R l → B) →
  l ≡ ≃→lens Eq.⟨ Iso-lens.get l , eq ⟩
get-equivalence→≡≃→lens {A = A} {B = B} univ l eq f =
  _↔_.from (equality-characterisation₃ univ)
    ( R≃∥B∥
    , (λ _ → truncation-is-proposition _ _)
    , (λ _ → refl)
    )
  where
  open Iso-lens

  A≃B : A ≃ B
  A≃B = Eq.⟨ _ , eq ⟩

  R≃∥B∥ : R l ≃ ∥ ↑ _ B ∥
  R≃∥B∥ = Eq.⇔→≃
    R-prop
    truncation-is-proposition
    (∥∥-map lift ⊚ inhabited l)
    (Trunc.rec R-prop (remainder l ⊚ _≃_.from A≃B ⊚ lower))
    where
    R-prop = get-equivalence→remainder-propositional l eq f

-- A variant of get-equivalence→≡≃→lens.

get-equivalence→≡≃→lens′ :
  {A B : Set a} →
  Univalence a →
  (l : Iso-lens A B) →
  (eq : Is-equivalence (Iso-lens.get l)) →
  (Iso-lens.R l → B) →
  l ≡ ≃→lens′ Eq.⟨ Iso-lens.get l , eq ⟩
get-equivalence→≡≃→lens′ {A = A} {B = B} univ l eq f =
  l            ≡⟨ get-equivalence→≡≃→lens univ _ _ f ⟩
  ≃→lens A≃B   ≡⟨ ≃→lens≡≃→lens′ univ _ ⟩∎
  ≃→lens′ A≃B  ∎
  where
  A≃B = Eq.⟨ Iso-lens.get l , eq ⟩

-- If the getter function is pointwise equal to the identity
-- function, then the remainder type is propositional.

get≡id→remainder-propositional :
  (l : Iso-lens A A) →
  (∀ a → Iso-lens.get l a ≡ a) →
  Is-proposition (Iso-lens.R l)
get≡id→remainder-propositional l get≡id =
  [inhabited⇒+]⇒+ 0 λ r →
    Trunc.rec
      (H-level-propositional ext 1)
      (λ a r₁ r₂ → cong proj₁ (
         (r₁ , a)        ≡⟨ sym $ to-lemma a r₁ ⟩
         _≃_.to equiv a  ≡⟨ to-lemma a r₂ ⟩∎
         (r₂ , a)        ∎))
      (inhabited r)
  where
  open Iso-lens l

  from-lemma : ∀ r a → _≃_.from equiv (r , a) ≡ a
  from-lemma r a =
    _≃_.from equiv (r , a)                                 ≡⟨ cong (λ a′ → _≃_.from equiv (proj₁ a′ , a)) $ sym $
                                                                _≃_.right-inverse-of equiv _ ⟩
    _≃_.from equiv
      (proj₁ (_≃_.to equiv (_≃_.from equiv (r , a))) , a)  ≡⟨⟩

    set (_≃_.from equiv (r , a)) a                         ≡⟨ sym $ get≡id _ ⟩

    get (set (_≃_.from equiv (r , a)) a)                   ≡⟨ get-set _ _ ⟩∎

    a                                                      ∎

  to-lemma : ∀ a r → _≃_.to equiv a ≡ (r , a)
  to-lemma a r =
    _≃_.to equiv a                         ≡⟨ cong (_≃_.to equiv) $ sym $ from-lemma r a ⟩
    _≃_.to equiv (_≃_.from equiv (r , a))  ≡⟨ _≃_.right-inverse-of equiv (r , a) ⟩∎
    (r , a)                                ∎

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Iso-lens A B (assuming univalence).

¬-Contractible-closed-domain :
  ∀ {a b} →
  Univalence (a ⊔ b) →
  ¬ ({A : Set a} {B : Set b} →
     Contractible A → Contractible (Iso-lens A B))
¬-Contractible-closed-domain univ closure =
                                     $⟨ ↑⊤-contractible ⟩
  Contractible (↑ _ ⊤)               ↝⟨ closure ⟩
  Contractible (Iso-lens (↑ _ ⊤) ⊥)  ↝⟨ H-level.respects-surjection
                                          (_↔_.surjection $ lens-from-contractible↔codomain-contractible univ ↑⊤-contractible)
                                          0 ⟩
  Contractible (Contractible ⊥)      ↝⟨ proj₁ ⟩
  Contractible ⊥                     ↝⟨ proj₁ ⟩
  ⊥                                  ↝⟨ ⊥-elim ⟩□
  ⊥₀                                 □
  where
  ↑⊤-contractible = ↑-closure 0 ⊤-contractible

-- Contractible is closed under Iso-lens A (assuming univalence).

Contractible-closed-codomain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Contractible B → Contractible (Iso-lens A B)
Contractible-closed-codomain {A = A} {B} univ cB =
                               $⟨ lens-to-contractible↔⊤ univ cB ⟩
  Iso-lens A B ↔ ⊤             ↝⟨ _⇔_.from contractible⇔↔⊤ ⟩□
  Contractible (Iso-lens A B)  □

-- If B is a proposition, then Iso-lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-codomain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition B → Is-proposition (Iso-lens A B)
Is-proposition-closed-codomain {A = A} {B} univ B-prop =
                                 $⟨ Π-closure ext 1 (λ _ → B-prop) ⟩
  Is-proposition (A → B)         ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ lens-to-proposition↔get univ B-prop)
                                      1 ⟩□
  Is-proposition (Iso-lens A B)  □

private

  -- If A has h-level 1 + n and equivalence between certain remainder
  -- types has h-level n, then Iso-lens A B has h-level 1 + n
  -- (assuming univalence).

  domain-1+-remainder-equivalence-0+⇒lens-1+ :
    {A : Set a} {B : Set b} →
    Univalence (a ⊔ b) →
    ∀ n →
    H-level (1 + n) A →
    ((l₁ l₂ : Iso-lens A B) →
       H-level n (Iso-lens.R l₁ ≃ Iso-lens.R l₂)) →
    H-level (1 + n) (Iso-lens A B)
  domain-1+-remainder-equivalence-0+⇒lens-1+
    {A = A} univ n hA hR = ≡↔+ _ _ λ l₁ l₂ →                    $⟨ Σ-closure n (hR l₁ l₂) (λ _ →
                                                                   Π-closure ext n λ _ →
                                                                   +⇒≡ hA) ⟩
    H-level n (∃ λ (eq : R l₁ ≃ R l₂) → ∀ p → _≡_ {A = A} _ _)  ↝⟨ H-level.respects-surjection
                                                                     (_↔_.surjection $ inverse $ equality-characterisation₄ univ)
                                                                     n ⟩□
    H-level n (l₁ ≡ l₂)                                         □
    where
    open Iso-lens

-- If A is a proposition, then Iso-lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Iso-lens A B)
Is-proposition-closed-domain {b = b} {A = A} {B = B} univ A-prop =
                                          $⟨ R₁≃R₂ ⟩
  (∀ l₁ l₂ → R l₁ ≃ R l₂)                 ↝⟨ (λ hyp l₁ l₂ → propositional⇒inhabited⇒contractible
                                                              (Eq.left-closure ext 0 (R-prop l₁))
                                                              (hyp l₁ l₂)) ⟩
  (∀ l₁ l₂ → Contractible (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ 0 A-prop ⟩□
  Is-proposition (Iso-lens A B)           □
  where
  open Iso-lens

  R-prop : (l : Iso-lens A B) → Is-proposition (R l)
  R-prop l =
    remainder-has-same-h-level-as-domain l 1 A-prop

  remainder⁻¹ : (l : Iso-lens A B) → R l → A
  remainder⁻¹ l r =
    rec A-prop
        (λ b → _≃_.from (equiv l) (r , b))
        (inhabited l r)

  R-to-R : (l₁ l₂ : Iso-lens A B) → R l₁ → R l₂
  R-to-R l₁ l₂ = remainder l₂ ⊚ remainder⁻¹ l₁

  involutive : (l : Iso-lens A B) {f : R l → R l} → ∀ r → f r ≡ r
  involutive l _ = R-prop l _ _

  R₁≃R₂ : (l₁ l₂ : Iso-lens A B) → R l₁ ≃ R l₂
  R₁≃R₂ l₁ l₂ = Eq.↔⇒≃ $
    Bij.bijection-from-involutive-family
      R-to-R (λ l _ → involutive l) l₁ l₂

-- An alternative proof.

Is-proposition-closed-domain′ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-proposition A → Is-proposition (Iso-lens A B)
Is-proposition-closed-domain′ {A = A} {B} univ A-prop =
                                         $⟨ Traditional.lens-preserves-h-level-of-domain 0 A-prop ⟩
  Is-proposition (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                              (_↔_.surjection $ inverse $ Iso-lens↔Traditional-lens ⊠ univ (mono₁ 1 A-prop))
                                              1 ⟩□
  Is-proposition (Iso-lens A B)          □

-- If A is a set, then Iso-lens A B is also a set (assuming
-- univalence).
--
-- TODO: Can one prove that the corresponding result does not hold for
-- codomains? Are there types A and B such that B is a set, but
-- Iso-lens A B is not?

Is-set-closed-domain :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  Is-set A → Is-set (Iso-lens A B)
Is-set-closed-domain {A = A} {B} univ A-set =
                                 $⟨ (λ {_ _} → Traditional.lens-preserves-h-level-of-domain 1 A-set) ⟩
  Is-set (Traditional.Lens A B)  ↝⟨ H-level.respects-surjection
                                      (_↔_.surjection $ inverse $ Iso-lens↔Traditional-lens ⊠ univ A-set)
                                      2 ⟩□
  Is-set (Iso-lens A B)          □

-- If A has h-level n, then Iso-lens A B has h-level 1 + n (assuming
-- univalence).
--
-- TODO: Can this be improved? The corresponding result for
-- Traditional.Lens (Traditional.lens-preserves-h-level-of-domain) is
-- stronger.

domain-0+⇒lens-1+ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
domain-0+⇒lens-1+ {A = A} {B} univ n hA =
                                                      $⟨ (λ l₁ l₂ → Eq.h-level-closure ext n (hR l₁) (hR l₂)) ⟩
  ((l₁ l₂ : Iso-lens A B) → H-level n (R l₁ ≃ R l₂))  ↝⟨ domain-1+-remainder-equivalence-0+⇒lens-1+ univ n (mono₁ n hA) ⟩□
  H-level (1 + n) (Iso-lens A B)                      □
  where
  open Iso-lens

  hR : ∀ l → H-level n (R l)
  hR l = remainder-has-same-h-level-as-domain l n hA

-- An alternative proof.

domain-0+⇒lens-1+′ :
  {A : Set a} {B : Set b} →
  Univalence (a ⊔ b) →
  ∀ n → H-level n A → H-level (1 + n) (Iso-lens A B)
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

  H-level (1 + n) (Iso-lens A B)               □
  where
  open Iso-lens

  iso =
    Iso-lens A B                                         ↝⟨ inverse $ drop-⊤-right (λ l →
                                                              _⇔_.to contractible⇔↔⊤ $
                                                                propositional⇒inhabited⇒contractible
                                                                  (H-level-propositional ext n)
                                                                  (remainder-has-same-h-level-as-domain l n hA)) ⟩
    (∃ λ (l : Iso-lens A B) → H-level n (R l))           ↝⟨ inverse Σ-assoc F.∘ Σ-cong Iso-lens-as-Σ (λ _ → F.id) ⟩

    (∃ λ R → (A ≃ (R × B) × (R → ∥ B ∥)) × H-level n R)  ↝⟨ (∃-cong λ _ → ×-comm) ⟩

    (∃ λ R → H-level n R × A ≃ (R × B) × (R → ∥ B ∥))    ↝⟨ Σ-assoc ⟩□

    (∃ λ (p : ∃ (H-level n)) →
       A ≃ (proj₁ p × B) × (proj₁ p → ∥ B ∥))            □

------------------------------------------------------------------------
-- An existence result

-- There is, in general, no Iso-lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Iso-lens (Σ A B) A
no-first-projection-lens =
  Lens.Non-dependent.no-first-projection-lens
    Iso-lens contractible-to-contractible

------------------------------------------------------------------------
-- Iso-lens combinators

module Iso-lens-combinators where

  -- The definition of the identity lens is unique, if the get
  -- function is required to be the identity (assuming univalence).

  id-unique :
    {A : Set a} →
    Univalence a →
    ((l₁ , _) (l₂ , _) :
       ∃ λ (l : Iso-lens A A) → ∀ a → Iso-lens.get l a ≡ a) →
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
    open Iso-lens

    R→R :
      (l₁ l₂ : ∃ λ (l : Iso-lens A A) → ∀ a → get l a ≡ a) →
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
    let open Iso-lens in
    {A : Set a} {C : Set c} →
    Univalence (a ⊔ c) →
    (∥ C ∥ → C) →
    ((comp₁ , _) (comp₂ , _) :
       ∃ λ (comp : Iso-lens B C → Iso-lens A B → Iso-lens A C) →
         ∀ l₁ l₂ a c →
           set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp₁ ≡ comp₂
  ∘-unique {A = A} {C = C} univ ∥C∥→C
           (comp₁ , set₁) (comp₂ , set₂) =
    ⟨ext⟩ λ l₁ → ⟨ext⟩ λ l₂ →
      lenses-equal-if-setters-equal univ
        (comp₁ l₁ l₂) (comp₂ l₁ l₂) (∥C∥→C ⊚ inhabited (comp₁ l₁ l₂)) $
        ⟨ext⟩ λ a → ⟨ext⟩ λ c →
          set (comp₁ l₁ l₂) a c           ≡⟨ set₁ _ _ _ _ ⟩
          set l₂ a (set l₁ (get l₂ a) c)  ≡⟨ sym $ set₂ _ _ _ _ ⟩∎
          set (comp₂ l₁ l₂) a c           ∎
    where
    open Iso-lens

  -- Identity lens.

  id : Block "id" → Iso-lens A A
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
    Iso-lens B C → Iso-lens A B → Iso-lens A C
  ⟨_,_⟩_∘_ _ _ {A = A} {B} {C} l₁@(⟨ _ , _ , _ ⟩) l₂@(⟨ _ , _ , _ ⟩) = record
    { R         = R l₂ × R l₁
    ; equiv     = A                  ↝⟨ equiv l₂ ⟩
                  R l₂ × B           ↝⟨ F.id ×-cong equiv l₁ ⟩
                  R l₂ × (R l₁ × C)  ↔⟨ ×-assoc ⟩□
                  (R l₂ × R l₁) × C  □
    ; inhabited = ∥∥-map (get l₁) ⊚ inhabited l₂ ⊚ proj₁
    }
    where
    open Iso-lens

  -- A variant of composition for lenses between types with the same
  -- universe level.

  infixr 9 _∘_

  _∘_ :
    {A B C : Set a} →
    Iso-lens B C → Iso-lens A B → Iso-lens A C
  l₁ ∘ l₂ = ⟨ lzero , lzero ⟩ l₁ ∘ l₂

  -- Other definitions of composition match ⟨_,_⟩_∘_, if the codomain
  -- type is inhabited whenever it is merely inhabited, and the
  -- resulting setter function is defined in a certain way (assuming
  -- univalence).

  composition≡∘ :
    let open Iso-lens in
    {A : Set (a ⊔ b ⊔ c)} {B : Set (b ⊔ c)} {C : Set c} →
    Univalence (a ⊔ b ⊔ c) →
    (∥ C ∥ → C) →
    (comp : Iso-lens B C → Iso-lens A B → Iso-lens A C) →
    (∀ l₁ l₂ a c →
       set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
    comp ≡ ⟨ a , b ⟩_∘_
  composition≡∘ univ ∥C∥→C comp set-comp =
    ∘-unique univ ∥C∥→C (comp , set-comp)
      (_ , λ { ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ → refl })

  -- Identity and composition form a kind of precategory (assuming
  -- univalence).

  associativity :
    ∀ a b c
      {A : Set (a ⊔ b ⊔ c ⊔ d)} {B : Set (b ⊔ c ⊔ d)}
      {C : Set (c ⊔ d)} {D : Set d} →
    Univalence (a ⊔ b ⊔ c ⊔ d) →
    (l₁ : Iso-lens C D)
    (l₂ : Iso-lens B C)
    (l₃ : Iso-lens A B) →
    ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
    ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
  associativity _ _ _ univ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ =
    _↔_.from (equality-characterisation₂ univ)
             (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl)

  left-identity :
    ∀ bi a {A : Set (a ⊔ b)} {B : Set b} →
    Univalence (a ⊔ b) →
    (l : Iso-lens A B) →
    ⟨ a , lzero ⟩ id bi ∘ l ≡ l
  left-identity ⊠ _ {B = B} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₂ univ)
      ( (R × ∥ B ∥  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl
      )
    where
    open Iso-lens l

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
    (l : Iso-lens A B) →
    ⟨ lzero , a ⟩ l ∘ id bi ≡ l
  right-identity ⊠ _ {A = A} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₂ univ)
      ( (∥ A ∥ × R  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl
      )
    where
    open Iso-lens l

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

open Iso-lens-combinators

------------------------------------------------------------------------
-- Isomorphisms expressed using Iso-lens quasi-inverses

private
  module B {a} (b : Block "id") =
    Bi-invertibility equality-with-J (Set a) Iso-lens (id b) _∘_
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
  open Iso-lens

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

-- See also ≃≃≅ below.

------------------------------------------------------------------------
-- Equivalences expressed using bi-invertibility for lenses

-- A form of equivalence between types, expressed using lenses.

open B public using () renaming (_≊_ to [_]_≊_; _≅_ to [_]_≅_)
open BM public using (equality-characterisation-≊)

-- Lenses with left inverses have propositional remainder types.

has-left-inverse→remainder-propositional :
  (b : Block "id")
  (l : Iso-lens A B) →
  B.Has-left-inverse b l →
  Is-proposition (Iso-lens.R l)
has-left-inverse→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l⁻¹∘l≡id) =
                                $⟨ get≡id→remainder-propositional
                                     (l⁻¹ ∘ l)
                                     (λ a → cong (flip get a) l⁻¹∘l≡id) ⟩
  Is-proposition (R (l⁻¹ ∘ l))  ↔⟨⟩
  Is-proposition (R l × R l⁻¹)  ↝⟨ H-level-×₁ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Iso-lens

-- Lenses with right inverses have propositional remainder types.

has-right-inverse→remainder-propositional :
  (b : Block "id")
  (l : Iso-lens A B) →
  B.Has-right-inverse b l →
  Is-proposition (Iso-lens.R l)
has-right-inverse→remainder-propositional
  ⊠ l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l∘l⁻¹≡id) =
                                $⟨ get≡id→remainder-propositional
                                     (l ∘ l⁻¹)
                                     (λ a → cong (flip get a) l∘l⁻¹≡id) ⟩
  Is-proposition (R (l ∘ l⁻¹))  ↔⟨⟩
  Is-proposition (R l⁻¹ × R l)  ↝⟨ H-level-×₂ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
  Is-proposition (R l)          □
  where
  open Iso-lens

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
  open Iso-lens

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
    l′ : ∀ b (A≊B : [ b ] A ≊ B) → Iso-lens A B
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

-- The getter function of a bi-invertible lens is an equivalence
-- (assuming univalence).

Is-bi-invertible→Is-equivalence-get :
  {A : Set a}
  (b : Block "id") →
  Univalence a →
  (l : Iso-lens A B) →
  B.Is-bi-invertible b l → Is-equivalence (Iso-lens.get l)
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
  (l : Iso-lens A B) →
  (Iso-lens.R l → B) →
  B.Is-bi-invertible b l ≃ Is-equivalence (Iso-lens.get l)
Is-bi-invertible≃Is-equivalence-get b univ l f = Eq.⇔→≃
  (BM.Is-bi-invertible-propositional b univ l)
  (Eq.propositional ext _)
  (Is-bi-invertible→Is-equivalence-get b univ l)
  (λ is-equiv →

     let l′ = ≃→lens′ Eq.⟨ get l , is-equiv ⟩ in

                              $⟨ proj₂ (_≃_.to (≃≃≊ b univ) Eq.⟨ _ , is-equiv ⟩) ⟩
     B.Is-bi-invertible b l′  ↝⟨ subst (B.Is-bi-invertible b) (sym $ get-equivalence→≡≃→lens′ univ l is-equiv f) ⟩□
     B.Is-bi-invertible b l   □)
  where
  open Iso-lens

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
           Iso-lens A B
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

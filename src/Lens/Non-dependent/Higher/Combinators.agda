------------------------------------------------------------------------
-- Identity and composition for higher lenses
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Combinators
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Bi-invertibility
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_)
open import Category equality-with-J as C using (Category; Precategory)
import Circle eq as Circle
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent.Higher eq
import Lens.Non-dependent.Traditional eq as Traditional
open import Lens.Non-dependent.Traditional.Combinators eq as TC
  using (Naive-category; Univalent)

private
  variable
    a b c d : Level
    A B C   : Type a

------------------------------------------------------------------------
-- Lens combinators

-- The definition of the identity lens is unique, if the get
-- function is required to be the identity (assuming univalence).

id-unique :
  {A : Type a} →
  Univalence a →
  (l₁ l₂ : Lens A A) →
  Lens.get l₁ ≡ P.id →
  Lens.get l₂ ≡ P.id →
  l₁ ≡ l₂
id-unique {A = A} univ l₁ l₂ get-l₁≡id get-l₂≡id =   $⟨ trans get-l₁≡id (sym get-l₂≡id) ⟩
  _≃_.to (_≃_.from f l₁′) ≡ _≃_.to (_≃_.from f l₂′)  ↝⟨ Eq.lift-equality ext ⟩
  _≃_.from f l₁′ ≡ _≃_.from f l₂′                    ↝⟨ _≃_.to $ Eq.≃-≡ (inverse f) {x = l₁′} {y = l₂′} ⟩
  l₁′ ≡ l₂′                                          ↝⟨ cong proj₁ ⟩□
  l₁ ≡ l₂                                            □
  where
  open Lens

  f : (A ≃ A) ≃ (∃ λ (l : Lens A A) → Is-equivalence (Lens.get l))
  f = ≃-≃-Σ-Lens-Is-equivalence-get univ

  is-equiv :
    (l : Lens A A) →
    get l ≡ P.id → Is-equivalence (get l)
  is-equiv _ get≡id =
    Eq.respects-extensional-equality
      (ext⁻¹ $ sym get≡id)
      (_≃_.is-equivalence Eq.id)

  l₁′ l₂′ : ∃ λ (l : Lens A A) → Is-equivalence (Lens.get l)
  l₁′ = l₁ , is-equiv l₁ get-l₁≡id
  l₂′ = l₂ , is-equiv l₂ get-l₂≡id

-- The result of composing two lenses is unique if the codomain type
-- is inhabited whenever it is merely inhabited, and we require that
-- the resulting setter function is defined in a certain way
-- (assuming univalence).

∘-unique :
  let open Lens in
  {A : Type a} {C : Type c} →
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

opaque

  -- Identity lens.

  id : Lens A A
  id {A = A} = record
    { R         = ∥ A ∥
    ; equiv     = A          ↔⟨ inverse ∥∥×↔ ⟩□
                  ∥ A ∥ × A  □
    ; inhabited = P.id
    }

opaque
  unfolding id

  -- The identity lens's getter is the identity function.

  get-id≡id : Lens.get id ≡ P.id {A = A}
  get-id≡id = refl _

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
--
-- See also Lens.Non-dependent.Higher.Coinductive.Small.⟨_⟩_⊚_ and
-- Lens.Non-dependent.Equivalent-preimages.⟨_⟩_⊚_.

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

-- A variant of composition for lenses between types with the same
-- universe level.

infixr 9 _∘_

_∘_ :
  {A B C : Type a} →
  Lens B C → Lens A B → Lens A C
l₁ ∘ l₂ = ⟨ lzero , lzero ⟩ l₁ ∘ l₂

-- Other definitions of composition match ⟨_,_⟩_∘_, if the codomain
-- type is inhabited whenever it is merely inhabited, and the
-- resulting setter function is defined in a certain way (assuming
-- univalence).

composition≡∘ :
  let open Lens in
  ∀ a b {A : Type (a ⊔ b ⊔ c)} {B : Type (b ⊔ c)} {C : Type c} →
  Univalence (a ⊔ b ⊔ c) →
  (∥ C ∥ → C) →
  (comp : Lens B C → Lens A B → Lens A C) →
  (∀ l₁ l₂ a c →
     set (comp l₁ l₂) a c ≡ set l₂ a (set l₁ (get l₂ a) c)) →
  comp ≡ ⟨ a , b ⟩_∘_
composition≡∘ _ _ univ ∥C∥→C comp set-comp =
  ∘-unique univ ∥C∥→C (comp , set-comp)
    (_ , λ { ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ _ _ → refl _ })

-- Identity and composition form a kind of precategory (assuming
-- univalence).

associativity :
  ∀ a b c
    {A : Type (a ⊔ b ⊔ c ⊔ d)} {B : Type (b ⊔ c ⊔ d)}
    {C : Type (c ⊔ d)} {D : Type d} →
  Univalence (a ⊔ b ⊔ c ⊔ d) →
  (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
  ⟨ a ⊔ b , c ⟩ l₁ ∘ (⟨ a , b ⟩ l₂ ∘ l₃) ≡
  ⟨ a , b ⊔ c ⟩ (⟨ b , c ⟩ l₁ ∘ l₂) ∘ l₃
associativity _ _ _ univ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ ⟨ _ , _ , _ ⟩ =
  _↔_.from (equality-characterisation₁ univ)
           (Eq.↔⇒≃ (inverse ×-assoc) , λ _ → refl _)

opaque
  unfolding id

  left-identity :
    ∀ a {A : Type (a ⊔ b)} {B : Type b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ a , lzero ⟩ id ∘ l ≡ l
  left-identity _ {B = B} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₁ univ)
      ( (R × ∥ B ∥  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl _
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
        ; right-inverse-of = refl
        }
      ; left-inverse-of = λ { (r , _) →
          cong (λ x → r , x) $ truncation-is-proposition _ _ }
      }

  right-identity :
    ∀ a {A : Type (a ⊔ b)} {B : Type b} →
    Univalence (a ⊔ b) →
    (l : Lens A B) →
    ⟨ lzero , a ⟩ l ∘ id ≡ l
  right-identity _ {A = A} univ l@(⟨ _ , _ , _ ⟩) =
    _↔_.from (equality-characterisation₁ univ)
      ( (∥ A ∥ × R  ↔⟨ lemma ⟩□
         R          □)
      , λ _ → refl _
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
        ; right-inverse-of = refl
        }
      ; left-inverse-of = λ { (_ , r) →
          cong (λ x → x , r) $ truncation-is-proposition _ _ }
      }

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private
  module B {a} =
    Bi-invertibility equality-with-J (Type a) Lens id _∘_
  module BM {a} (univ : Univalence a) = B.More
    (left-identity _ univ)
    (right-identity _ univ)
    (associativity _ _ _ univ)

-- A form of isomorphism between types, expressed using lenses.

open B public
  using ()
  renaming (_≅_ to _≅_;
            Has-quasi-inverse to Has-quasi-inverse)

opaque
  unfolding id

  -- Lenses with quasi-inverses can be converted to equivalences.

  ≅→≃ : A ≅ B → A ≃ B
  ≅→≃ (l@(⟨ _ , _ , _ ⟩) , l⁻¹@(⟨ _ , _ , _ ⟩) , l∘l⁻¹≡id , l⁻¹∘l≡id) =
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

-- There is a split surjection from A ≅ B to A ≃ B (assuming
-- univalence).

≅↠≃ :
  {A B : Type a} →
  Univalence a →
  (A ≅ B) ↠ (A ≃ B)
≅↠≃ {A = A} {B = B} univ = record
  { logical-equivalence = record
    { to   = ≅→≃
    ; from = from
    }
  ; right-inverse-of = ≅→≃∘from
  }
  where
  from : A ≃ B → A ≅ B
  from A≃B = l , l⁻¹ , l∘l⁻¹≡id , l⁻¹∘l≡id
    where
    l : Lens A B
    l = ≃→lens′ A≃B

    l⁻¹ : Lens B A
    l⁻¹ = ≃→lens′ (inverse A≃B)

    opaque
      unfolding id

      l∘l⁻¹≡id : l ∘ l⁻¹ ≡ id
      l∘l⁻¹≡id = _↔_.from (equality-characterisation₁ univ)
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

      l⁻¹∘l≡id : l⁻¹ ∘ l ≡ id
      l⁻¹∘l≡id = _↔_.from (equality-characterisation₁ univ)
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

  opaque
    unfolding ≅→≃

    ≅→≃∘from : ∀ A≃B → ≅→≃ (from A≃B) ≡ A≃B
    ≅→≃∘from _ = Eq.lift-equality ext (refl _)

-- There is not necessarily a split surjection from
-- Is-equivalence (Lens.get l) to Has-quasi-inverse l, if l is a
-- lens between types in the same universe (assuming univalence).

¬Is-equivalence-get↠Has-quasi-inverse :
  Univalence a →
  ¬ ({A B : Type a}
     (l : Lens A B) →
     Is-equivalence (Lens.get l) ↠ Has-quasi-inverse l)
¬Is-equivalence-get↠Has-quasi-inverse {a = a} univ surj =
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

  opaque
    unfolding id

    lemma₂ :
      (∃ λ (eq : R id ≃ R (id {A = ↑ a Circle.𝕊¹})) →
         (∀ z → _≃_.to eq (remainder id z) ≡ remainder id z)
           ×
         ((z : Z) → get id z ≡ get id z)) ≃
      ((z : Z) → z ≡ z)
    lemma₂ =
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
                                                                         (Is-equivalence-propositional ext)
                                                                         (_≃_.is-equivalence Eq.id) ⟩

    Is-equivalence P.id                                             ↔⟨ ≡⇒↝ equivalence $ cong Is-equivalence $ sym
                                                                       get-id≡id ⟩

    Is-equivalence (get id)                                         ↝⟨ surj id ⟩

    Has-quasi-inverse id                                            ↔⟨ BM.Has-quasi-inverse≃id≡id-domain univ
                                                                         (id , left-identity _ univ _ , right-identity _ univ _) ⟩

    id ≡ id                                                         ↔⟨ equality-characterisation₂ univ ⟩

    (∃ λ (eq : R id ≃ R id) →
       (∀ z → _≃_.to eq (remainder id z) ≡ remainder id z)
         ×
       (∀ z → get id z ≡ get id z))                                 ↔⟨ lemma₂ ⟩□

    ((z : Z) → z ≡ z)                                               □

-- See also ≃≃≅ below.

------------------------------------------------------------------------
-- Equivalences expressed using bi-invertibility for lenses

-- A form of equivalence between types, expressed using lenses.

open B public
  using ()
  renaming (_≊_ to _≊_;
            Has-left-inverse to Has-left-inverse;
            Has-right-inverse to Has-right-inverse;
            Is-bi-invertible to Is-bi-invertible)
open BM public
  using ()
  renaming (equality-characterisation-≊ to equality-characterisation-≊)

opaque
  unfolding id

  -- Lenses with left inverses have propositional remainder types.

  has-left-inverse→remainder-propositional :
    (l : Lens A B) →
    Has-left-inverse l →
    Is-proposition (Lens.R l)
  has-left-inverse→remainder-propositional
    l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l⁻¹∘l≡id) =
                                  $⟨ get≡id→remainder-propositional
                                       (l⁻¹ ∘ l)
                                       (λ a → cong (flip get a) l⁻¹∘l≡id) ⟩
    Is-proposition (R (l⁻¹ ∘ l))  ↔⟨⟩
    Is-proposition (R l × R l⁻¹)  ↝⟨ H-level-×₁ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
    Is-proposition (R l)          □
    where
    open Lens

opaque
  unfolding id

  -- Lenses with right inverses have propositional remainder types.

  has-right-inverse→remainder-propositional :
    (l : Lens A B) →
    Has-right-inverse l →
    Is-proposition (Lens.R l)
  has-right-inverse→remainder-propositional
    l@(⟨ _ , _ , _ ⟩) (l⁻¹@(⟨ _ , _ , _ ⟩) , l∘l⁻¹≡id) =
                                  $⟨ get≡id→remainder-propositional
                                       (l ∘ l⁻¹)
                                       (λ a → cong (flip get a) l∘l⁻¹≡id) ⟩
    Is-proposition (R (l ∘ l⁻¹))  ↔⟨⟩
    Is-proposition (R l⁻¹ × R l)  ↝⟨ H-level-×₂ (∥∥-map (remainder l⁻¹) ⊚ inhabited l) 1 ⟩□
    Is-proposition (R l)          □
    where
    open Lens

-- There is an equivalence between A ≃ B and A ≊ B (assuming
-- univalence).

≃≃≊ :
  {A B : Type a} →
  Univalence a →
  (A ≃ B) ≃ (A ≊ B)
≃≃≊ {A = A} {B = B} univ = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  })
  where
  open Lens

  to : A ≃ B → A ≊ B
  to = B.≅→≊ ⊚ _↠_.from (≅↠≃ univ)

  from : A ≊ B → A ≃ B
  from = _↠_.to (≅↠≃ univ) ⊚ _↠_.from (BM.≅↠≊ univ)

  to∘from : ∀ A≊B → to (from A≊B) ≡ A≊B
  to∘from A≊B =
    _≃_.from (equality-characterisation-≊ univ _ _) $
    _↔_.from (equality-characterisation₂ univ)
      ( ∥B∥≃R  A≊B
      , lemma₁ A≊B
      , lemma₂ A≊B
      )
    where
    l′ : ∀ (A≊B : A ≊ B) → Lens A B
    l′ A≊B = proj₁ (to (from A≊B))

    ∥B∥≃R : ∀ (A≊B@(l , _) : A ≊ B) → ∥ B ∥ ≃ R l
    ∥B∥≃R (l , (l-inv@(l⁻¹ , _) , _)) = Eq.⇔→≃
      truncation-is-proposition
      R-prop
      (Trunc.rec R-prop (remainder l ⊚ get l⁻¹))
      (inhabited l)
      where
      R-prop = has-left-inverse→remainder-propositional l l-inv

    opaque
      unfolding ≅→≃

      lemma₁ :
        ∀ (A≊B@(l , _) : A ≊ B) a →
        _≃_.to (∥B∥≃R A≊B) (remainder (l′ A≊B) a) ≡ remainder l a
      lemma₁
        ( l@(⟨ _ , _ , _ ⟩)
        , (l⁻¹@(⟨ _ , _ , _ ⟩) , l⁻¹∘l≡id)
        , (⟨ _ , _ , _ ⟩ , _)
        ) a =
        remainder l (get l⁻¹ (get l a))  ≡⟨⟩
        remainder l (get (l⁻¹ ∘ l) a)    ≡⟨ cong (λ l′ → remainder l (get l′ a)) l⁻¹∘l≡id ⟩
        remainder l (get id a)           ≡⟨⟩
        remainder l a                    ∎

      lemma₂ :
        ∀ (A≊B@(l , _) : A ≊ B) a →
        get (l′ A≊B) a ≡ get l a
      lemma₂
        (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) _ =
        refl _

  opaque
    unfolding ≅→≃

    from∘to :
      (A≃B : A ≃ B) →
      _↠_.to (≅↠≃ univ) (_↠_.from (BM.≅↠≊ univ)
        (B.≅→≊ (_↠_.from (≅↠≃ univ) A≃B))) ≡
      A≃B
    from∘to _ = Eq.lift-equality ext (refl _)

opaque
  unfolding ≅→≃

  -- The right-to-left direction of ≃≃≊ maps bi-invertible lenses to
  -- their getter functions.

  to-from-≃≃≊≡get :
    (univ : Univalence a)
    (A≊B@(l , _) : A ≊ B) →
    _≃_.to (_≃_.from (≃≃≊ univ) A≊B) ≡ Lens.get l
  to-from-≃≃≊≡get
    _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
    refl _

-- A variant of ≃≃≊ that works even if A and B live in different
-- universes.
--
-- This variant came up in a discussion with Andrea Vezzosi.

≃≃≊′ :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  (A ≃ B) ≃ (↑ b A ≊ ↑ a B)
≃≃≊′ {a = a} {b = b} {A = A} {B = B} univ =
  A ≃ B          ↔⟨ inverse $ Eq.≃-preserves-bijections ext Bij.↑↔ Bij.↑↔ ⟩
  ↑ b A ≃ ↑ a B  ↝⟨ ≃≃≊ univ ⟩□
  ↑ b A ≊ ↑ a B  □

opaque
  unfolding ≅→≃

  -- The right-to-left direction of ≃≃≊′ maps bi-invertible lenses to
  -- variants of their getter functions.

  to-from-≃≃≊′≡get :
    {A : Type a} {B : Type b}
    (univ : Univalence (a ⊔ b)) →
    (A≊B@(l , _) : ↑ b A ≊ ↑ a B) →
    _≃_.to (_≃_.from (≃≃≊′ univ) A≊B) ≡ lower ⊚ Lens.get l ⊚ lift
  to-from-≃≃≊′≡get
    _ (⟨ _ , _ , _ ⟩ , (⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
    refl _

opaque
  unfolding ≅→≃

  -- The getter function of a bi-invertible lens is an equivalence
  -- (assuming univalence).

  Is-bi-invertible→Is-equivalence-get :
    {A : Type a} →
    Univalence a →
    (l : Lens A B) →
    Is-bi-invertible l → Is-equivalence (Lens.get l)
  Is-bi-invertible→Is-equivalence-get
    univ l@(⟨ _ , _ , _ ⟩)
    is-bi-inv@((⟨ _ , _ , _ ⟩ , _) , (⟨ _ , _ , _ ⟩ , _)) =
    _≃_.is-equivalence (_≃_.from (≃≃≊ univ) (l , is-bi-inv))

-- If l is a lens between types in the same universe, then there is an
-- equivalence between "l is bi-invertible" and "the getter of l is an
-- equivalence" (assuming univalence).

Is-bi-invertible≃Is-equivalence-get :
  {A B : Type a} →
  Univalence a →
  (l : Lens A B) →
  Is-bi-invertible l ≃ Is-equivalence (Lens.get l)
Is-bi-invertible≃Is-equivalence-get univ l = Eq.⇔→≃
  (BM.Is-bi-invertible-propositional univ l)
  (Is-equivalence-propositional ext)
  (Is-bi-invertible→Is-equivalence-get univ l)
  (λ is-equiv →

     let l′ = ≃→lens′ Eq.⟨ get l , is-equiv ⟩ in

                          $⟨ proj₂ (_≃_.to (≃≃≊ univ) Eq.⟨ _ , is-equiv ⟩) ⟩
     Is-bi-invertible l′  ↝⟨ subst Is-bi-invertible (sym $ get-equivalence→≡≃→lens′ univ l is-equiv) ⟩□
     Is-bi-invertible l   □)
  where
  open Lens

-- If A is a set, then there is an equivalence between A ≊ B and A ≅ B
-- (assuming univalence).

≊≃≅ :
  {A B : Type a} →
  Univalence a →
  Is-set A →
  (A ≊ B) ≃ (A ≅ B)
≊≃≅ univ A-set =
  ∃-cong λ _ →
    BM.Is-bi-invertible≃Has-quasi-inverse-domain
      univ
      (Is-set-closed-domain univ A-set)

------------------------------------------------------------------------
-- A category

opaque

  -- If A is a set, then there is an equivalence between A ≃ B and A ≅ B
  -- (assuming univalence).

  ≃≃≅ :
    {A B : Type a} →
    Univalence a →
    Is-set A →
    (A ≃ B) ≃ (A ≅ B)
  ≃≃≅ {A = A} {B = B} univ A-set =
    A ≃ B  ↝⟨ ≃≃≊ univ ⟩
    A ≊ B  ↝⟨ ≊≃≅ univ A-set ⟩□
    A ≅ B  □

opaque
  unfolding id ≃≃≅

  -- The equivalence ≃≃≅ maps identity to identity.

  ≃≃≅-id≡id :
    {A : Type a}
    (univ : Univalence a) (A-set : Is-set A) →
    proj₁ (_≃_.to (≃≃≅ univ A-set) F.id) ≡ id
  ≃≃≅-id≡id univ _ =
    _↔_.from (equality-characterisation₁ univ)
      (F.id , λ _ → refl _)

-- Lenses between sets in the same universe form a precategory
-- (assuming univalence).

private

  precategory′ :
    Univalence a →
    C.Precategory′ (lsuc a) (lsuc a)
  precategory′ {a = a} univ =
      Set a
    , (λ (A , A-set) (B , _) →
           Lens A B
         , Is-set-closed-domain univ A-set)
    , id
    , _∘_
    , left-identity lzero univ _
    , right-identity lzero univ _
    , (λ {_ _ _ _ l₁ l₂ l₃} →
         associativity lzero lzero lzero univ l₃ l₂ l₁)

opaque

  precategory :
    Univalence a →
    Precategory (lsuc a) (lsuc a)
  precategory univ .C.Precategory.precategory =
    precategory′ univ

opaque

  -- Lenses between sets in the same universe form a category
  -- (assuming univalence).

  category :
    Univalence a →
    Category (lsuc a) (lsuc a)
  category univ =
    C.precategory-with-Set-to-category
      ext
      (λ _ _ → univ)
      (proj₂ $ precategory′ univ)
      (λ (_ , A-set) _ → ≃≃≅ univ A-set)
      (λ (_ , A-set) → ≃≃≅-id≡id univ A-set)

opaque
  unfolding id precategory

  -- The precategory defined here is equal to the one defined in
  -- Traditional, if the latter one is lifted (assuming univalence).

  precategory≡precategory :
    Univalence (lsuc a) →
    (univ : Univalence a) →
    precategory univ ≡
    C.lift-precategory-Hom _ TC.precategory
  precategory≡precategory univ⁺ univ =
    _↔_.to (C.equality-characterisation-Precategory ext univ⁺ univ⁺)
      ( F.id
      , (λ (X , X-set) (Y , _) →
           Lens X Y                    ↔⟨ Lens↔Traditional-lens univ X-set ⟩
           Traditional.Lens X Y        ↔⟨ inverse Bij.↑↔ ⟩□
           ↑ _ (Traditional.Lens X Y)  □)
      , (λ (_ , X-set) → cong lift $ _↔_.from
           (Traditional.equality-characterisation-for-sets X-set)
           (refl _))
      , (λ (_ , X-set) (_ , Y-set) _ (lift l₁) (lift l₂) →
           cong lift (∘-lemma X-set Y-set l₁ l₂))
      )
    where
    opaque
      unfolding Lens↔Traditional-lens.from

      ∘-lemma :
        (A-set : Is-set A) (B-set : Is-set B)
        (l₁ : Traditional.Lens B C) (l₂ : Traditional.Lens A B) →
        Lens.traditional-lens
          (_↠_.from (Lens↠Traditional-lens B-set) l₁ ∘
           _↠_.from (Lens↠Traditional-lens A-set) l₂) ≡
        l₁ TC.∘ l₂
      ∘-lemma A-set _ _ _ =
        _↔_.from (Traditional.equality-characterisation-for-sets A-set)
          (refl _)

-- The category defined here is equal to the one defined in
-- Traditional, if the latter one is lifted (assuming univalence).

category≡category :
  Univalence (lsuc a) →
  (univ : Univalence a) →
  category univ ≡
  C.lift-category-Hom _ (TC.category univ)
category≡category univ⁺ univ =
  _↔_.from (C.≡↔precategory≡precategory ext)
    (Category.precategory (category univ)          ≡⟨ lemma ⟩

     precategory univ                              ≡⟨ precategory≡precategory univ⁺ univ ⟩∎

     Category.precategory
       (C.lift-category-Hom _ (TC.category univ))  ∎)
  where
  opaque
    unfolding category precategory

    lemma :
      Category.precategory (category univ) ≡
      precategory univ
    lemma = refl _

-- Types in a fixed universe and higher lenses between them form a
-- naive category (assuming univalence).

naive-category :
  Univalence a →
  Naive-category (lsuc a) (lsuc a)
naive-category {a = a} univ =
    Type a
  , Lens
  , id
  , _∘_
  , left-identity lzero univ
  , right-identity lzero univ
  , associativity lzero lzero lzero univ

-- This category is univalent.
--
-- An anonymous reviewer asked if something like this could be proved,
-- given ≃≃≊. The proof of this result is due to Andrea Vezzosi.

univalent :
  (univ : Univalence a) →
  Univalent (naive-category univ)
univalent univ =
  BM.≡≃≊→Univalence-≊ univ λ {A B} →
    A ≡ B  ↝⟨ ≡≃≃ univ ⟩
    A ≃ B  ↝⟨ ≃≃≊ univ ⟩□
    A ≊ B  □

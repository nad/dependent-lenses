------------------------------------------------------------------------
-- Dependent lenses
------------------------------------------------------------------------

module Lens.Dependent where

open import Algebra
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Function hiding (id) renaming (_∘_ to _⊚_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Level
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Nullary

------------------------------------------------------------------------
-- Dependent lenses with "remainder types" visible in the type

-- If Lens₃ A R B is inhabited, then a value of type A can be split up
-- into a "remainder" r of type R and a value of type B r.

Lens₃ : ∀ {a r b} → Set a → (R : Set r) → (R → Set b) → Set _
Lens₃ A R B = A ↔ Σ R B

module Lens₃ {a r b} {A : Set a} {R : Set r} {B : R → Set b}
             (lens : Lens₃ A R B) where

  open Inverse lens

  -- The remainder.

  remainder : A → R
  remainder a = proj₁ (to ⟨$⟩ a)

  -- Getter.

  get : (a : A) → B (remainder a)
  get a = proj₂ (to ⟨$⟩ a)

  -- Setter.

  set : (a : A) → B (remainder a) → A
  set a b = from ⟨$⟩ (remainder a , b)

  -- Modifier.

  modify : (a : A) → (B (remainder a) → B (remainder a)) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b = begin
    proj₁ (to ⟨$⟩ (from ⟨$⟩ (remainder a , b)))  ≡⟨ P.cong proj₁ (right-inverse-of _) ⟩
    proj₁ {B = B} (remainder a , b)              ≡⟨⟩
    remainder a                                  ∎
    where open P.≡-Reasoning

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a = begin
    from ⟨$⟩ (proj₁ (to ⟨$⟩ a) , proj₂ (to ⟨$⟩ a))  ≡⟨⟩
    from ⟨$⟩ (to ⟨$⟩ a)                             ≡⟨ left-inverse-of _ ⟩
    a                                               ∎
    where open P.≡-Reasoning

  get-set-≅ : ∀ a b → get (set a b) ≅ b
  get-set-≅ a b = begin
    proj₂ (to ⟨$⟩ (from ⟨$⟩ (remainder a , b)))  ≅⟨ proj₂-cong (right-inverse-of _) ⟩
    proj₂ {B = B} (remainder a , b)              ≡⟨⟩
    b                                            ∎
    where
    open H.≅-Reasoning

    proj₂-cong : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
                 p₁ ≡ p₂ → proj₂ p₁ ≅ proj₂ p₂
    proj₂-cong P.refl = H.refl

  get-set : ∀ a b → get (set a b) ≡
                    P.subst B (P.sym $ remainder-set a b) b
  get-set a b = H.≅-to-≡ (begin
    proj₂ (to ⟨$⟩ (from ⟨$⟩ (remainder a , b)))  ≅⟨ get-set-≅ a b ⟩
    b                                            ≅⟨ H.sym $ H.≡-subst-removable B (P.sym $ remainder-set a b) _ ⟩
    P.subst B (P.sym $ remainder-set a b) b      ∎)
    where open H.≅-Reasoning

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡
                        set a (P.subst B (remainder-set a b₁) b₂)
  set-set a b₁ b₂ = begin
    from ⟨$⟩ (proj₁ (to ⟨$⟩ (from ⟨$⟩ (proj₁ (to ⟨$⟩ a) , b₁))) , b₂)  ≡⟨ P.cong (_⟨$⟩_ from)
                                                                            (,-cong (P.cong proj₁ $ right-inverse-of _)
                                                                                    (H.sym $
                                                                                       H.≡-subst-removable B (remainder-set a b₁) _)) ⟩
    from ⟨$⟩ (proj₁ (to ⟨$⟩ a) , P.subst B (remainder-set a b₁) b₂)    ∎
    where
    open P.≡-Reasoning

    ,-cong : ∀ {a b} {A : Set a} {B : A → Set b} {x₁ y₁ x₂ y₂} →
             x₁ ≡ x₂ → y₁ ≅ y₂ → _≡_ {A = Σ A B} (x₁ , y₁) (x₂ , y₂)
    ,-cong P.refl H.refl = P.refl

------------------------------------------------------------------------
-- Lens₃ combinators

-- Identity lens.

id₃ : ∀ {a} {A : Set a} → Lens₃ A (Lift ⊤) (λ _ → A)
id₃ {A = A} = Inv.sym $ proj₁ CM.identity A
  where
  module CM = CommutativeMonoid (×-CommutativeMonoid bijection _)

-- Composition of lenses.

infixr 9 _₃∘₃_

_₃∘₃_ : ∀ {a r₁ b₁ r₂ b₂} {A : Set a} {R₁ : Set r₁} {B₁ : R₁ → Set b₁}
          {R₂ : R₁ → Set r₂} {B₂ : (r : R₁) → R₂ r → Set b₂} →
        (∀ {r} → Lens₃ (B₁ r) (R₂ r) (B₂ r)) → Lens₃ A R₁ B₁ →
        Lens₃ A (Σ R₁ R₂) (uncurry B₂)
_₃∘₃_ {A = A} {R₁} {B₁} {R₂} {B₂} l₁ l₂ =
  A                             ↔⟨ l₂ ⟩
  Σ R₁ B₁                       ↔⟨ Σ.cong Inv.id l₁ ⟩
  Σ R₁ (λ r → Σ (R₂ r) (B₂ r))  ↔⟨ Inv.sym Σ-assoc ⟩
  Σ (Σ R₁ R₂) (uncurry B₂)      ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Dependent lenses without "remainder types" visible in the type

-- The remainder /level/ is still visible in the type.

record Lens {a b} r
            (A : Set a) (B : A → Set b) : Set (a ⊔ suc (b ⊔ r)) where
  field
    -- The remainder type: what remains of A when B is removed
    -- (roughly).

    R : Set r

    -- A variant of B, indexed by Rs instead of As.

    B′ : R → Set b

    -- The main lens isomorphism.

    lens : Lens₃ A R B′

  private module L = Lens₃ lens

  -- The non-B part of the A value.

  remainder : A → R
  remainder = L.remainder

  field
    -- An isomorphism which specifies in what sense B′ is a variant of
    -- B.

    variant : ∀ {a} → B′ (remainder a) ↔ B a

  open Inverse

  -- Getter.

  get : (a : A) → B a
  get a = to variant ⟨$⟩ L.get a

  -- Setter.

  set : (a : A) → B a → A
  set a b = L.set a (from variant ⟨$⟩ b)

  -- Modifier.

  modify : (a : A) → (B a → B a) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b = L.remainder-set a (from variant ⟨$⟩ b)

  -- Hence the type of the gettable part stays unchanged (up to
  -- isomorphism) after a set.

  B-set : ∀ {a b} → B (set a b) ↔ B a
  B-set {a} {b} =
    B (set a b)               ↔⟨ Inv.sym variant ⟩
    B′ (remainder (set a b))  ≡⟨ P.cong B′ (remainder-set a b) ⟩
    B′ (remainder a)          ↔⟨ variant ⟩
    B a                       ∎
    where open Related.EquationalReasoning

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a = begin
    L.set a (from variant ⟨$⟩ (to variant ⟨$⟩ L.get a))  ≡⟨ P.cong (L.set a) (left-inverse-of variant _) ⟩
    L.set a (L.get a)                                    ≡⟨ L.set-get a ⟩
    a                                                    ∎
    where open P.≡-Reasoning

  get-set : ∀ a b → get (set a b) ≡ from B-set ⟨$⟩ b
  get-set a b = P.cong (_⟨$⟩_ (to variant)) (H.≅-to-≡ (begin
    L.get (L.set a (from variant ⟨$⟩ b))   ≅⟨ L.get-set-≅ a (from variant ⟨$⟩ b) ⟩
    from variant ⟨$⟩ b                     ≅⟨ lemma eq ⟩
    from (≡⇒ eq) ⟨$⟩ (from variant ⟨$⟩ b)  ∎))
    where
    open H.≅-Reasoning

    eq = P.cong B′ (remainder-set a b)

    lemma : ∀ {ℓ} {A B : Set ℓ} {x : B} (eq : A ≡ B) →
            x ≅ from (≡⇒ eq) ⟨$⟩ x
    lemma P.refl = H.refl

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to B-set ⟨$⟩ b₂)
  set-set a b₁ b₂ = begin
    L.set (L.set a (from variant ⟨$⟩ b₁)) (from variant ⟨$⟩ b₂)      ≡⟨ L.set-set a (from variant ⟨$⟩ b₁) (from variant ⟨$⟩ b₂) ⟩
    L.set a (P.subst B′ (remainder-set a b₁) (from variant ⟨$⟩ b₂))  ≡⟨ P.cong (L.set a) lemma ⟩
    L.set a (from variant ⟨$⟩ (to B-set ⟨$⟩ b₂))                     ∎
    where
    open P.≡-Reasoning

    eq = remainder-set a b₁

    lemma₂ : ∀ {a p} {A : Set a} (P : A → Set p)
               {x y : A} {p : P x} (eq : x ≡ y) →
             P.subst P eq p ≡ to (≡⇒ (P.cong P eq)) ⟨$⟩ p
    lemma₂ _ P.refl = P.refl

    lemma = begin
      P.subst B′ eq (from variant ⟨$⟩ b₂)                    ≡⟨ lemma₂ B′ eq ⟩
      to (≡⇒ (P.cong B′ eq)) ⟨$⟩ (from variant ⟨$⟩ b₂)       ≡⟨ P.sym $ left-inverse-of variant _ ⟩
      from variant ⟨$⟩ (to variant ⟨$⟩
        (to (≡⇒ (P.cong B′ eq)) ⟨$⟩ (from variant ⟨$⟩ b₂)))  ∎

------------------------------------------------------------------------
-- Lens combinators

-- Conversion from Lens₃ to Lens.

Lens₃-to-Lens : ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
                (l : Lens₃ A R B) → Lens r A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens l = record
  { lens    = l
  ; variant = Inv.id
  }

-- Identity lens.

id : ∀ {a} {A : Set a} → Lens a A (λ _ → A)
id = Lens₃-to-Lens id₃

-- Composition of lenses.
--
-- Note that this function combines a family of Lenses and a Lens₃.

infixr 9 _∘₃_

_∘₃_ : ∀ {a r₁ r₂ b c} {A : Set a} {R : Set r₂} {B : R → Set b}
         {C : {r : R} → B r → Set c} →
       (∀ {r} → Lens r₁ (B r) C) → (l₂ : Lens₃ A R B) →
       Lens _ A (C ⊚ Lens₃.get l₂)
l₁ ∘₃ l₂ = record
  { lens    = Lens.lens l₁ ₃∘₃ l₂
  ; variant = Lens.variant l₁
  }

-- /Forward/ composition of lenses.
--
-- This function combines /Lens/es, but has a type which is arguably
-- more complicated. The type is also somewhat restricted: C is only
-- indexed by As, not Bs.

infixr 9 _∘_

_∘_ : ∀ {a b c r₁ r₂} {A : Set a} {B : A → Set b} {C : A → Set c} →
      (l₁ : Lens r₁ A B) →
      let open Lens l₁; open Inverse lens in
      (∀ {r} → Lens r₂ (B′ r) (λ b′ → C (from ⟨$⟩ (r , b′)))) →
      Lens _ A C
_∘_ {C = C} l₁ l₂ = record
  { lens    = lens l₂ ₃∘₃ lens l₁
  ; variant = λ {a} →
      B′ l₂ (remainder l₂ (Lens₃.get (lens l₁) a))  ↔⟨ variant l₂ ⟩
      C (from (lens l₁) ⟨$⟩ (to (lens l₁) ⟨$⟩ a))   ≡⟨ P.cong C (left-inverse-of (lens l₁) a) ⟩
      C a                                           ∎
  }
  where
  open Inverse
  open Lens
  open Related.EquationalReasoning

-- Lenses respect (certain) isomorphisms.
--
-- Note that B₁ and B₂ are required to have the same universe level.
-- One could avoid this restriction by adding another level parameter
-- to the definition of Lens.

cast : ∀ {r b}
         {a₁} {A₁ : Set a₁} {B₁ : A₁ → Set b}
         {a₂} {A₂ : Set a₂} {B₂ : A₂ → Set b}
       (A₁↔A₂ : A₁ ↔ A₂) →
       (∀ a → B₁ (Inverse.from A₁↔A₂ ⟨$⟩ a) ↔ B₂ a) →
       Lens r A₁ B₁ → Lens _ A₂ B₂
cast {A₁ = A₁} {B₁} {A₂ = A₂} {B₂} A₁↔A₂ B₁↔B₂ l = record
  { lens    = A₂      ↔⟨ Inv.sym A₁↔A₂ ⟩
              A₁      ↔⟨ lens ⟩
              Σ R B′  ∎
  ; variant = λ {a} →
              B′ (remainder (from ⟨$⟩ a))  ↔⟨ variant ⟩
              B₁ (from ⟨$⟩ a)              ↔⟨ B₁↔B₂ _ ⟩
              B₂ a                         ∎
  }
  where
  open Inverse A₁↔A₂
  open Lens l
  open Related.EquationalReasoning

------------------------------------------------------------------------
-- An observation

-- Lenses cannot (easily) be used to replace ordinary projections: one
-- cannot, in general, define lenses with the type of the first
-- projection from a Σ-type.

-- Proof for Lens.

not-proj₁ : ∀ r →
            ∃₂ λ (A : Set) (B : A → Set) →
            ¬ Lens r (Σ A B) (λ _ → A)
not-proj₁ r = , , empty
  where
  -- A Σ-type which is isomorphic to the unit type.

  Unit = Σ Bool λ b → b ≡ true

  -- All its inhabitants are equal.

  equal : (u₁ u₂ : Unit) → u₁ ≡ u₂
  equal (.true , P.refl) (.true , P.refl) = P.refl

  -- Its only inhabitant.

  u : Unit
  u = (true , P.refl)

  -- We cannot construct a lens from Unit to Bool.

  empty : ¬ Lens r Unit (λ _ → Bool)
  empty l = distinct (equal (set u true) (set u false))
    where
    open Inverse
    open Lens l
    open P.≡-Reasoning

    -- Some lemmas.

    helper :
      {A : Set r} {B C : Set} {b : B} {c₁ c₂ : C}
      (P : A → Set) (f : C → A) (inv : ∀ {c} → P (f c) ↔ B) →
      c₁ ≡ c₂ → (eq : f c₁ ≡ f c₂) →
      to inv ⟨$⟩ (from (≡⇒ (P.cong P eq)) ⟨$⟩ (from inv ⟨$⟩ b)) ≡ b
    helper f P inv P.refl P.refl = right-inverse-of inv _

    from-B-set : ∀ b → from (B-set {b = b}) ⟨$⟩ b ≡ b
    from-B-set b =
      helper B′ remainder variant
             (equal (set u b) u) (remainder-set u b)

    -- set u true and set u false must be distinct.

    distinct : set u true ≢ set u false
    distinct eq with begin
      true                  ≡⟨ P.sym $ from-B-set true ⟩
      from B-set ⟨$⟩ true   ≡⟨ P.sym $ get-set u true ⟩
      get (set u true)      ≡⟨ P.cong get eq ⟩
      get (set u false)     ≡⟨ get-set u false ⟩
      from B-set ⟨$⟩ false  ≡⟨ from-B-set false ⟩
      false                 ∎
    ... | ()

-- Proof for Lens₃.

not-proj₁₃ : ∀ r →
             ∃₂ λ (A : Set) (B : A → Set) →
               ∀ (R : Set r) → ¬ Lens₃ (Σ A B) R (λ _ → A)
not-proj₁₃ r =
  , , λ _ l → proj₂ (proj₂ (not-proj₁ r)) (Lens₃-to-Lens l)

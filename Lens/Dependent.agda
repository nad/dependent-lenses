------------------------------------------------------------------------
-- Dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lens.Dependent where

open import Bool
open import Equality.Propositional
open import Logical-equivalence using (module _⇔_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J using (_↔_; module _↔_; ↑↔)
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Dependent lenses with "remainder types" visible in the type

-- If Lens₃ A R B is inhabited, then a value of type A can be split up
-- into a "remainder" r of type R and a value of type B r.

Lens₃ : ∀ {a r b} → Set a → (R : Set r) → (R → Set b) → Set _
Lens₃ A R B = A ↔ Σ R B

module Lens₃ {a r b} {A : Set a} {R : Set r} {B : R → Set b}
             (lens : Lens₃ A R B) where

  open _↔_ lens

  -- The remainder.

  remainder : A → R
  remainder a = proj₁ (to a)

  -- Getter.

  get : (a : A) → B (remainder a)
  get a = proj₂ (to a)

  -- Setter.

  set : (a : A) → B (remainder a) → A
  set a b = from (remainder a , b)

  -- Modifier.

  modify : (a : A) → (B (remainder a) → B (remainder a)) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b =
    proj₁ (to (from (remainder a , b)))  ≡⟨ cong proj₁ (right-inverse-of _) ⟩∎
    remainder a                          ∎

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    from (proj₁ (to a) , proj₂ (to a))  ≡⟨⟩
    from (to a)                         ≡⟨ left-inverse-of _ ⟩∎
    a                                   ∎

  get-set : ∀ a b → get (set a b) ≡
                    subst B (sym $ remainder-set a b) b
  get-set a b =
    proj₂ (to (from (remainder a , b)))  ≡⟨ sym $ subst-application proj₂ (sym lemma) ⟩
    subst (B ⊚ proj₁) (sym lemma) b      ≡⟨ subst-∘ _ _ (sym lemma) ⟩
    subst B (cong proj₁ (sym lemma)) b   ≡⟨ cong (λ x → subst B x b) (cong-sym _ lemma) ⟩∎
    subst B (sym (cong proj₁ lemma)) b   ∎
    where
    lemma = right-inverse-of _

  set-set : ∀ a b₁ b₂ →
            set (set a b₁) b₂ ≡
            set a (subst B (remainder-set a b₁) b₂)
  set-set a b₁ b₂ =
    from (proj₁ (to (from (remainder a , b₁))) , b₂)      ≡⟨ cong from (Σ-≡,≡→≡ (remainder-set a b₁) refl) ⟩∎
    from (remainder a , subst B (remainder-set a b₁) b₂)  ∎

------------------------------------------------------------------------
-- Lens₃ combinators

-- Identity lens.

id₃ : ∀ {a} {A : Set a} → Lens₃ A (↑ a ⊤) (λ _ → A)
id₃ {A = A} =
  A          ↔⟨ inverse ×-left-identity ⟩
  ⊤     × A  ↔⟨ inverse ↑↔ ×-cong F.id ⟩□
  ↑ _ ⊤ × A  □

-- Composition of lenses.

infixr 9 _₃∘₃_

_₃∘₃_ : ∀ {a r₁ b₁ r₂ b₂} {A : Set a} {R₁ : Set r₁} {B₁ : R₁ → Set b₁}
          {R₂ : R₁ → Set r₂} {B₂ : (r : R₁) → R₂ r → Set b₂} →
        (∀ {r} → Lens₃ (B₁ r) (R₂ r) (B₂ r)) → Lens₃ A R₁ B₁ →
        Lens₃ A (Σ R₁ R₂) (uncurry B₂)
_₃∘₃_ {A = A} {R₁} {B₁} {R₂} {B₂} l₁ l₂ =
  A                             ↔⟨ l₂ ⟩
  Σ R₁ B₁                       ↔⟨ ∃-cong (λ _ → l₁) ⟩
  Σ R₁ (λ r → Σ (R₂ r) (B₂ r))  ↔⟨ Σ-assoc ⟩□
  Σ (Σ R₁ R₂) (uncurry B₂)      □

------------------------------------------------------------------------
-- Dependent lenses without "remainder types" visible in the type

-- The remainder /level/ is still visible in the type.

record Lens {a b} r
            (A : Set a) (B : A → Set b) : Set (a ⊔ lsuc (b ⊔ r)) where
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
    -- An isomorphism that specifies in what sense B′ is a variant of
    -- B.

    variant : ∀ {a} → B′ (remainder a) ↔ B a

  open _↔_

  -- Getter.

  get : (a : A) → B a
  get a = to variant (L.get a)

  -- Setter.

  set : (a : A) → B a → A
  set a b = L.set a (from variant b)

  -- Modifier.

  modify : (a : A) → (B a → B a) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b = L.remainder-set a (from variant b)

  -- Hence the type of the gettable part stays unchanged (up to
  -- isomorphism) after a set.

  B-set : ∀ {a b} → B (set a b) ↔ B a
  B-set {a} {b} =
    B (set a b)               ↔⟨ inverse variant ⟩
    B′ (remainder (set a b))  ↔⟨ ≡⇒↝ bijection (cong B′ (remainder-set a b)) ⟩
    B′ (remainder a)          ↔⟨ variant ⟩
    B a                       □

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    L.set a (from variant (to variant (L.get a)))  ≡⟨ cong (L.set a) (left-inverse-of variant _) ⟩
    L.set a (L.get a)                              ≡⟨ L.set-get a ⟩∎
    a                                              ∎

  get-set : ∀ a b → get (set a b) ≡ from B-set b
  get-set a b = cong (to variant) (
    L.get (L.set a b′)            ≡⟨ L.get-set _ _ ⟩
    subst B′ (sym eq) b′          ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ bijection eq _ _ ⟩∎
    from (≡⇒↝ _ (cong B′ eq)) b′  ∎)
    where
    b′ = from variant b
    eq = remainder-set a b

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to B-set b₂)
  set-set a b₁ b₂ =
    L.set (L.set a (from variant b₁)) (from variant b₂)        ≡⟨ L.set-set a (from variant b₁) (from variant b₂) ⟩
    L.set a (subst B′ (remainder-set a b₁) (from variant b₂))  ≡⟨ cong (L.set a) lemma ⟩∎
    L.set a (from variant (to B-set b₂))                       ∎
    where
    eq = remainder-set a b₁

    lemma =
      subst B′ eq (from variant b₂)                           ≡⟨ subst-in-terms-of-≡⇒↝ bijection eq _ _ ⟩
      to (≡⇒↝ bijection (cong B′ eq)) (from variant b₂)       ≡⟨ sym $ left-inverse-of variant _ ⟩∎
      from variant (to variant
        (to (≡⇒↝ bijection (cong B′ eq)) (from variant b₂)))  ∎

------------------------------------------------------------------------
-- Lens combinators

-- Conversion from Lens₃ to Lens.

Lens₃-to-Lens : ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
                (l : Lens₃ A R B) → Lens r A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens l = record
  { lens    = l
  ; variant = F.id
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
  { lens    = lens l₁ ₃∘₃ l₂
  ; variant = variant l₁
  }
  where open Lens

-- /Forward/ composition of lenses.
--
-- This function combines /Lens/es, but has a type which is arguably
-- more complicated. The type is also somewhat restricted: C is only
-- indexed by As, not Bs.

infixr 9 _∘_

_∘_ : ∀ {a b c r₁ r₂} {A : Set a} {B : A → Set b} {C : A → Set c} →
      (l₁ : Lens r₁ A B) →
      let open Lens l₁; open _↔_ lens in
      (∀ {r} → Lens r₂ (B′ r) (λ b′ → C (from (r , b′)))) →
      Lens _ A C
_∘_ {C = C} l₁ l₂ = record
  { lens    = lens l₂ ₃∘₃ lens l₁
  ; variant = λ {a} →
      B′ l₂ (remainder l₂ (Lens₃.get (lens l₁) a))  ↔⟨ variant l₂ ⟩
      C (from (lens l₁) (to (lens l₁) a))           ↝⟨ ≡⇒↝ _ (cong C (left-inverse-of (lens l₁) a)) ⟩□
      C a                                           □
  }
  where
  open _↔_
  open Lens

-- Lenses respect (certain) isomorphisms.
--
-- Note that B₁ and B₂ are required to have the same universe level.
-- One could avoid this restriction by adding another level parameter
-- to the definition of Lens.

cast : ∀ {r b}
         {a₁} {A₁ : Set a₁} {B₁ : A₁ → Set b}
         {a₂} {A₂ : Set a₂} {B₂ : A₂ → Set b}
       (A₁↔A₂ : A₁ ↔ A₂) →
       (∀ a → B₁ (_↔_.from A₁↔A₂ a) ↔ B₂ a) →
       Lens r A₁ B₁ → Lens _ A₂ B₂
cast {A₁ = A₁} {B₁} {A₂ = A₂} {B₂} A₁↔A₂ B₁↔B₂ l = record
  { lens    = A₂      ↔⟨ inverse A₁↔A₂ ⟩
              A₁      ↔⟨ lens ⟩□
              Σ R B′  □
  ; variant = λ {a} →
              B′ (remainder (from a))  ↔⟨ variant ⟩
              B₁ (from a)              ↔⟨ B₁↔B₂ _ ⟩□
              B₂ a                     □
  }
  where
  open _↔_ A₁↔A₂
  open Lens l

------------------------------------------------------------------------
-- An observation

-- Lens₃ lenses cannot (easily) be used to replace ordinary
-- projections: one cannot, in general, define lenses with the type of
-- the first projection from a Σ-type. For Lens lenses the situation
-- is more complicated.

module Observation where

  -- A Σ-type which is isomorphic to the unit type.

  Unit = Σ Bool λ b → b ≡ true

  -- All its inhabitants are equal.

  equal : (u₁ u₂ : Unit) → u₁ ≡ u₂
  equal (.true , refl) (.true , refl) = refl

  -- Its only inhabitant.

  u : Unit
  u = (true , refl)

  -- The first projection Lens₃ cannot be defined for Unit.

  not-proj₁₃ : ∀ {r} {R : Set r} → ¬ Lens₃ Unit R (λ _ → Bool)
  not-proj₁₃ l = Bool.true≢false (
    true                                                    ≡⟨ sym $ subst-const (sym $ remainder-set u true) ⟩
    subst (λ _ → Bool) (sym $ remainder-set u true) true    ≡⟨ sym $ get-set u true ⟩
    get (set u true)                                        ≡⟨ cong get (equal (set u true) (set u false)) ⟩
    get (set u false)                                       ≡⟨ get-set u false ⟩
    subst (λ _ → Bool) (sym $ remainder-set u false) false  ≡⟨ subst-const (sym $ remainder-set u false) ⟩∎
    false                                                   ∎)
    where
    open Lens₃ l

  -- The first projection Lens cannot be defined for Unit /if/ we
  -- assume that the K rule holds.

  not-proj₁ : ∀ {r} → K-rule r r → ¬ Lens r Unit (λ _ → Bool)
  not-proj₁ {r} k l = contradiction
    where
    open _↔_
    open Lens l

    -- Some lemmas.

    helper :
      {A C : Set} {B : Set r} {a₁ a₂ : A} {c : C}
      (P : B → Set) (f : A → B)
      (inv : ∀ {a} → P (f a) ↔ C) →
      Is-set B →
      a₁ ≡ a₂ → (eq : f a₁ ≡ f a₂) →
      to inv (from (≡⇒↝ _ (cong P eq)) (from inv c)) ≡ c
    helper {c = c} P _ inv B-is-set refl eq =
      to inv (from (≡⇒↝ _ (cong P eq))   (from inv c))  ≡⟨ cong (λ eq → to inv (from (≡⇒↝ _ (cong P eq)) _))
                                                                (_⇔_.to set⇔UIP B-is-set eq refl) ⟩
      to inv (from (≡⇒↝ _ (cong P refl)) (from inv c))  ≡⟨⟩
      to inv (from inv c)                               ≡⟨ right-inverse-of inv _ ⟩∎
      c                                                 ∎

    from-B-set : ∀ b → from (B-set {a = u} {b = b}) b ≡ b
    from-B-set b =
      helper B′
             remainder
             variant
             (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP k))
             (equal (set u b) u)
             (remainder-set u b)

    -- A contradiction.

    contradiction : ⊥
    contradiction = Bool.true≢false (
      true               ≡⟨ sym $ from-B-set true ⟩
      from B-set true    ≡⟨ sym $ get-set u true ⟩
      get (set u true)   ≡⟨ cong get (equal (set u true) (set u false)) ⟩
      get (set u false)  ≡⟨ get-set u false ⟩
      from B-set false   ≡⟨ from-B-set false ⟩∎
      false              ∎)

  -- If we assume univalence and extensionality, then we /can/ define
  -- two Lenses that have the same type signature as a first
  -- projection lens for Unit (modulo the presence of a lifting).

  possible : (Bool ≃ Bool) ↔ Bool →
             Univalence′ Bool Bool →
             Lens _ Unit (λ _ → ↑ _ Bool)
  possible [Bool≃Bool]↔Bool univ = record
    { R       = Set
    ; B′      = _≡ Bool
    ; lens    = Σ Bool (_≡ true)  ↝⟨ inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ⟩
                ⊤                 ↝⟨ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ⟩□
                Σ Set  (_≡ Bool)  □
    ; variant = Bool ≡ Bool  ↔⟨ ≡≃≃ univ ⟩
                Bool ≃ Bool  ↝⟨ [Bool≃Bool]↔Bool ⟩
                Bool         ↝⟨ inverse ↑↔ ⟩□
                ↑ _ Bool     □
    }

  proj₁₁ : Extensionality lzero lzero →
           Univalence′ Bool Bool →
           Lens _ Unit (λ _ → ↑ _ Bool)
  proj₁₁ ext = possible ([Bool≃Bool]↔Bool₁ ext)

  proj₁₂ : Extensionality lzero lzero →
           Univalence′ Bool Bool →
           Lens _ Unit (λ _ → ↑ _ Bool)
  proj₁₂ ext = possible ([Bool≃Bool]↔Bool₂ ext)

  -- One of the Lenses has a reasonable get function, and is thus a
  -- first projection lens:

  proj₁₁-get : ∀ {ext : Extensionality _ _} {univ b eq} →
               Lens.get (proj₁₁ ext univ) (b , eq) ≡ lift true
  proj₁₁-get = refl

  -- The other Lens doesn't have a reasonable get function:

  proj₁₂-get : ∀ {ext : Extensionality _ _} {univ b eq} →
               Lens.get (proj₁₂ ext univ) (b , eq) ≡ lift false
  proj₁₂-get = refl

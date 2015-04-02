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
open import Equality.Tactic equality-with-J as Tactic
open import Equivalence equality-with-J using (_≃_; module _≃_; ↔⇒≃)
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

  open _↔_

  -- The remainder.

  remainder : A → R
  remainder a = proj₁ (to lens a)

  -- Getter.

  get : (a : A) → B (remainder a)
  get a = proj₂ (to lens a)

  -- Setter.

  set : (a : A) → B (remainder a) → A
  set a b = from lens (remainder a , b)

  -- Modifier.

  modify : (a : A) → (B (remainder a) → B (remainder a)) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b =
    proj₁ (to lens (from lens (remainder a , b)))  ≡⟨ cong proj₁ (right-inverse-of lens _) ⟩∎
    remainder a                                    ∎

  -- A related isomorphism.

  B-set↔ : ∀ {a b} → B (remainder (set a b)) ↔ B (remainder a)
  B-set↔ = ≡⇒↝ _ (cong B (remainder-set _ _))

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    from lens (proj₁ (to lens a) , proj₂ (to lens a))  ≡⟨⟩
    from lens (to lens a)                              ≡⟨ left-inverse-of lens _ ⟩∎
    a                                                  ∎

  get-set₁ : ∀ a b → get (set a b) ≡ subst B (sym (remainder-set a b)) b
  get-set₁ a b =
    proj₂ (to lens (from lens (remainder a , b)))  ≡⟨ sym $ subst-application proj₂ (sym lemma) ⟩

    subst (B ⊚ proj₁) (sym lemma)
          (proj₂ {B = B} (remainder a , b))        ≡⟨⟩

    subst (B ⊚ proj₁) (sym lemma) b                ≡⟨ subst-∘ _ _ (sym lemma) ⟩

    subst B (cong proj₁ (sym lemma)) b             ≡⟨ cong (λ x → subst B x b) (cong-sym _ lemma) ⟩∎

    subst B (sym (cong proj₁ lemma)) b             ∎
    where
    lemma = right-inverse-of lens _

  get-set₂ : ∀ a b → get (set a b) ≡ from B-set↔ b
  get-set₂ a b =
    proj₂ (to lens (from lens (remainder a , b)))  ≡⟨ get-set₁ _ _ ⟩
    subst B (sym (cong proj₁ lemma)) b             ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ bijection (cong proj₁ lemma) _ _ ⟩∎
    from (≡⇒↝ _ (cong B (cong proj₁ lemma))) b     ∎
    where
    lemma = right-inverse-of lens _

  set-set₁ : ∀ a b₁ b₂ →
             set (set a b₁) b₂ ≡ set a (subst B (remainder-set a b₁) b₂)
  set-set₁ a b₁ b₂ =
    from lens (remainder (set a b₁) , b₂)    ≡⟨ cong (from lens) (Σ-≡,≡→≡ eq refl) ⟩∎
    from lens (remainder a , subst B eq b₂)  ∎
    where
    eq = remainder-set a b₁

  set-set₂ : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to B-set↔ b₂)
  set-set₂ a b₁ b₂ =
    set (set a b₁) b₂                  ≡⟨ set-set₁ _ _ _ ⟩
    set a (subst B eq b₂)              ≡⟨ cong (set a) (subst-in-terms-of-≡⇒↝ bijection eq _ _) ⟩∎
    set a (to (≡⇒↝ _ (cong B eq)) b₂)  ∎
    where
    eq = remainder-set a b₁

------------------------------------------------------------------------
-- Lens₃ combinators

-- Identity lens.

id₃ : ∀ {a} {A : Set a} → Lens₃ A ⊤ (λ _ → A)
id₃ {A = A} =
  A      ↔⟨ inverse ×-left-identity ⟩□
  ⊤ × A  □

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
  open _↔_

  -- The non-B part of the A value.

  remainder : A → R
  remainder = L.remainder

  field
    -- An equality that specifies in what sense B′ is a variant of B.
    --
    -- (This used to be a bijection, but it was turned into an
    -- equality in order to make it obvious that, if the K rule is
    -- enabled, then variant cannot do anything strange.)

    variant : ∀ {a} → B′ (remainder a) ≡ B a

  -- A corresponding isomorphism.

  variant↔ : ∀ {a} → B′ (remainder a) ↔ B a
  variant↔ = ≡⇒↝ _ variant

  -- Getter.

  get : (a : A) → B a
  get a = to variant↔ (L.get a)

  -- Setter.

  set : (a : A) → B a → A
  set a b = L.set a (from variant↔ b)

  -- Modifier.

  modify : (a : A) → (B a → B a) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b = L.remainder-set a (from variant↔ b)

  -- Hence the type of the gettable part stays unchanged after a set.

  B-set : ∀ {a b} → B (set a b) ≡ B a
  B-set {a} {b} =
    B (set a b)               ≡⟨ sym variant ⟩
    B′ (remainder (set a b))  ≡⟨ cong B′ (remainder-set a b) ⟩
    B′ (remainder a)          ≡⟨ variant ⟩∎
    B a                       ∎

  -- A corresponding isomorphism.

  B-set↔ : ∀ {a b} → B (set a b) ↔ B a
  B-set↔ = ≡⇒↝ _ B-set

  -- Unfolding lemmas for B-set↔.

  to-B-set↔ :
    ∀ {a b} →
    to (B-set↔ {a = a} {b = b}) ≡
    to variant↔ ⊚ to L.B-set↔ ⊚ from variant↔
  to-B-set↔ =
    to (≡⇒↝ _ (trans (sym variant) (trans eq variant)))       ≡⟨ ≡⇒↝-trans bijection {B≡C = trans eq variant} ⟩
    to (≡⇒↝ _ (trans eq variant)) ⊚ to (≡⇒↝ _ (sym variant))  ≡⟨ cong (to (≡⇒↝ _ (trans eq variant)) ⊚_) (≡⇒↝-sym bijection {eq = variant}) ⟩
    to (≡⇒↝ _ (trans eq variant)) ⊚ from variant↔             ≡⟨ cong (_⊚ from variant↔) (≡⇒↝-trans bijection {B≡C = variant}) ⟩∎
    to variant↔ ⊚ to (≡⇒↝ _ eq) ⊚ from variant↔               ∎
    where
    eq = cong B′ (remainder-set _ _)

  from-B-set↔ :
    ∀ {a b} →
    from (B-set↔ {a = a} {b = b}) ≡
    to variant↔ ⊚ from L.B-set↔ ⊚ from variant↔
  from-B-set↔ =
    from (≡⇒↝ _ (trans (sym variant) (trans eq variant)))         ≡⟨ sym $ ≡⇒↝-sym bijection {eq = trans (sym variant) (trans eq variant)} ⟩
    to (≡⇒↝ _ (sym (trans (sym variant) (trans eq variant))))     ≡⟨ cong (to ⊚ ≡⇒↝ bijection)
                                                                          (Tactic.prove (Sym (Trans (Sym (Lift variant))
                                                                                                    (Trans (Lift eq) (Lift variant))))
                                                                                        (Trans (Trans (Sym (Lift variant)) (Sym (Lift eq)))
                                                                                               (Lift variant))
                                                                                        refl) ⟩
    to (≡⇒↝ _ (trans (trans (sym variant) (sym eq)) variant))     ≡⟨ ≡⇒↝-trans bijection {B≡C = variant} ⟩
    to variant↔ ⊚ to (≡⇒↝ _ (trans (sym variant) (sym eq)))       ≡⟨ cong (to variant↔ ⊚_) (≡⇒↝-trans bijection {B≡C = sym eq}) ⟩
    to variant↔ ⊚ to (≡⇒↝ _ (sym eq)) ⊚ to (≡⇒↝ _ (sym variant))  ≡⟨ cong₂ (λ f g → to variant↔ ⊚ f ⊚ g)
                                                                           (≡⇒↝-sym bijection {eq = eq})
                                                                           (≡⇒↝-sym bijection {eq = variant}) ⟩∎
    to variant↔ ⊚ from (≡⇒↝ _ eq) ⊚ from variant↔                 ∎
    where
    eq = cong B′ (remainder-set _ _)

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    L.set a (from variant↔ (to variant↔ (L.get a)))  ≡⟨ cong (L.set a) (left-inverse-of variant↔ _) ⟩
    L.set a (L.get a)                                ≡⟨ L.set-get a ⟩∎
    a                                                ∎

  get-set : ∀ a b → get (set a b) ≡ from B-set↔ b
  get-set a b =
    to variant↔ (L.get (L.set a (from variant↔ b)))  ≡⟨ cong (to variant↔) $ L.get-set₂ _ _ ⟩
    to variant↔ (from (≡⇒↝ _ eq) (from variant↔ b))  ≡⟨ cong (_$ b) (sym from-B-set↔) ⟩∎
    from B-set↔ b                                    ∎
    where
    eq = cong B′ (remainder-set a b)

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to B-set↔ b₂)
  set-set a b₁ b₂ =
    L.set (L.set a (from variant↔ b₁)) (from variant↔ b₂)  ≡⟨ L.set-set₂ a (from variant↔ b₁) (from variant↔ b₂) ⟩
    L.set a (to L.B-set↔ (from variant↔ b₂))               ≡⟨ cong (L.set a) lemma ⟩∎
    L.set a (from variant↔ (to B-set↔ b₂))                 ∎
    where
    lemma =
      to L.B-set↔ (from variant↔ b₂)                                ≡⟨ sym $ left-inverse-of variant↔ _ ⟩
      from variant↔ (to variant↔ (to L.B-set↔ (from variant↔ b₂)))  ≡⟨ cong (from variant↔ ⊚ (_$ b₂)) $ sym to-B-set↔ ⟩∎
      from variant↔ (to B-set↔ b₂)                                  ∎

------------------------------------------------------------------------
-- Lens combinators

-- Conversion from Lens₃ to Lens.

Lens₃-to-Lens : ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
                (l : Lens₃ A R B) → Lens r A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens l = record
  { lens    = l
  ; variant = refl
  }

-- Identity lens.

id : ∀ {a} {A : Set a} → Lens lzero A (λ _ → A)
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
      B′ l₂ (remainder l₂ (Lens₃.get (lens l₁) a))  ≡⟨ variant l₂ ⟩
      C (from (lens l₁) (to (lens l₁) a))           ≡⟨ cong C (left-inverse-of (lens l₁) a) ⟩∎
      C a                                           ∎
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
       (∀ a → B₁ (_↔_.from A₁↔A₂ a) ≡ B₂ a) →
       Lens r A₁ B₁ → Lens _ A₂ B₂
cast {A₁ = A₁} {B₁} {A₂ = A₂} {B₂} A₁↔A₂ B₁≡B₂ l = record
  { lens    = A₂      ↔⟨ inverse A₁↔A₂ ⟩
              A₁      ↔⟨ lens ⟩□
              Σ R B′  □
  ; variant = λ {a} →
              B′ (remainder (from a))  ≡⟨ variant ⟩
              B₁ (from a)              ≡⟨ B₁≡B₂ _ ⟩∎
              B₂ a                     ∎
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
    subst (λ _ → Bool) (sym $ remainder-set u true) true    ≡⟨ sym $ get-set₁ u true ⟩
    get (set u true)                                        ≡⟨ cong get (equal (set u true) (set u false)) ⟩
    get (set u false)                                       ≡⟨ get-set₁ u false ⟩
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

    from-B-set : ∀ b → from (B-set↔ {a = u} {b = b}) b ≡ b
    from-B-set b =
      from B-set↔ b                                             ≡⟨ cong (_$ b) from-B-set↔ ⟩
      to variant↔ (from (Lens₃.B-set↔ lens) (from variant↔ b))  ≡⟨ helper B′
                                                                          remainder
                                                                          variant↔
                                                                          (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP k))
                                                                          (equal (set u b) u)
                                                                          (remainder-set u b) ⟩∎
      b                                                         ∎

    -- A contradiction.

    contradiction : ⊥
    contradiction = Bool.true≢false (
      true               ≡⟨ sym $ from-B-set true ⟩
      from B-set↔ true   ≡⟨ sym $ get-set u true ⟩
      get (set u true)   ≡⟨ cong get (equal (set u true) (set u false)) ⟩
      get (set u false)  ≡⟨ get-set u false ⟩
      from B-set↔ false  ≡⟨ from-B-set false ⟩∎
      false              ∎)

  -- If we assume univalence, then we /can/ define two Lenses that
  -- have the same type signature as a first projection lens for Unit
  -- (modulo the presence of a lifting).

  possible : (Bool ≃ Bool) ↔ Bool →
             Univalence lzero →
             Univalence (lsuc lzero) →
             Lens _ Unit (λ _ → ↑ _ Bool)
  possible [Bool≃Bool]↔Bool univ₀ univ₁ = record
    { R       = Set
    ; B′      = _≡ Bool
    ; lens    = Σ Bool (_≡ true)  ↝⟨ inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ⟩
                ⊤                 ↝⟨ _⇔_.to contractible⇔⊤↔ (singleton-contractible _) ⟩□
                Σ Set  (_≡ Bool)  □
    ; variant = ≃⇒≡ univ₁ (↔⇒≃ (
                  Bool ≡ Bool  ↔⟨ ≡≃≃ univ₀ ⟩
                  Bool ≃ Bool  ↝⟨ [Bool≃Bool]↔Bool ⟩
                  Bool         ↝⟨ inverse ↑↔ ⟩□
                  ↑ _ Bool     □))
    }

  proj₁₁ : Univalence lzero →
           Univalence (lsuc lzero) →
           Lens _ Unit (λ _ → ↑ _ Bool)
  proj₁₁ univ₀ univ₁ =
    possible ([Bool≃Bool]↔Bool₁
                (dependent-extensionality univ₁ (λ _ → univ₀)))
             univ₀ univ₁

  proj₁₂ : Univalence lzero →
           Univalence (lsuc lzero) →
           Lens _ Unit (λ _ → ↑ _ Bool)
  proj₁₂ univ₀ univ₁ =
    possible ([Bool≃Bool]↔Bool₂
                (dependent-extensionality univ₁ (λ _ → univ₀)))
             univ₀ univ₁

  -- One of the Lenses has a reasonable get function, and is thus a
  -- first projection lens:

  get-possible :
    ∀ (iso : (Bool ≃ Bool) ↔ Bool)
    (univ₀ : Univalence _) (univ₁ : Univalence _) p →
    Lens.get (possible iso univ₀ univ₁) p ≡
    lift (_↔_.to iso F.id)
  get-possible iso univ₀ univ₁ _ =
    to (≡⇒↝ _ (≃⇒≡ univ₁ (↔⇒≃ iso′))) refl  ≡⟨ cong (_$ refl) (≡⇒→-≃⇒≡ bijection univ₁) ⟩
    to iso′ refl                            ≡⟨ refl ⟩∎
    lift (to iso F.id)                      ∎
    where
    open _↔_

    iso′ = (inverse ↑↔ F.∘ iso) F.∘ _≃_.bijection (≡≃≃ univ₀)

  proj₁₁-get : ∀ (univ₀ : Univalence _) (univ₁ : Univalence _) p →
               Lens.get (proj₁₁ univ₀ univ₁) p ≡ lift true
  proj₁₁-get univ₀ univ₁ =
    get-possible ([Bool≃Bool]↔Bool₁ _) univ₀ univ₁

  -- The other Lens doesn't have a reasonable get function:

  proj₁₂-get : ∀ (univ₀ : Univalence _) (univ₁ : Univalence _) p →
               Lens.get (proj₁₂ univ₀ univ₁) p ≡ lift false
  proj₁₂-get univ₀ univ₁ =
    get-possible ([Bool≃Bool]↔Bool₂ _) univ₀ univ₁

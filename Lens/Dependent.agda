------------------------------------------------------------------------
-- Dependent lenses
------------------------------------------------------------------------

-- Some code below depends on both the K rule and resizing rules for
-- the propositional truncation. I don't know if these assumptions are
-- mutually consistent, but Andrea Vezzosi and I have discussed this,
-- and it seems plausible that some form of extensional type theory
-- with squash types would provide a model for these axioms.

{-# OPTIONS --without-K #-}

module Lens.Dependent where

open import Equality.Propositional
open import Logical-equivalence using (module _⇔_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_; module _↔_)
open import Bool equality-with-J
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Decision-procedures equality-with-J
open import Equality.Tactic equality-with-J as Tactic hiding (module Eq)
open import Equivalence equality-with-J as Eq using (_≃_; module _≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation equality-with-J as Trunc
open import Surjection equality-with-J using (module _↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent.Alternative as ND using (Iso-lens)

------------------------------------------------------------------------
-- Dependent lenses with "remainder types" visible in the type

-- If Lens₃ A R B is inhabited, then a value of type A can be split up
-- into a "remainder" r of type R and a value of type B r.

Lens₃ : ∀ {a r b} → Set a → (R : Set r) → (R → Set b) → Set _
Lens₃ A R B = A ≃ Σ R B

module Lens₃ {a r b} {A : Set a} {R : Set r} {B : R → Set b}
             (lens : Lens₃ A R B) where

  open _≃_

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

  B-set↔ : ∀ {a b} → B (remainder (set a b)) ≃ B (remainder a)
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
    subst B (sym (cong proj₁ lemma)) b             ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ equivalence (cong proj₁ lemma) _ _ ⟩∎
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
    set a (subst B eq b₂)              ≡⟨ cong (set a) (subst-in-terms-of-≡⇒↝ equivalence eq _ _) ⟩∎
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
-- Some Lens₃ properties

-- id₃ and _₃∘₃_ form a kind of monoid.

left-identity₃ :
  ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
  Extensionality (a ⊔ b ⊔ r) (a ⊔ b ⊔ r) →
  (l : Lens₃ A R B) →
  id₃ ₃∘₃ l
    ≡
  (A                      ↝⟨ l ⟩
   Σ R B                  ↝⟨ Σ-cong (inverse ×-right-identity) (λ _ → F.id) ⟩□
   Σ (R × ⊤) (B ⊚ proj₁)  □)
left-identity₃ ext _ = Eq.lift-equality ext refl

right-identity₃ :
  ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
  Extensionality (a ⊔ b ⊔ r) (a ⊔ b ⊔ r) →
  (l : Lens₃ A R B) →
  l ₃∘₃ id₃
    ≡
  (A                      ↝⟨ l ⟩
   Σ R B                  ↝⟨ Σ-cong (inverse ×-left-identity) (λ _ → F.id) ⟩□
   Σ (⊤ × R) (B ⊚ proj₂)  □)
right-identity₃ ext _ = Eq.lift-equality ext refl

associativity₃ :
  ∀ {a r₁ b₁ r₂ b₂ r₃ b₃}
    {A : Set a} {R₁ : Set r₁} {B₁ : R₁ → Set b₁}
    {R₂ : R₁ → Set r₂} {B₂ : (r₁ : R₁) → R₂ r₁ → Set b₂}
    {R₃ : (r₁ : R₁) → R₂ r₁ → Set r₃}
    {B₃ : (r₁ : R₁) (r₂ : R₂ r₁) → R₃ r₁ r₂ → Set b₃} →
  Extensionality (a ⊔ r₁ ⊔ r₂ ⊔ r₃ ⊔ b₃) (a ⊔ r₁ ⊔ r₂ ⊔ r₃ ⊔ b₃) →
  (l₁ : ∀ {r₁ r₂} → Lens₃ (B₂ r₁ r₂) (R₃ r₁ r₂) (B₃ r₁ r₂))
  (l₂ : ∀ {r} → Lens₃ (B₁ r) (R₂ r) (B₂ r))
  (l₃ : Lens₃ A R₁ B₁) →
  l₁ ₃∘₃ (l₂ ₃∘₃ l₃)
    ≡
  (A                                                             ↝⟨ (l₁ ₃∘₃ l₂) ₃∘₃ l₃ ⟩
   Σ (Σ R₁ (λ r₁ → Σ (R₂ r₁) (R₃ r₁))) (uncurry (uncurry ⊚ B₃))  ↝⟨ Σ-cong Σ-assoc (λ _ → F.id) ⟩□
   Σ (Σ (Σ R₁ R₂) (uncurry R₃)) (uncurry (uncurry B₃))           □)
associativity₃ ext _ _ _ = Eq.lift-equality ext refl

------------------------------------------------------------------------
-- Dependent lenses without "remainder types" visible in the type

Lens : ∀ {a b} (A : Set a) → (A → Set b) → Set (lsuc (lsuc (a ⊔ b)))
Lens {a} {b} A B =
  ∃ λ (R : Set (lsuc (a ⊔ b))) →
  ∃ λ (B′ : R → Set b) →
  ∃ λ (lens : Lens₃ A R B′) →
  ((r : R) → ∥ B′ r ∥ 1 b)
    ×
  (∀ a → B′ (Lens₃.remainder lens a) ≡ B a)

module Lens {a b} {A : Set a} {B : A → Set b} (l : Lens A B) where

  -- The remainder type: what remains of A when B is removed
  -- (roughly).

  R : Set (lsuc (a ⊔ b))
  R = proj₁ l

  -- A variant of B, indexed by Rs instead of As.

  B′ : R → Set b
  B′ = proj₁ (proj₂ l)

  -- The main lens isomorphism.

  lens : Lens₃ A R B′
  lens = proj₁ (proj₂ (proj₂ l))

  -- If the remainder type is inhabited, then the corresponding view
  -- should also be (merely) inhabited.

  inhabited : (r : R) → ∥ B′ r ∥ 1 b
  inhabited = proj₁ (proj₂ (proj₂ (proj₂ l)))

  private module L = Lens₃ lens
  open _≃_

  -- The "non-B" part of the A value.

  remainder : A → R
  remainder = L.remainder

  -- An equality that specifies in what sense B′ is a variant of B.
  --
  -- (This used to be a bijection, but it was turned into an
  -- equality in order to make it obvious that, if the K rule is
  -- enabled, then variant cannot do anything strange.)

  variant : ∀ a → B′ (remainder a) ≡ B a
  variant = proj₂ (proj₂ (proj₂ (proj₂ l)))

  -- A corresponding isomorphism.

  variant≃ : ∀ {a} → B′ (remainder a) ≃ B a
  variant≃ = ≡⇒↝ _ (variant _)

  -- A variant of variant.

  other-variant : ∀ r (b′ : B′ r) → B′ r ≡ B (from lens (r , b′))
  other-variant r b′ =
    B′ r                                       ≡⟨⟩
    B′ (proj₁ {B = B′} (r , b′))               ≡⟨ cong (B′ ⊚ proj₁) (sym $ right-inverse-of lens (r , b′)) ⟩
    B′ (proj₁ (to lens (from lens (r , b′))))  ≡⟨⟩
    B′ (remainder (from lens (r , b′)))        ≡⟨ variant (_≃_.from lens (r , b′)) ⟩∎
    B (from lens (r , b′))                     ∎

  -- Note that B ⊚ _≃_.from lens only depends on the "R part" of the
  -- argument.

  independent-of-B′ : (r : R) → Constant (B ⊚ _≃_.from lens ⊚ (r ,_))
  independent-of-B′ r b₁ b₂ =
    B (_≃_.from lens (r , b₁))  ≡⟨ sym $ other-variant _ _ ⟩
    B′ r                        ≡⟨ other-variant _ _ ⟩∎
    B (_≃_.from lens (r , b₂))  ∎

  -- Thus we can, with a fair number of assumptions, define a variant
  -- of B that only depends on R.
  --
  -- The assumptions:
  -- * Extensionality.
  -- * A resizing rule for the propositional truncation.
  -- * The K rule.

  module First-variant-of-B
           (ext    : Extensionality (lsuc (lsuc b)) (lsuc b))
           (resize : ∀ {r} → ∥ B′ r ∥ 1 b → ∥ B′ r ∥ 1 (lsuc (lsuc b)))
           (K      : K-rule (lsuc b) (lsuc b))
           where

    private
      B̲′ : (r : R) → ∥ B′ r ∥ 1 (lsuc b) → Set b
      B̲′ r =
        to (constant-function≃∥inhabited∥⇒inhabited
              (# 0) ext (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP K)))
           (B ⊚ _≃_.from lens ⊚ (r ,_) , independent-of-B′ r)

    B̲ : R → Set b
    B̲ r = B̲′ r (with-lower-level _ (resize (inhabited r)))

    -- This type family is pointwise equal to B′ (given the same
    -- assumptions).

    B′≡B̲ : ∀ r → B′ r ≡ B̲ r
    B′≡B̲ r = Trunc.prop-elim
      ext
      (λ ∥b′∥ → B′ r ≡ B̲′ r ∥b′∥)
      (λ _ → _⇔_.from set⇔UIP (_⇔_.to K⇔UIP K) _ _)
      (other-variant r)
      (resize (inhabited r))
      (with-lower-level _ (resize (inhabited r)))

  -- We can also use other assumptions:
  --
  -- * Extensionality.
  -- * Univalence.
  -- * A resizing rule for the propositional truncation.
  -- * B should be a family of sets.

  module Second-variant-of-B
           (ext    : Extensionality (lsuc (lsuc b)) (lsuc b))
           (univ   : Univalence b)
           (resize : ∀ {r} → ∥ B′ r ∥ 1 b → ∥ B′ r ∥ 1 (lsuc b))
           (B-set  : ∀ a → Is-set (B a))
           where

    private

      B̲-triple : (r : R) → ∃ λ (X : SET b) → B′ r ≡ proj₁ X
      B̲-triple r =
        to (coherently-constant-function≃∥inhabited∥⇒inhabited
              (# 0)
              ext
              (Σ-closure 3
                 (∃-H-level-H-level-1+
                    (lower-extensionality _ _ ext) univ 2)
                 (λ { (_ , X-set) → mono₁ 2 $
                      H-level-H-level-≡ʳ
                        (lower-extensionality _ _ ext) univ 1 X-set })))
           ( (λ b′ →   (B (_≃_.from lens (r , b′)) , B-set _)
                     , other-variant r b′)
           , (λ b′₁ b′₂ → Σ-≡,≡→≡
                (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂)
                         (_⇔_.to propositional⇔irrelevant
                            Is-set-is-propositional
                            _ _))
                (subst (λ X → B′ r ≡ proj₁ X)
                       (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _)
                       (other-variant r b′₁)                        ≡⟨ subst-∘ (B′ r ≡_) proj₁
                                                                               (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _) ⟩
                 subst (B′ r ≡_)
                       (cong proj₁ $
                          Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _)
                       (other-variant r b′₁)                        ≡⟨⟩

                 trans (other-variant r b′₁)
                       (cong proj₁ $
                          Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _)  ≡⟨ cong (trans (other-variant r b′₁)) $
                                                                         proj₁-Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _ ⟩
                 trans (other-variant r b′₁)
                       (independent-of-B′ r b′₁ b′₂)                ≡⟨⟩

                 trans (other-variant r b′₁)
                       (trans (sym $ other-variant r b′₁)
                              (other-variant r b′₂))                ≡⟨ sym $ trans-assoc _ _ (other-variant r b′₂) ⟩

                 trans (trans (other-variant r b′₁)
                              (sym $ other-variant r b′₁))
                       (other-variant r b′₂)                        ≡⟨ cong (flip trans (other-variant r b′₂)) $
                                                                         trans-symʳ (other-variant r b′₁) ⟩
                 trans refl (other-variant r b′₂)                   ≡⟨ trans-reflˡ _ ⟩∎

                 other-variant r b′₂                                ∎))
           , (λ b′₁ b′₂ b′₃ →
                let lemma =
                      trans (independent-of-B′ r b′₁ b′₂)
                            (independent-of-B′ r b′₂ b′₃)              ≡⟨⟩

                      trans (trans (sym $ other-variant r b′₁)
                                   (other-variant r b′₂))
                            (trans (sym $ other-variant r b′₂)
                                   (other-variant r b′₃))              ≡⟨ sym $ trans-assoc (independent-of-B′ r b′₁ b′₂)
                                                                                            (sym $ other-variant r b′₂)
                                                                                            (other-variant r b′₃) ⟩
                      trans (trans (trans (sym $ other-variant r b′₁)
                                          (other-variant r b′₂))
                                   (sym $ other-variant r b′₂))
                            (other-variant r b′₃)                      ≡⟨ cong (flip trans (other-variant r b′₃)) $
                                                                            trans-[trans]-sym (sym $ other-variant r b′₁)
                                                                                              (other-variant r b′₂) ⟩
                      trans (sym $ other-variant r b′₁)
                            (other-variant r b′₃)                      ≡⟨ refl ⟩∎

                      independent-of-B′ r b′₁ b′₃                      ∎
                in
                trans
                  (Σ-≡,≡→≡ (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _) _)
                  (Σ-≡,≡→≡ (Σ-≡,≡→≡ (independent-of-B′ r b′₂ b′₃) _) _)  ≡⟨ trans-Σ-≡,≡→≡ (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _)
                                                                                          (Σ-≡,≡→≡ (independent-of-B′ r b′₂ b′₃) _)
                                                                                          _ _ ⟩
                Σ-≡,≡→≡
                  (trans (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂) _)
                         (Σ-≡,≡→≡ (independent-of-B′ r b′₂ b′₃) _))
                  _                                                      ≡⟨ Σ-≡,≡→≡-cong (trans-Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₂)
                                                                                                        (independent-of-B′ r b′₂ b′₃)
                                                                                                        _ _)
                                                                                         refl ⟩
                Σ-≡,≡→≡
                  (Σ-≡,≡→≡ (trans (independent-of-B′ r b′₁ b′₂)
                                  (independent-of-B′ r b′₂ b′₃))
                           _)
                  _                                                      ≡⟨ Σ-≡,≡→≡-cong
                                                                              (Σ-≡,≡→≡-cong lemma
                                                                                            (_⇔_.to propositional⇔irrelevant
                                                                                               (mono₁ 0 (Is-set-is-propositional _ _))
                                                                                               _ _))
                                                                              (_⇔_.to propositional⇔irrelevant
                                                                                 (H-level-H-level-≡ʳ (lower-extensionality _ _ ext)
                                                                                                     univ 1 (B-set _) _ _)
                                                                                 _ _) ⟩∎
                Σ-≡,≡→≡ (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₃) _) _      ∎))
          (resize (inhabited r))
        where
        Is-set-is-propositional :
          {B : Set b} → Is-proposition (Is-set B)
        Is-set-is-propositional =
          H-level-propositional (lower-extensionality _ _ ext) 2

    B̲ : R → Set b
    B̲ r = proj₁ (proj₁ (B̲-triple r))

    B̲-set : ∀ r → Is-set (B̲ r)
    B̲-set r = proj₂ (proj₁ (B̲-triple r))

    B′≡B̲ : ∀ r → B′ r ≡ B̲ r
    B′≡B̲ r = proj₂ (B̲-triple r)

  -- Getter.

  get : (a : A) → B a
  get a = to variant≃ (L.get a)

  -- Setter.

  set : (a : A) → B a → A
  set a b = L.set a (from variant≃ b)

  -- Modifier.

  modify : (a : A) → (B a → B a) → A
  modify a f = set a (f (get a))

  -- Setting leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b = L.remainder-set a (from variant≃ b)

  -- Hence the type of the gettable part stays unchanged after a set.

  B-set : ∀ {a b} → B (set a b) ≡ B a
  B-set {a} {b} =
    B (set a b)               ≡⟨ sym (variant _) ⟩
    B′ (remainder (set a b))  ≡⟨ cong B′ (remainder-set a b) ⟩
    B′ (remainder a)          ≡⟨ variant _ ⟩∎
    B a                       ∎

  -- A corresponding isomorphism.

  B-set↔ : ∀ {a b} → B (set a b) ≃ B a
  B-set↔ = ≡⇒↝ _ B-set

  -- Unfolding lemmas for B-set↔.

  to-B-set↔ :
    ∀ {a b} →
    to (B-set↔ {a = a} {b = b}) ≡
    to variant≃ ⊚ to L.B-set↔ ⊚ from variant≃
  to-B-set↔ =
    to (≡⇒↝ _ (trans (sym (variant _)) (trans eq (variant _))))       ≡⟨ ≡⇒↝-trans equivalence {B≡C = trans eq (variant _)} ⟩
    to (≡⇒↝ _ (trans eq (variant _))) ⊚ to (≡⇒↝ _ (sym (variant _)))  ≡⟨ cong (to (≡⇒↝ _ (trans eq (variant _))) ⊚_)
                                                                              (≡⇒↝-sym equivalence {eq = variant _}) ⟩
    to (≡⇒↝ _ (trans eq (variant _))) ⊚ from variant≃                 ≡⟨ cong (_⊚ from variant≃) (≡⇒↝-trans equivalence {B≡C = variant _}) ⟩∎
    to variant≃ ⊚ to (≡⇒↝ _ eq) ⊚ from variant≃                       ∎
    where
    eq = cong B′ (remainder-set _ _)

  from-B-set↔ :
    ∀ {a b} →
    from (B-set↔ {a = a} {b = b}) ≡
    to variant≃ ⊚ from L.B-set↔ ⊚ from variant≃
  from-B-set↔ =
    from (≡⇒↝ _ (trans (sym (variant _)) (trans eq (variant _))))      ≡⟨ sym $ ≡⇒↝-sym equivalence {eq = trans (sym (variant _))
                                                                                                                (trans eq (variant _))} ⟩
    to (≡⇒↝ _ (sym (trans (sym (variant _)) (trans eq (variant _)))))  ≡⟨ cong (to ⊚ ≡⇒↝ equivalence)
                                                                               (Tactic.prove (Sym (Trans (Sym (Lift (variant _)))
                                                                                                         (Trans (Lift eq) (Lift (variant _)))))
                                                                                             (Trans (Trans (Sym (Lift (variant _)))
                                                                                                           (Sym (Lift eq)))
                                                                                                    (Lift (variant _)))
                                                                                             refl) ⟩
    to (≡⇒↝ _ (trans (trans (sym (variant _)) (sym eq)) (variant _)))  ≡⟨ ≡⇒↝-trans equivalence {B≡C = variant _} ⟩
    to variant≃ ⊚ to (≡⇒↝ _ (trans (sym (variant _)) (sym eq)))        ≡⟨ cong (to variant≃ ⊚_) (≡⇒↝-trans equivalence {B≡C = sym eq}) ⟩
    to variant≃ ⊚ to (≡⇒↝ _ (sym eq)) ⊚ to (≡⇒↝ _ (sym (variant _)))   ≡⟨ cong₂ (λ f g → to variant≃ ⊚ f ⊚ g)
                                                                                (≡⇒↝-sym equivalence {eq = eq})
                                                                                (≡⇒↝-sym equivalence {eq = variant _}) ⟩∎
    to variant≃ ⊚ from (≡⇒↝ _ eq) ⊚ from variant≃                      ∎
    where
    eq = cong B′ (remainder-set _ _)

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    L.set a (from variant≃ (to variant≃ (L.get a)))  ≡⟨ cong (L.set a) (left-inverse-of variant≃ _) ⟩
    L.set a (L.get a)                                ≡⟨ L.set-get a ⟩∎
    a                                                ∎

  get-set : ∀ a b → get (set a b) ≡ from B-set↔ b
  get-set a b =
    to variant≃ (L.get (L.set a (from variant≃ b)))  ≡⟨ cong (to variant≃) $ L.get-set₂ _ _ ⟩
    to variant≃ (from (≡⇒↝ _ eq) (from variant≃ b))  ≡⟨ cong (_$ b) (sym from-B-set↔) ⟩∎
    from B-set↔ b                                    ∎
    where
    eq = cong B′ (remainder-set a b)

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to B-set↔ b₂)
  set-set a b₁ b₂ =
    L.set (L.set a (from variant≃ b₁)) (from variant≃ b₂)  ≡⟨ L.set-set₂ a (from variant≃ b₁) (from variant≃ b₂) ⟩
    L.set a (to L.B-set↔ (from variant≃ b₂))               ≡⟨ cong (L.set a) lemma ⟩∎
    L.set a (from variant≃ (to B-set↔ b₂))                 ∎
    where
    lemma =
      to L.B-set↔ (from variant≃ b₂)                                ≡⟨ sym $ left-inverse-of variant≃ _ ⟩
      from variant≃ (to variant≃ (to L.B-set↔ (from variant≃ b₂)))  ≡⟨ cong (from variant≃ ⊚ (_$ b₂)) $ sym to-B-set↔ ⟩∎
      from variant≃ (to B-set↔ b₂)                                  ∎

------------------------------------------------------------------------
-- Some lens isomorphisms

-- If B x is a proposition for all x, then Lens A B is isomorphic to
-- (x : A) → B x (assuming extensionality and univalence).

lens-to-proposition↔get :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Univalence b →
  (∀ x → Is-proposition (B x)) →
  Lens A B ↔ ((x : A) → B x)
lens-to-proposition↔get {a} {b} {A} {B} ext univ₁ univ₂ B-prop =
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥ 1 _)
     ×
   (∀ a → B′ (Lens₃.remainder lens a) ≡ B a))                ↔⟨ (∃-cong λ _ → ∃-cong λ B′ → ∃-cong λ l → ∃-cong λ _ →
                                                                 Eq.Π-preserves (lower-extensionality lzero (lsuc a) ext) l λ _ →
                                                                 ≡⇒↝ _ $ cong (λ x → _ ≡ B x) $ sym $ _≃_.left-inverse-of l _) ⟩
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥ 1 _)
     ×
   (∀ p → B′ (proj₁ p) ≡ B (_≃_.from lens p)))               ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → currying) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥ 1 _)
     ×
   ((r : R) (b : B′ r) → B′ r ≡ B (_≃_.from lens (r , b))))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ΠΣ-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) →
      ∥ B′ r ∥ 1 _
        ×
      ((b : B′ r) → B′ r ≡ B (_≃_.from lens (r , b)))))      ↔⟨ (∃-cong λ _ → ∃-cong λ B′ → ∃-cong λ lens →
                                                                 Eq.∀-preserves (lower-extensionality lzero (lsuc a) ext) $
                                                                 lemma₁ B′ lens) ⟩
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∃ λ (⊤≃B′ : ⊤ ≃ B′ r) →
                B (_≃_.from lens (r , _≃_.to ⊤≃B′ _))))      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ΠΣ-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ∃ λ (⊤≃B′ : ∀ r → ⊤ ≃ B′ r) →
   ∀ r → B (_≃_.from lens (r , _≃_.to (⊤≃B′ r) _)))          ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (⊤≃B′ : ∀ r → ⊤ ≃ B′ r) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ∀ r → B (_≃_.from lens (r , _≃_.to (⊤≃B′ r) _)))          ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ ⊤≃B′ →
                                                                 Σ-cong (Eq.≃-preserves-bijections ext F.id
                                                                           (drop-⊤-right (λ r → inverse (⊤≃B′ r)))) λ _ →
                                                                 F.id) ⟩
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   (∀ r → ⊤ ≃ B′ r)
     ×
   ∃ λ (lens : A ≃ R) →
   ∀ r → B (_≃_.from lens r))                                ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ R) →
   (∀ r → ⊤ ≃ B′ r)
     ×
   ∀ r → B (_≃_.from lens r))                                ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (lens : A ≃ R) →
   ∃ λ (B′ : R → Set _) →
   (∀ r → ⊤ ≃ B′ r)
     ×
   ∀ r → B (_≃_.from lens r))                                ↝⟨ Σ-assoc ⟩

  (Σ (∃ λ (R : Set _) → A ≃ R) λ { (R , lens) →
   ∃ λ (B′ : R → Set _) →
   (∀ r → ⊤ ≃ B′ r)
     ×
   ∀ r → B (_≃_.from lens r) })                              ↝⟨ drop-⊤-left-Σ (other-singleton-with-≃-↔-⊤ ext univ₁) ⟩

  (∃ λ (B′ : ↑ _ A → Set _) →
   (∀ a → ⊤ ≃ B′ a)
     ×
   (∀ a → B (lower a)))                                      ↝⟨ Σ-assoc ⟩

  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ⊤ ≃ B′ a)
    ×
  (∀ a → B (lower a))                                        ↔⟨ ((∃-cong λ _ → Eq.∀-preserves (lower-extensionality lzero _ ext) λ _ →
                                                                  Eq.≃-preserves (lower-extensionality _ _ ext) (inverse $ Eq.↔⇒≃ Bij.↑↔) F.id)
                                                                   ×-cong
                                                                 Eq.Π-preserves (lower-extensionality lzero _ ext)
                                                                                (Eq.↔⇒≃ Bij.↑↔) (λ _ → F.id)) ⟩
  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ↑ _ ⊤ ≃ B′ a)
    ×
  (∀ a → B a)                                                ↔⟨ (∃-cong λ B′ →
                                                                 Eq.∀-preserves (lower-extensionality lzero (lsuc a) ext) λ _ →
                                                                 inverse $ ≡≃≃ univ₂)
                                                                  ×-cong
                                                                F.id ⟩
  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ↑ _ ⊤ ≡ B′ a)
    ×
  (∀ a → B a)                                                ↔⟨ (∃-cong λ _ →
                                                                 Eq.extensionality-isomorphism (lower-extensionality lzero (lsuc a) ext))
                                                                  ×-cong
                                                                F.id ⟩
  (∃ λ (B′ : ↑ _ A → Set _) → const (↑ _ ⊤) ≡ B′)
    ×
  (∀ a → B a)                                                ↝⟨ drop-⊤-left-× (λ _ →
                                                                inverse $ _⇔_.to contractible⇔⊤↔ (other-singleton-contractible _)) ⟩□
  (∀ a → B a)                                                □
  where
  lemma₂ : {R : Set _} (B′ : R → Set _) (r : R) → _
  lemma₂ B′ r =
    (∥ B′ r ∥ 1 _ × Is-proposition (B′ r))  ↝⟨ ×-comm ⟩

    (Is-proposition (B′ r) × ∥ B′ r ∥ 1 _)  ↝⟨ (∃-cong λ B′-prop → ∥∥↔ b (lower-extensionality (lsuc a) _ ext) B′-prop) ⟩

    (Is-proposition (B′ r) × B′ r)          ↔⟨ _↠_.from (Eq.≃↠⇔ (Σ-closure 1 (H-level-propositional (lower-extensionality _ _ ext) 1) λ B′-prop →
                                                                 B′-prop)
                                                                (H-level-propositional (lower-extensionality _ _ ext) 0))
                                                        (record { to   = uncurry propositional⇒inhabited⇒contractible
                                                                ; from = λ B′-contr → mono₁ 0 B′-contr , proj₁ B′-contr
                                                                }) ⟩
    Contractible (B′ r)                     ↝⟨ contractible↔⊤≃ (lower-extensionality _ _ ext) ⟩□

    ⊤ ≃ B′ r                                □

  lemma₁ : {R : Set _} (B′ : R → Set _) (lens : A ≃ Σ R B′) (r : R) → _
  lemma₁ B′ lens r =
    ∥ B′ r ∥ 1 _
      ×
    ((b′ : B′ r) → B′ r ≡ B (_≃_.from lens (r , b′)))  ↝⟨ (∃-cong λ _ → Eq.∀-preserves (lower-extensionality _ (lsuc a) ext) λ _ →
                                                           ≡≃≃ univ₂) ⟩
    ∥ B′ r ∥ 1 _
      ×
    ((b′ : B′ r) → B′ r ≃ B (_≃_.from lens (r , b′)))  ↝⟨ (∃-cong λ _ → Eq.∀-preserves (lower-extensionality _ _ ext) λ b′ →
                                                           _↠_.from (Eq.≃↠⇔ (Eq.right-closure (lower-extensionality _ _ ext)
                                                                                              0
                                                                                              (B-prop _))
                                                                            (×-closure 1
                                                                                       (H-level-propositional (lower-extensionality _ _ ext) 1)
                                                                                       (B-prop _)))
                                                                    (record
                                                                       { to   = λ eq →   H-level.respects-surjection
                                                                                           (_≃_.surjection (inverse eq))
                                                                                           1
                                                                                           (B-prop _)
                                                                                       , _≃_.to eq b′
                                                                       ; from = λ { (B′-prop , b) → _↠_.from (Eq.≃↠⇔ B′-prop (B-prop _))
                                                                                                             (record { to   = const b
                                                                                                                     ; from = const b′
                                                                                                                     }) }
                                                                       })) ⟩
    ∥ B′ r ∥ 1 _
      ×
    ((b′ : B′ r) → Is-proposition (B′ r)
                     ×
                   B (_≃_.from lens (r , b′)))         ↔⟨ (∃-cong λ _ → ΠΣ-comm) ⟩

    ∥ B′ r ∥ 1 _
      ×
    (B′ r → Is-proposition (B′ r))
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↝⟨ (∃-cong λ _ →
                                                           _↠_.from (Eq.≃↠⇔ (Π-closure (lower-extensionality _ _ ext) 1 λ _ →
                                                                             H-level-propositional (lower-extensionality _ _ ext) 1)
                                                                            (H-level-propositional (lower-extensionality _ _ ext) 1))
                                                                    (record { to   = λ B′-prop → [inhabited⇒+]⇒+ 0 B′-prop
                                                                            ; from = λ B′-prop _ → B′-prop
                                                                            })
                                                             ×-cong
                                                           F.id) ⟩
    ∥ B′ r ∥ 1 _
      ×
    Is-proposition (B′ r)
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ ×-assoc ⟩

    (∥ B′ r ∥ 1 _
      ×
     Is-proposition (B′ r))
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ lemma₂ B′ r ×-cong F.id ⟩

    (⊤ ≃ B′ r)
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ (∃-cong λ ⊤≃B′ → drop-⊤-left-Π (lower-extensionality _ _ ext)
                                                                                         (_≃_.bijection $ inverse ⊤≃B′)) ⟩□
    (∃ λ (⊤≃B′ : ⊤ ≃ B′ r) →
     B (_≃_.from lens (r , _≃_.to ⊤≃B′ _)))            □

-- If B x is contractible for all x, then Lens A B is isomorphic to ⊤
-- (assuming extensionality and univalence).

lens-to-contractible↔⊤ :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Univalence b →
  (∀ x → Contractible (B x)) →
  Lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} ext univ₁ univ₂ cB =
  Lens A B         ↝⟨ lens-to-proposition↔get ext univ₁ univ₂ (mono₁ 0 ⊚ cB) ⟩
  ((x : A) → B x)  ↔⟨ (Eq.∀-preserves (lower-extensionality _ _ ext) λ _ →
                       Eq.↔⇒≃ $ inverse $ _⇔_.to contractible⇔⊤↔ (cB _)) ⟩
  (A → ⊤)          ↝⟨ →-right-zero ⟩□
  ⊤                □

-- Lens A (const ⊥) is isomorphic to ¬ A (assuming extensionality and
-- univalence).

lens-to-⊥↔¬ :
  ∀ {a b} {A : Set a} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  Univalence (lsuc (a ⊔ b)) →
  Univalence b →
  Lens A (const (⊥ {ℓ = b})) ↔ ¬ A
lens-to-⊥↔¬ {A = A} ext univ₁ univ₂ =
  Lens A (const ⊥)  ↝⟨ lens-to-proposition↔get ext univ₁ univ₂ (λ _ → ⊥-propositional) ⟩
  (A → ⊥)           ↝⟨ inverse $ ¬↔→⊥ (lower-extensionality _ _ ext) ⟩□
  ¬ A               □

-- If we assume that equality with the codomain type is propositional,
-- then non-dependent dependent lenses are isomorphic to non-dependent
-- lenses (assuming extensionality and resizing rules for the
-- propositional truncation).
--
-- TODO: Can this be proved without assuming that equality with the
-- codomain type is propositional? If not, can the definition of Lens
-- be changed so that it can be proved?

non-dependent-lenses-isomorphic :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 b → ∥ B ∥ 1 (a ⊔ b)) →
  ({B′ : Set b} → ∥ B′ ∥ 1 b → ∥ B′ ∥ 1 (lsuc b)) →
  (∀ {B′} → Is-proposition (B′ ≡ B)) →
  ∃ λ (iso : Lens A (const B) ↔ Iso-lens A B) →
    ∀ {l a} → Lens.get l a ≡ ND.Iso-lens.get (_↔_.to iso l) a
non-dependent-lenses-isomorphic {a} {A = A} {B}
                                ext resize₁ resize₂ ≡B-prop =
  (Lens A (const B)  ↝⟨ ∃-cong lemma ⟩□
   Iso-lens A B      □)
  , λ {l a} →
    let p = variant l a
        q = Trunc.rec _ _ (resize₂ (inhabited l (remainder l a)))
    in
    _≃_.to (≡⇒↝ _ p) (proj₂ (_≃_.to (lens l) a))  ≡⟨ cong (λ eq → _≃_.to (≡⇒↝ _ eq) (proj₂ (_≃_.to (lens l) a)))
                                                          (_⇔_.to propositional⇔irrelevant ≡B-prop p q) ⟩∎
    _≃_.to (≡⇒↝ _ q) (proj₂ (_≃_.to (lens l) a))  ∎
  where
  open Lens

  lemma = λ R →
    (∃ λ (B′ : R → Set _) →
     ∃ λ (lens : A ≃ Σ R B′) →
     ((r : R) → ∥ B′ r ∥ 1 _)
       ×
     (∀ a → B′ (Lens₃.remainder lens a) ≡ B))     ↔⟨ (∃-cong λ _ → ∃-cong λ l → ∃-cong λ _ →
                                                      Eq.Π-preserves (lower-extensionality lzero (lsuc a) ext) l (λ _ → F.id)) ⟩
    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥ 1 _)
       ×
     (∀ p → B′ (proj₁ p) ≡ B))                    ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → currying) ⟩

    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥ 1 _)
       ×
     ((r : R) → B′ r → B′ r ≡ B))                 ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ inh →
                                                      Eq.∀-preserves (lower-extensionality lzero (lsuc a) ext) λ r →
                                                      _↠_.from (Eq.≃↠⇔ (Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
                                                                        ≡B-prop)
                                                                       ≡B-prop)
                                                        (record { from = λ B′r≡B     → const B′r≡B
                                                                ; to   = λ B′r→B′r≡B → Trunc.rec ≡B-prop B′r→B′r≡B (resize₂ (inh r))
                                                                })) ⟩
    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥ 1 _)
       ×
     ((r : R) → B′ r ≡ B))                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → B′ r ≡ B)
       ×
     ((r : R) → ∥ B′ r ∥ 1 _))                    ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (B′ : R → Set _) →
     ((r : R) → B′ r ≡ B)
       ×
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥ 1 _))                    ↔⟨ (∃-cong λ _ →
                                                        Σ-cong (Eq.extensionality-isomorphism
                                                                  (lower-extensionality lzero (lsuc a) ext)) λ B′≡B →
                                                        Eq.≃-preserves ext F.id (∃-cong λ _ → ≡⇒↝ _ (B′≡B _))
                                                          ×-cong
                                                        Eq.∀-preserves (lower-extensionality lzero (lsuc a) ext) (λ _ →
                                                          Eq.↔⇒≃ $ ∥∥-cong (lower-extensionality (lsuc a) _ ext)
                                                                           (≡⇒↝ _ (B′≡B _))))  ⟩
    (∃ λ (B′ : R → Set _) →
     B′ ≡ const B
       ×
     (A ≃ (R × B))
       ×
     (R → ∥ B ∥ 1 _))                             ↝⟨ Σ-assoc ⟩

    ((∃ λ (B′ : R → Set _) → B′ ≡ const B)
       ×
     (A ≃ (R × B))
       ×
     (R → ∥ B ∥ 1 _))                             ↝⟨ drop-⊤-left-× (λ _ →
                                                     inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _)) ⟩
    ((A ≃ (R × B))
       ×
     (R → ∥ B ∥ 1 _))                             ↔⟨ (∃-cong λ _ →
                                                      _↠_.from (Eq.≃↠⇔ (Π-closure (lower-extensionality lzero (lsuc a) ext) 1 λ _ →
                                                                        truncation-has-correct-h-level 1 (lower-extensionality (lsuc a) _ ext))
                                                                       (Π-closure ext 1 λ _ →
                                                                        truncation-has-correct-h-level 1 (lower-extensionality lzero _ ext)))
                                                        (record { from = λ R→∥B∥ r → with-lower-level a (R→∥B∥ r)
                                                                ; to   = λ R→∥B∥ r → resize₁ (R→∥B∥ r)
                                                                })) ⟩□
    ((A ≃ (R × B))
       ×
     (R → ∥ B ∥ 1 _))                             □

-- Non-dependent dependent lenses are isomorphic to non-dependent
-- lenses, assuming extensionality, resizing rules for the
-- propositional truncation, and the K rule.

non-dependent-lenses-isomorphic-K :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (lsuc (a ⊔ b)) →
  (∥ B ∥ 1 b → ∥ B ∥ 1 (a ⊔ b)) →
  ({B′ : Set b} → ∥ B′ ∥ 1 b → ∥ B′ ∥ 1 (lsuc b)) →
  K-rule (lsuc b) (lsuc b) →
  ∃ λ (iso : Lens A (const B) ↔ Iso-lens A B) →
    ∀ {l a} → Lens.get l a ≡ ND.Iso-lens.get (_↔_.to iso l) a
non-dependent-lenses-isomorphic-K ext resize₁ resize₂ K =
  non-dependent-lenses-isomorphic ext resize₁ resize₂
    (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP K) _ _)

------------------------------------------------------------------------
-- Lens combinators

-- Conversion from Lens₃ to Lens (depends on extensionality).

Lens₃-to-Lens :
  ∀ {a b} {A : Set a} {R : Set (lsuc (a ⊔ b))} {B : R → Set b} →
  Extensionality (lsuc b) b →
  (l : Lens₃ A R B) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens {A = A} {R} {B} ext l =
  _ ,
  _ ,
  (A                                                  ↝⟨ l ⟩
   Σ R B                                              ↔⟨ ∃-cong (λ _ → inverse (∥∥×↔ ext)) ⟩
   Σ R (λ r → ∥ B r ∥ 1 _ × B r)                      ↔⟨ Σ-assoc ⟩□
   Σ (Σ R (λ r → ∥ B r ∥ 1 _)) (λ { (r , _) → B r })  □) ,
  proj₂ ,
  λ _ → refl

-- A variant of Lens₃-to-Lens.

Lens₃-to-Lens′ :
  ∀ {a r b} {A : Set (a ⊔ r)} {R : Set r} {B : R → Set b} →
  Extensionality (lsuc b) b →
  (l : Lens₃ A R B) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens′ {A = A} {R} {B} ext l =
  Lens₃-to-Lens ext
    (A                                 ↝⟨ l ⟩
     Σ R B                             ↝⟨ Σ-cong (inverse Bij.↑↔) (λ _ → F.id) ⟩□
     Σ (↑ _ R) (λ { (lift r) → B r })  □)

-- Identity lens (defined using extensionality).

id : ∀ {a} {A : Set a} →
     Extensionality (lsuc a) a →
     Lens A (λ _ → A)
id {A = A} ext = Lens₃-to-Lens′ ext
  (A      ↔⟨ inverse ×-left-identity ⟩□
   ⊤ × A  □)

-- Alternative conversion from Lens₃ to Lens.

Lens₃-to-Lens-if-inhabited :
  ∀ {a b} {A : Set a} {R : Set (lsuc (a ⊔ b))} {B : R → Set b} →
  (l : Lens₃ A R B) →
  (∀ r → ∥ B r ∥ 1 b) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens-if-inhabited {A = A} {R} {B} l inh =
  _ ,
  _ ,
  l ,
  inh ,
  λ _ → refl

-- A variant of Lens₃-to-Lens-if-inhabited.

Lens₃-to-Lens-if-inhabited′ :
  ∀ {a r b} {A : Set (a ⊔ r)} {R : Set r} {B : R → Set b} →
  (l : Lens₃ A R B) →
  (∀ r → ∥ B r ∥ 1 b) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens-if-inhabited′ {A = A} {R} {B} l inh =
  Lens₃-to-Lens-if-inhabited
    (A                                 ↝⟨ l ⟩
     Σ R B                             ↝⟨ Σ-cong (inverse Bij.↑↔) (λ _ → F.id) ⟩□
     Σ (↑ _ R) (λ { (lift r) → B r })  □)
    (λ { (lift r) → inh r })

-- Identity lens for merely inhabited types.

id-if-inhabited : ∀ {a} {A : Set a} →
                  ∥ A ∥ 1 a → Lens A (λ _ → A)
id-if-inhabited {A = A} ∥a∥ =
  Lens₃-to-Lens-if-inhabited′
    (A      ↔⟨ inverse ×-left-identity ⟩□
     ⊤ × A  □)
    (const ∥a∥)

-- Composition of lenses.
--
-- Note that this function combines a family of Lenses and a Lens₃.

infixr 9 _∘₃_

_∘₃_ :
  ∀ {a b c} {A : Set (a ⊔ b ⊔ c)} {R : Set (lsuc (a ⊔ b ⊔ c))}
    {B : R → Set (b ⊔ c)} {C : {r : R} → B r → Set c} →
  (∀ {r} → Lens (B r) C) → (l₂ : Lens₃ A R B) →
  Lens A (C ⊚ Lens₃.get l₂)
_∘₃_ {R = R} l₁ l₂ =
  (∃ λ (r : R) → Lens.R (l₁ {r = r})) ,
  (λ { (r₁ , r₂) → Lens.B′ (l₁ {r = r₁}) r₂ }) ,
  Lens.lens l₁ ₃∘₃ l₂ ,
  Lens.inhabited l₁ ⊚ proj₂ ,
  Lens.variant l₁ ⊚ Lens₃.get l₂

-- /Forward/ composition of lenses.
--
-- This function combines /Lens/es, but has a type which is arguably
-- more complicated. The type is also somewhat restricted: C is only
-- indexed by As, not Bs.

infixr 9 _∘_

_∘_ : ∀ {a b c}
        {A : Set (a ⊔ b ⊔ c)} {B : A → Set (b ⊔ c)} {C : A → Set c} →
      (l₁ : Lens A B) →
      let open Lens l₁; open _≃_ lens in
      (∀ {r} → Lens (B′ r) (λ b′ → C (from (r , b′)))) →
      Lens A C
_∘_ {C = C} l₁ l₂ =
  (∃ λ (r₁ : R l₁) → Lens.R (l₂ {r = r₁})) ,
  (λ { (r₁ , r₂) → B′ (l₂ {r = r₁}) r₂ }) ,
  lens l₂ ₃∘₃ lens l₁ ,
  (λ { (_ , r₂) → inhabited l₂ r₂ }) ,
  λ a →
    B′ l₂ (remainder l₂ (Lens₃.get (lens l₁) a))  ≡⟨ variant l₂ _ ⟩
    C (from (lens l₁) (to (lens l₁) a))           ≡⟨ cong C (left-inverse-of (lens l₁) a) ⟩∎
    C a                                           ∎
  where
  open _≃_
  open Lens

-- Lenses respect (certain) equivalences.

cast : ∀ {a b} {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b}
       (A₁≃A₂ : A₁ ≃ A₂) →
       (∀ a → B₁ (_≃_.from A₁≃A₂ a) ≡ B₂ a) →
       Lens A₁ B₁ → Lens A₂ B₂
cast {A₁ = A₁} {A₂} {B₁} {B₂} A₁≃A₂ B₁≡B₂ l =
  _ ,
  _ ,
  (A₂      ↝⟨ inverse A₁≃A₂ ⟩
   A₁      ↝⟨ lens ⟩□
   Σ R B′  □) ,
  inhabited ,
  λ a →
    B′ (remainder (from a))  ≡⟨ variant _ ⟩
    B₁ (from a)              ≡⟨ B₁≡B₂ _ ⟩∎
    B₂ a                     ∎
  where
  open _≃_ A₁≃A₂
  open Lens l

------------------------------------------------------------------------
-- An observation

-- Lens₃ lenses cannot (easily) be used to replace ordinary
-- projections: one cannot, in general, define lenses with the type of
-- the first projection from a Σ-type. For Lens lenses the situation
-- is unclear.

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

  not-proj₁ : K-rule (# 1) (# 1) → ¬ Lens Unit (λ _ → Bool)
  not-proj₁ k l = contradiction
    where
    open _≃_
    open Lens l

    -- Some lemmas.

    helper :
      {A C : Set} {B : Set₁} {a₁ a₂ : A} {c : C}
      (P : B → Set) (f : A → B)
      (inv : ∀ {a} → P (f a) ≃ C) →
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
      to variant≃ (from (Lens₃.B-set↔ lens) (from variant≃ b))  ≡⟨ helper B′
                                                                          remainder
                                                                          variant≃
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

  -- TODO: What is the situation in the presence of univalence?

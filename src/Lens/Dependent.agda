------------------------------------------------------------------------
-- Dependent lenses
------------------------------------------------------------------------

-- Some code below depends on the K rule. I don't know if the K rule,
-- the propositional truncation, and extensionality are mutually
-- consistent, but Andrea Vezzosi and I have discussed this, and it
-- seems plausible that some form of extensional type theory with
-- squash types would provide a model for these things. (I don't know
-- if the interval could be modelled in this way, but the interval is
-- not needed here, only extensionality.)

{-# OPTIONS --without-K #-}

module Lens.Dependent where

open import Equality.Propositional
open import Interval using (ext)
open import H-level.Truncation.Propositional as Trunc
open import Logical-equivalence using (module _⇔_)
open import Prelude hiding (id; Unit) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bij using (_↔_; module _↔_)
open import Bool equality-with-J
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Decision-procedures equality-with-J
open import Equality.Tactic equality-with-J as Tactic hiding (module Eq)
open import Equivalence equality-with-J as Eq using (_≃_; module _≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
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

  codomain-set-≃ : ∀ {a b} → B (remainder (set a b)) ≃ B (remainder a)
  codomain-set-≃ = ≡⇒↝ _ (cong B (remainder-set _ _))

  -- Some lens laws.

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    from lens (proj₁ (to lens a) , proj₂ (to lens a))  ≡⟨⟩
    from lens (to lens a)                              ≡⟨ left-inverse-of lens _ ⟩∎
    a                                                  ∎

  get-set₁ : ∀ a b → get (set a b) ≡ subst B (sym (remainder-set a b)) b
  get-set₁ a b =
    proj₂ (to lens (from lens (remainder a , b)))  ≡⟨ sym $ dependent-cong proj₂ (sym lemma) ⟩

    subst (B ⊚ proj₁) (sym lemma)
          (proj₂ {B = B} (remainder a , b))        ≡⟨⟩

    subst (B ⊚ proj₁) (sym lemma) b                ≡⟨ subst-∘ _ _ (sym lemma) ⟩

    subst B (cong proj₁ (sym lemma)) b             ≡⟨ cong (λ x → subst B x b) (cong-sym _ lemma) ⟩∎

    subst B (sym (cong proj₁ lemma)) b             ∎
    where
    lemma = right-inverse-of lens _

  get-set₂ : ∀ a b → get (set a b) ≡ from codomain-set-≃ b
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

  set-set₂ : ∀ a b₁ b₂ →
             set (set a b₁) b₂ ≡ set a (to codomain-set-≃ b₂)
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
  (l : Lens₃ A R B) →
  id₃ ₃∘₃ l
    ≡
  (A                      ↝⟨ l ⟩
   Σ R B                  ↝⟨ Σ-cong (inverse ×-right-identity) (λ _ → F.id) ⟩□
   Σ (R × ⊤) (B ⊚ proj₁)  □)
left-identity₃ _ = Eq.lift-equality ext refl

right-identity₃ :
  ∀ {a r b} {A : Set a} {R : Set r} {B : R → Set b} →
  (l : Lens₃ A R B) →
  l ₃∘₃ id₃
    ≡
  (A                      ↝⟨ l ⟩
   Σ R B                  ↝⟨ Σ-cong (inverse ×-left-identity) (λ _ → F.id) ⟩□
   Σ (⊤ × R) (B ⊚ proj₂)  □)
right-identity₃ _ = Eq.lift-equality ext refl

associativity₃ :
  ∀ {a r₁ b₁ r₂ b₂ r₃ b₃}
    {A : Set a} {R₁ : Set r₁} {B₁ : R₁ → Set b₁}
    {R₂ : R₁ → Set r₂} {B₂ : (r₁ : R₁) → R₂ r₁ → Set b₂}
    {R₃ : (r₁ : R₁) → R₂ r₁ → Set r₃}
    {B₃ : (r₁ : R₁) (r₂ : R₂ r₁) → R₃ r₁ r₂ → Set b₃} →
  (l₁ : ∀ {r₁ r₂} → Lens₃ (B₂ r₁ r₂) (R₃ r₁ r₂) (B₃ r₁ r₂))
  (l₂ : ∀ {r} → Lens₃ (B₁ r) (R₂ r) (B₂ r))
  (l₃ : Lens₃ A R₁ B₁) →
  l₁ ₃∘₃ (l₂ ₃∘₃ l₃)
    ≡
  (A                                                             ↝⟨ (l₁ ₃∘₃ l₂) ₃∘₃ l₃ ⟩
   Σ (Σ R₁ (λ r₁ → Σ (R₂ r₁) (R₃ r₁))) (uncurry (uncurry ⊚ B₃))  ↝⟨ Σ-cong Σ-assoc (λ _ → F.id) ⟩□
   Σ (Σ (Σ R₁ R₂) (uncurry R₃)) (uncurry (uncurry B₃))           □)
associativity₃ _ _ _ = Eq.lift-equality ext refl

------------------------------------------------------------------------
-- Dependent lenses without "remainder types" visible in the type

Lens : ∀ {a b} (A : Set a) → (A → Set b) → Set (lsuc (a ⊔ b))
Lens {a} {b} A B =
  ∃ λ (R : Set (a ⊔ b)) →
  ∃ λ (B′ : R → Set b) →
  ∃ λ (lens : Lens₃ A R B′) →
  ((r : R) → ∥ B′ r ∥)
    ×
  (∀ a → B′ (Lens₃.remainder lens a) ≡ B a)

module Lens {a b} {A : Set a} {B : A → Set b} (l : Lens A B) where

  -- The remainder type: what remains of A when B is removed
  -- (roughly).

  R : Set (a ⊔ b)
  R = proj₁ l

  -- A variant of B, indexed by Rs instead of As.

  B′ : R → Set b
  B′ = proj₁ (proj₂ l)

  -- The main lens isomorphism.

  lens : Lens₃ A R B′
  lens = proj₁ (proj₂ (proj₂ l))

  -- If the remainder type is inhabited, then the corresponding view
  -- should also be (merely) inhabited.

  inhabited : (r : R) → ∥ B′ r ∥
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

  -- Thus we can, assuming that the K rule holds, define a variant of
  -- B that only depends on R.

  module First-variant-of-B (K : K-rule (lsuc b) (lsuc b)) where

    private

      B̲′ : (r : R) → ∥ B′ r ∥ → Set b
      B̲′ r =
        to (constant-function≃∥inhabited∥⇒inhabited
              (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP K)))
           (B ⊚ _≃_.from lens ⊚ (r ,_) , independent-of-B′ r)

    B̲ : R → Set b
    B̲ r = B̲′ r (inhabited r)

    -- This type family is pointwise equal to B′ (given the same
    -- assumptions).

    B′≡B̲ : ∀ r → B′ r ≡ B̲ r
    B′≡B̲ r = Trunc.elim
      (λ ∥b′∥ → B′ r ≡ B̲′ r ∥b′∥)
      (λ _ → _⇔_.from set⇔UIP (_⇔_.to K⇔UIP K) _ _)
      (other-variant r)
      (inhabited r)

  -- We can also use other assumptions:
  --
  -- * Univalence.
  -- * B should be a family of sets.

  module Second-variant-of-B
           (univ  : Univalence b)
           (B-set : ∀ a → Is-set (B a))
           where

    private

      B̲-triple : (r : R) → ∃ λ (X : SET b) → B′ r ≡ proj₁ X
      B̲-triple r =
        to (coherently-constant-function≃∥inhabited∥⇒inhabited
              (Σ-closure 3
                 (∃-H-level-H-level-1+ ext univ 2)
                 (λ { (_ , X-set) → mono₁ 2 $
                      H-level-H-level-≡ʳ ext univ 1 X-set })))
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
                                                                                 (H-level-H-level-≡ʳ ext univ 1 (B-set _) _ _)
                                                                                 _ _) ⟩∎
                Σ-≡,≡→≡ (Σ-≡,≡→≡ (independent-of-B′ r b′₁ b′₃) _) _      ∎))
          (inhabited r)
        where
        Is-set-is-propositional :
          {B : Set b} → Is-proposition (Is-set B)
        Is-set-is-propositional =
          H-level-propositional ext 2

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

  codomain-set : ∀ {a b} → B (set a b) ≡ B a
  codomain-set {a} {b} =
    B (set a b)               ≡⟨ sym (variant _) ⟩
    B′ (remainder (set a b))  ≡⟨ cong B′ (remainder-set a b) ⟩
    B′ (remainder a)          ≡⟨ variant _ ⟩∎
    B a                       ∎

  -- A corresponding isomorphism.

  codomain-set-≃ : ∀ {a b} → B (set a b) ≃ B a
  codomain-set-≃ = ≡⇒↝ _ codomain-set

  -- Unfolding lemmas for codomain-set-≃.

  to-codomain-set-≃ :
    ∀ {a b} →
    to (codomain-set-≃ {a = a} {b = b}) ≡
    to variant≃ ⊚ to L.codomain-set-≃ ⊚ from variant≃
  to-codomain-set-≃ =
    to (≡⇒↝ _ (trans (sym (variant _)) (trans eq (variant _))))       ≡⟨ ≡⇒↝-trans equivalence {B≡C = trans eq (variant _)} ⟩
    to (≡⇒↝ _ (trans eq (variant _))) ⊚ to (≡⇒↝ _ (sym (variant _)))  ≡⟨ cong (to (≡⇒↝ _ (trans eq (variant _))) ⊚_)
                                                                              (≡⇒↝-sym equivalence {eq = variant _}) ⟩
    to (≡⇒↝ _ (trans eq (variant _))) ⊚ from variant≃                 ≡⟨ cong (_⊚ from variant≃) (≡⇒↝-trans equivalence {B≡C = variant _}) ⟩∎
    to variant≃ ⊚ to (≡⇒↝ _ eq) ⊚ from variant≃                       ∎
    where
    eq = cong B′ (remainder-set _ _)

  from-codomain-set-≃ :
    ∀ {a b} →
    from (codomain-set-≃ {a = a} {b = b}) ≡
    to variant≃ ⊚ from L.codomain-set-≃ ⊚ from variant≃
  from-codomain-set-≃ =
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

  get-set : ∀ a b → get (set a b) ≡ from codomain-set-≃ b
  get-set a b =
    to variant≃ (L.get (L.set a (from variant≃ b)))  ≡⟨ cong (to variant≃) $ L.get-set₂ _ _ ⟩
    to variant≃ (from (≡⇒↝ _ eq) (from variant≃ b))  ≡⟨ cong (_$ b) (sym from-codomain-set-≃) ⟩∎
    from codomain-set-≃ b                            ∎
    where
    eq = cong B′ (remainder-set a b)

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a (to codomain-set-≃ b₂)
  set-set a b₁ b₂ =
    L.set (L.set a (from variant≃ b₁)) (from variant≃ b₂)  ≡⟨ L.set-set₂ a (from variant≃ b₁) (from variant≃ b₂) ⟩
    L.set a (to L.codomain-set-≃ (from variant≃ b₂))       ≡⟨ cong (L.set a) lemma ⟩∎
    L.set a (from variant≃ (to codomain-set-≃ b₂))         ∎
    where
    lemma =
      to L.codomain-set-≃ (from variant≃ b₂)                    ≡⟨ sym $ left-inverse-of variant≃ _ ⟩

      from variant≃
        (to variant≃ (to L.codomain-set-≃ (from variant≃ b₂)))  ≡⟨ cong (from variant≃ ⊚ (_$ b₂)) $ sym to-codomain-set-≃ ⟩∎

      from variant≃ (to codomain-set-≃ b₂)                      ∎

-- For non-dependent dependent lenses, and in the presence of the K
-- rule, codomain-set-≃ is equal to the identity.

codomain-set-≃≡id :
  ∀ {a b} {A : Set a} {B : Set b} →
  K-rule (lsuc b) (lsuc b) →
  (l : Lens A (λ _ → B)) →
  ∀ {a b} → Lens.codomain-set-≃ l {a = a} {b = b} ≡ Eq.id
codomain-set-≃≡id K l =
  codomain-set-≃      ≡⟨⟩
  ≡⇒↝ _ codomain-set  ≡⟨ cong (≡⇒↝ _) (_⇔_.to K⇔UIP K codomain-set refl) ⟩
  ≡⇒↝ _ refl          ≡⟨ refl ⟩∎
  Eq.id               ∎
  where
  open Lens l

------------------------------------------------------------------------
-- Some lens isomorphisms

-- Iso-lens preserves level-preserving equivalences (assuming
-- univalence).

Lens-cong :
  ∀ {a b} {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b} →
  Univalence b →
  (A₁≃A₂ : A₁ ≃ A₂) →
  (∀ a → B₁ a ≃ B₂ (_≃_.to A₁≃A₂ a)) →
  Lens A₁ B₁ ≃ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂} {B₁} {B₂} univ A₁≃A₂ B₁≃B₂ =
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : Lens₃ A₁ R B′) →
   ((r : R) → ∥ B′ r ∥)
     ×
   (∀ a → B′ (remainder lens a) ≡ B₁ a))              ↝⟨ (∃-cong λ R → ∃-cong λ B′ →
                                                          Σ-cong (Eq.≃-preserves ext A₁≃A₂ F.id) λ lens →
                                                          ∃-cong λ _ →
                                                          Eq.Π-preserves ext A₁≃A₂ λ a →
                                                          ≡-preserves-≃ ext univ univ
                                                            (≡⇒↝ _ (
      B′ (proj₁ (to lens a))                                        ≡⟨ cong (λ a → B′ (proj₁ (to lens a))) $ sym $ left-inverse-of A₁≃A₂ _ ⟩∎
      B′ (proj₁ (to lens (from A₁≃A₂ (to A₁≃A₂ a))))                ∎))
                                                            (B₁≃B₂ a)) ⟩□
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : Lens₃ A₂ R B′) →
   ((r : R) → ∥ B′ r ∥)
     ×
   (∀ a → B′ (remainder lens a) ≡ B₂ a))              □
  where
  open Lens₃
  open _≃_

-- If B x is a proposition for all x, then Lens A B is isomorphic to
-- (x : A) → B x (assuming univalence).

lens-to-proposition↔get :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Univalence (a ⊔ b) →
  Univalence b →
  (∀ x → Is-proposition (B x)) →
  Lens A B ↔ ((x : A) → B x)
lens-to-proposition↔get {b = b} {A} {B} univ₁ univ₂ B-prop =
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥)
     ×
   (∀ a → B′ (Lens₃.remainder lens a) ≡ B a))                ↔⟨ (∃-cong λ _ → ∃-cong λ B′ → ∃-cong λ l → ∃-cong λ _ →
                                                                 Eq.Π-preserves ext l λ _ →
                                                                 ≡⇒↝ _ $ cong (λ x → _ ≡ B x) $ sym $ _≃_.left-inverse-of l _) ⟩
  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥)
     ×
   (∀ p → B′ (proj₁ p) ≡ B (_≃_.from lens p)))               ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → currying) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) → ∥ B′ r ∥)
     ×
   ((r : R) (b : B′ r) → B′ r ≡ B (_≃_.from lens (r , b))))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ΠΣ-comm) ⟩

  (∃ λ (R : Set _) →
   ∃ λ (B′ : R → Set _) →
   ∃ λ (lens : A ≃ Σ R B′) →
   ((r : R) →
      ∥ B′ r ∥
        ×
      ((b : B′ r) → B′ r ≡ B (_≃_.from lens (r , b)))))      ↔⟨ (∃-cong λ _ → ∃-cong λ B′ → ∃-cong λ lens →
                                                                 Eq.∀-preserves ext $
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
                                                                           (drop-⊤-right (λ r → inverse {k = equivalence} (⊤≃B′ r)))) λ _ →
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
   ∀ r → B (_≃_.from lens r) })                              ↝⟨ drop-⊤-left-Σ (other-singleton-with-≃-↔-⊤ {b = b} ext univ₁) ⟩

  (∃ λ (B′ : ↑ _ A → Set _) →
   (∀ a → ⊤ ≃ B′ a)
     ×
   (∀ a → B (lower a)))                                      ↝⟨ Σ-assoc ⟩

  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ⊤ ≃ B′ a)
    ×
  (∀ a → B (lower a))                                        ↔⟨ ((∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                                  Eq.≃-preserves ext (inverse $ Eq.↔⇒≃ Bij.↑↔) F.id)
                                                                   ×-cong
                                                                 Eq.Π-preserves ext (Eq.↔⇒≃ Bij.↑↔) (λ _ → F.id)) ⟩
  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ↑ _ ⊤ ≃ B′ a)
    ×
  (∀ a → B a)                                                ↔⟨ (∃-cong λ B′ →
                                                                 Eq.∀-preserves ext λ _ →
                                                                 inverse $ ≡≃≃ univ₂)
                                                                  ×-cong
                                                                F.id ⟩
  (∃ λ (B′ : ↑ _ A → Set _) → ∀ a → ↑ _ ⊤ ≡ B′ a)
    ×
  (∀ a → B a)                                                ↔⟨ (∃-cong λ _ →
                                                                 Eq.extensionality-isomorphism ext)
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
    (∥ B′ r ∥ × Is-proposition (B′ r))  ↝⟨ ×-comm ⟩

    (Is-proposition (B′ r) × ∥ B′ r ∥)  ↝⟨ (∃-cong λ B′-prop → ∥∥↔ B′-prop) ⟩

    (Is-proposition (B′ r) × B′ r)      ↔⟨ _↠_.from (Eq.≃↠⇔ (Σ-closure 1 (H-level-propositional ext 1) λ B′-prop →
                                                             B′-prop)
                                                            (H-level-propositional ext 0))
                                                    (record { to   = uncurry propositional⇒inhabited⇒contractible
                                                            ; from = λ B′-contr → mono₁ 0 B′-contr , proj₁ B′-contr
                                                            }) ⟩
    Contractible (B′ r)                 ↝⟨ contractible↔⊤≃ ext ⟩□

    ⊤ ≃ B′ r                            □

  lemma₁ : {R : Set _} (B′ : R → Set _) (lens : A ≃ Σ R B′) (r : R) → _
  lemma₁ B′ lens r =
    ∥ B′ r ∥
      ×
    ((b′ : B′ r) → B′ r ≡ B (_≃_.from lens (r , b′)))  ↝⟨ (∃-cong λ _ → Eq.∀-preserves ext λ _ →
                                                           ≡≃≃ univ₂) ⟩
    ∥ B′ r ∥
      ×
    ((b′ : B′ r) → B′ r ≃ B (_≃_.from lens (r , b′)))  ↝⟨ (∃-cong λ _ → Eq.∀-preserves ext λ b′ →
                                                           _↠_.from (Eq.≃↠⇔ (Eq.right-closure ext 0 (B-prop _))
                                                                            (×-closure 1
                                                                                       (H-level-propositional ext 1)
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
    ∥ B′ r ∥
      ×
    ((b′ : B′ r) → Is-proposition (B′ r)
                     ×
                   B (_≃_.from lens (r , b′)))         ↔⟨ (∃-cong λ _ → ΠΣ-comm) ⟩

    ∥ B′ r ∥
      ×
    (B′ r → Is-proposition (B′ r))
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↝⟨ (∃-cong λ _ →
                                                           _↠_.from (Eq.≃↠⇔ (Π-closure ext 1 λ _ →
                                                                             H-level-propositional ext 1)
                                                                            (H-level-propositional ext 1))
                                                                    (record { to   = λ B′-prop → [inhabited⇒+]⇒+ 0 B′-prop
                                                                            ; from = λ B′-prop _ → B′-prop
                                                                            })
                                                             ×-cong
                                                           F.id) ⟩
    ∥ B′ r ∥
      ×
    Is-proposition (B′ r)
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ ×-assoc ⟩

    (∥ B′ r ∥
      ×
     Is-proposition (B′ r))
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ lemma₂ B′ r ×-cong F.id ⟩

    (⊤ ≃ B′ r)
      ×
    ((b′ : B′ r) → B (_≃_.from lens (r , b′)))         ↔⟨ (∃-cong λ ⊤≃B′ → drop-⊤-left-Π ext (_≃_.bijection $ inverse ⊤≃B′)) ⟩□

    (∃ λ (⊤≃B′ : ⊤ ≃ B′ r) →
     B (_≃_.from lens (r , _≃_.to ⊤≃B′ _)))            □

-- If B x is contractible for all x, then Lens A B is isomorphic to ⊤
-- (assuming univalence).

lens-to-contractible↔⊤ :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Univalence (a ⊔ b) →
  Univalence b →
  (∀ x → Contractible (B x)) →
  Lens A B ↔ ⊤
lens-to-contractible↔⊤ {A = A} {B} univ₁ univ₂ cB =
  Lens A B         ↝⟨ lens-to-proposition↔get univ₁ univ₂ (mono₁ 0 ⊚ cB) ⟩
  ((x : A) → B x)  ↔⟨ (Eq.∀-preserves ext λ _ →
                       Eq.↔⇒≃ $ inverse $ _⇔_.to contractible⇔⊤↔ (cB _)) ⟩
  (A → ⊤)          ↝⟨ →-right-zero ⟩□
  ⊤                □

-- Lens A (const ⊥) is isomorphic to ¬ A (assuming univalence).

lens-to-⊥↔¬ :
  ∀ {a b} {A : Set a} →
  Univalence (a ⊔ b) →
  Univalence b →
  Lens A (const (⊥ {ℓ = b})) ↔ ¬ A
lens-to-⊥↔¬ {A = A} univ₁ univ₂ =
  Lens A (const ⊥)  ↝⟨ lens-to-proposition↔get univ₁ univ₂ (λ _ → ⊥-propositional) ⟩
  (A → ⊥)           ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A               □

-- If we assume that equality with the codomain type is propositional,
-- then non-dependent dependent lenses are isomorphic to non-dependent
-- lenses.
--
-- TODO: Can this be proved without assuming that equality with the
-- codomain type is propositional? If not, can the definition of Lens
-- be changed so that it can be proved?

non-dependent-lenses-isomorphic :
  ∀ {a b} {A : Set a} {B : Set b} →
  (∀ {B′} → Is-proposition (B′ ≡ B)) →
  ∃ λ (iso : Lens A (const B) ↔ Iso-lens A B) →
    ∀ {l a} → Lens.get l a ≡ ND.Iso-lens.get (_↔_.to iso l) a
non-dependent-lenses-isomorphic {a} {A = A} {B} ≡B-prop =
  (Lens A (const B)  ↝⟨ ∃-cong lemma ⟩□
   Iso-lens A B      □)
  , λ {l a} →
    let p = variant l a
        q = Trunc.rec _ _ (inhabited l (remainder l a))
    in
    _≃_.to (≡⇒↝ _ p) (proj₂ (_≃_.to (lens l) a))  ≡⟨ cong (λ eq → _≃_.to (≡⇒↝ _ eq) (proj₂ (_≃_.to (lens l) a)))
                                                          (_⇔_.to propositional⇔irrelevant ≡B-prop p q) ⟩∎
    _≃_.to (≡⇒↝ _ q) (proj₂ (_≃_.to (lens l) a))  ∎
  where
  open Lens

  lemma = λ R →
    (∃ λ (B′ : R → Set _) →
     ∃ λ (lens : A ≃ Σ R B′) →
     ((r : R) → ∥ B′ r ∥)
       ×
     (∀ a → B′ (Lens₃.remainder lens a) ≡ B))     ↔⟨ (∃-cong λ _ → ∃-cong λ l → ∃-cong λ _ →
                                                      Eq.Π-preserves ext l (λ _ → F.id)) ⟩
    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥)
       ×
     (∀ p → B′ (proj₁ p) ≡ B))                    ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → currying) ⟩

    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥)
       ×
     ((r : R) → B′ r → B′ r ≡ B))                 ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ inh →
                                                      Eq.∀-preserves ext λ r →
                                                      _↠_.from (Eq.≃↠⇔ (Π-closure ext 1 λ _ →
                                                                        ≡B-prop)
                                                                       ≡B-prop)
                                                        (record { from = λ B′r≡B     → const B′r≡B
                                                                ; to   = λ B′r→B′r≡B → Trunc.rec ≡B-prop B′r→B′r≡B (inh r)
                                                                })) ⟩
    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥)
       ×
     ((r : R) → B′ r ≡ B))                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

    (∃ λ (B′ : R → Set _) →
     (A ≃ Σ R B′)
       ×
     ((r : R) → B′ r ≡ B)
       ×
     ((r : R) → ∥ B′ r ∥))                        ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (B′ : R → Set _) →
     ((r : R) → B′ r ≡ B)
       ×
     (A ≃ Σ R B′)
       ×
     ((r : R) → ∥ B′ r ∥))                        ↔⟨ (∃-cong λ _ →
                                                        Σ-cong (Eq.extensionality-isomorphism ext) λ B′≡B →
                                                        Eq.≃-preserves ext F.id (∃-cong λ _ → ≡⇒↝ _ (B′≡B _))
                                                          ×-cong
                                                        Eq.∀-preserves ext (λ _ →
                                                          Eq.↔⇒≃ $ ∥∥-cong (≡⇒↝ _ (B′≡B _))))  ⟩
    (∃ λ (B′ : R → Set _) →
     B′ ≡ const B
       ×
     (A ≃ (R × B))
       ×
     (R → ∥ B ∥))                                 ↝⟨ Σ-assoc ⟩

    ((∃ λ (B′ : R → Set _) → B′ ≡ const B)
       ×
     (A ≃ (R × B))
       ×
     (R → ∥ B ∥))                                 ↝⟨ drop-⊤-left-× (λ _ →
                                                     inverse $ _⇔_.to contractible⇔⊤↔ (singleton-contractible _)) ⟩□
    ((A ≃ (R × B))
       ×
     (R → ∥ B ∥))                                 □

-- Non-dependent dependent lenses are isomorphic to non-dependent
-- lenses, assuming the K rule.

non-dependent-lenses-isomorphic-K :
  ∀ {a b} {A : Set a} {B : Set b} →
  K-rule (lsuc b) (lsuc b) →
  ∃ λ (iso : Lens A (const B) ↔ Iso-lens A B) →
    ∀ {l a} → Lens.get l a ≡ ND.Iso-lens.get (_↔_.to iso l) a
non-dependent-lenses-isomorphic-K K =
  non-dependent-lenses-isomorphic
    (_⇔_.from set⇔UIP (_⇔_.to K⇔UIP K) _ _)

------------------------------------------------------------------------
-- Lens combinators

-- Conversion from Lens₃ to Lens.

Lens₃-to-Lens :
  ∀ {a b} {A : Set a} {R : Set (a ⊔ b)} {B : R → Set b} →
  (l : Lens₃ A R B) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens {A = A} {R} {B} l =
  _ ,
  _ ,
  (A                                              ↝⟨ l ⟩
   Σ R B                                          ↔⟨ ∃-cong (λ _ → inverse ∥∥×↔) ⟩
   Σ R (λ r → ∥ B r ∥ × B r)                      ↔⟨ Σ-assoc ⟩□
   Σ (Σ R (λ r → ∥ B r ∥)) (λ { (r , _) → B r })  □) ,
  proj₂ ,
  λ _ → refl

-- A variant of Lens₃-to-Lens.

Lens₃-to-Lens′ :
  ∀ {a r b} {A : Set (a ⊔ r)} {R : Set r} {B : R → Set b} →
  (l : Lens₃ A R B) →
  Lens A (B ⊚ Lens₃.remainder l)
Lens₃-to-Lens′ {a} {b = b} {A} {R} {B} l =
  Lens₃-to-Lens
    (A                                       ↝⟨ l ⟩
     Σ R B                                   ↝⟨ Σ-cong (inverse Bij.↑↔) (λ _ → F.id) ⟩□
     Σ (↑ (a ⊔ b) R) (λ { (lift r) → B r })  □)

-- Identity lens.

id : ∀ {a} {A : Set a} →
     Lens A (λ _ → A)
id {A = A} = Lens₃-to-Lens′
  (A      ↔⟨ inverse ×-left-identity ⟩□
   ⊤ × A  □)

-- Composition of lenses.
--
-- Note that this function combines a family of Lenses and a Lens₃.

infixr 9 _∘₃_

_∘₃_ :
  ∀ {a b c} {A : Set (a ⊔ b ⊔ c)} {R : Set (a ⊔ b ⊔ c)}
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

-- Can the composition operation be generalised?

-- The argument below does not depend on the details of the
-- implementation of Lens.

module No-fully-general-composition-operator
  (Lens′ : (A : Set) → (A → Set) → Set₁)
  (get′  : ∀ {A B} → Lens′ A B → (a : A) → B a)
  where

  -- The following type signature—and partial specification—might seem
  -- like a reasonable goal (if we restrict attention to Set₀).

  Type-of-composition : Set₁
  Type-of-composition =
    {A : Set} {B : A → Set} {C : (a : A) → B a → Set}
    (l₁ : Lens′ A B)
    (l₂ : ∀ a → Lens′ (B a) (C a)) →
    ∃ λ (l₃ : Lens′ A (λ a → C a (get′ l₁ a))) →
      ∀ a → get′ l₃ a ≡ get′ (l₂ a) (get′ l₁ a)

  -- However, this specification is unsatisfiable in the non-dependent
  -- case (for Iso-lenses).

  no-corresponding-non-dependent-composition-operator :
    let open ND.Iso-lens in
    ¬ ({A B C : Set}
       (l₁ : Iso-lens A B)
       (l₂ : A → Iso-lens B C) →
       ∃ λ (l₃ : Iso-lens A C) →
         ∀ a → get l₃ a ≡ get (l₂ a) (get l₁ a))
  no-corresponding-non-dependent-composition-operator comp =
    contradiction
    where
    open ND.Iso-lens
    open _≃_

    idL : Iso-lens Bool Bool
    idL = ND.Iso-lens-combinators.id

    swapL : Iso-lens Bool Bool
    swapL = ND.isomorphism-to-lens
      (Bool      ↔⟨ swap ⟩
       Bool      ↔⟨ inverse ×-left-identity ⟩□
       ⊤ × Bool  □)

    l₁ : Iso-lens Bool Bool
    l₁ = idL

    l₂ : Bool → Iso-lens Bool Bool
    l₂ = if_then idL else swapL

    l₃ : Iso-lens Bool Bool
    l₃ = proj₁ (comp l₁ l₂)

    get-constant : ∀ b → get l₃ b ≡ true
    get-constant true  = proj₂ (comp l₁ l₂) _
    get-constant false = proj₂ (comp l₁ l₂) _

    contradiction : ⊥
    contradiction = Bool.true≢false (
      true                        ≡⟨ sym $ get-constant (set l₃ true false) ⟩
      get l₃ (set l₃ true false)  ≡⟨ get-set l₃ true false ⟩∎
      false                       ∎)

  -- Thus it is also unsatisfiable if non-dependent dependent lenses
  -- are isomorphic (in a certain sense) to the corresponding
  -- Iso-lenses.

  no-composition-operator :
    ({A B : Set} →
     ∃ λ (iso : Lens′ A (λ _ → B) ↔ Iso-lens A B) →
       ∀ {l a} → get′ l a ≡ ND.Iso-lens.get (_↔_.to iso l) a) →
    ¬ Type-of-composition
  no-composition-operator Lens↔Iso-lens comp =
    no-corresponding-non-dependent-composition-operator
      (λ l₁ l₂ →
         let l₃ , get-l₃ = comp (from l₁) (λ a → from (l₂ a))
         in
         to l₃ , λ a →
           get (to l₃) a                                  ≡⟨ sym $ proj₂ Lens↔Iso-lens ⟩
           get′ l₃ a                                      ≡⟨ get-l₃ a ⟩
           get′ (from (l₂ a)) (get′ (from l₁) a)          ≡⟨ cong (get′ (from (l₂ a))) (proj₂ Lens↔Iso-lens) ⟩
           get′ (from (l₂ a)) (get (to (from l₁)) a)      ≡⟨ proj₂ Lens↔Iso-lens ⟩
           get (to (from (l₂ a))) (get (to (from l₁)) a)  ≡⟨ cong₂ (λ l₁ l₂ → get l₁ (get l₂ a))
                                                                   (right-inverse-of _)
                                                                   (right-inverse-of _) ⟩∎
           get (l₂ a) (get l₁ a)                          ∎)
    where
    open ND.Iso-lens
    open module Lens↔Iso-lens {A B : Set} =
      _↔_ (proj₁ (Lens↔Iso-lens {A = A} {B = B}))

-- In the presence of the K rule it is impossible to define a fully
-- general composition operator.

no-fully-general-composition-operator-K :
  let open Lens in
  K-rule (# 1) (# 1) →
  ¬ ({A : Set} {B : A → Set} {C : (a : A) → B a → Set}
     (l₁ : Lens A B)
     (l₂ : ∀ a → Lens (B a) (C a)) →
     ∃ λ (l₃ : Lens A (λ a → C a (Lens.get l₁ a))) →
       ∀ a → get l₃ a ≡ get (l₂ a) (get l₁ a))
no-fully-general-composition-operator-K K =
  No-fully-general-composition-operator.no-composition-operator
    Lens Lens.get
    (non-dependent-lenses-isomorphic-K K)

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
  not-proj₁ K l = Bool.true≢false (
    true                       ≡⟨ sym $ cong (λ eq → from eq true) $ codomain-set-≃≡id K l ⟩
    from codomain-set-≃ true   ≡⟨ sym $ get-set u true ⟩
    get (set u true)           ≡⟨ cong get (equal (set u true) (set u false)) ⟩
    get (set u false)          ≡⟨ get-set u false ⟩
    from codomain-set-≃ false  ≡⟨ cong (λ eq → from eq false) $ codomain-set-≃≡id K l ⟩∎
    false                      ∎)
    where
    open _≃_
    open Lens l

  -- TODO: What is the situation in the presence of univalence?

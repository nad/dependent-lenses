------------------------------------------------------------------------
-- Traditional non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Traditional
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

import Bi-invertibility
open import Bijection equality-with-J as Bij using (_↔_)
open import Category equality-with-J as C using (Category; Precategory)
open import Circle eq as Circle using (𝕊¹)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Surjection equality-with-J as Surjection using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)

private
  variable
    a b c p         : Level
    A B C D         : Set a
    u v x₁ x₂ y₁ y₂ : A

------------------------------------------------------------------------
-- Traditional lenses

-- Lenses.

record Lens (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    -- Getter and setter.
    get : A → B
    set : A → B → A

    -- Lens laws.
    get-set : ∀ a b → get (set a b) ≡ b
    set-get : ∀ a → set a (get a) ≡ a
    set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂

  -- A combination of get and set.

  modify : (B → B) → A → A
  modify f x = set x (f (get x))

instance

  -- Traditional lenses have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

private
  variable
    l₁ l₂ : Lens A B

------------------------------------------------------------------------
-- Some lemmas

-- The record type above is isomorphic to a nested Σ-type.

Lens-as-Σ :
  Lens A B ↔
  ∃ λ (get : A → B) →
  ∃ λ (set : A → B → A) →
  (∀ a b → get (set a b) ≡ b) ×
  (∀ a → set a (get a) ≡ a) ×
  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)
Lens-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ l → get l , set l , get-set l , set-get l , set-set l
      ; from = λ { (get , set , get-set , set-get , set-set) →
                   record
                     { get     = get
                     ; set     = set
                     ; get-set = get-set
                     ; set-get = set-get
                     ; set-set = set-set
                     }
                 }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }
  where
  open Lens

-- If two lenses have equal setters, then they also have equal
-- getters.

getters-equal-if-setters-equal :
  let open Lens in
  (l₁ l₂ : Lens A B) →
  set l₁ ≡ set l₂ →
  get l₁ ≡ get l₂
getters-equal-if-setters-equal l₁ l₂ setters-equal = ⟨ext⟩ λ a →
  get l₁ a                      ≡⟨ cong (get l₁) $ sym $ set-get l₂ _ ⟩
  get l₁ (set l₂ a (get l₂ a))  ≡⟨ cong (λ f → get l₁ (f _ _)) $ sym setters-equal ⟩
  get l₁ (set l₁ a (get l₂ a))  ≡⟨ get-set l₁ _ _ ⟩∎
  get l₂ a                      ∎
  where
  open Lens

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

------------------------------------------------------------------------
-- Some lens isomorphisms

-- If B is a proposition, then Lens A B is isomorphic to
-- (A → B) × ((a : A) → a ≡ a).

lens-to-proposition↔ :
  Is-proposition B →
  Lens A B ↔ (A → B) × ((a : A) → a ≡ a)
lens-to-proposition↔ {B = B} {A = A} B-prop =
  Lens A B                                                          ↝⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))                    ↝⟨ (∃-cong λ get → ∃-cong λ set → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                          ≡⇒↝ _ (
       (set (set a b₁)                         b₂ ≡ set a b₂)               ≡⟨ cong (λ b → set (set a b) b₂ ≡ _) (B-prop _ _) ⟩
       (set (set a (get a))                    b₂ ≡ set a b₂)               ≡⟨ cong (λ b → set (set a (get a)) b ≡ _) (B-prop _ _) ⟩
       (set (set a (get a)) (get (set a (get a))) ≡ set a b₂)               ≡⟨ cong (λ b → _ ≡ set a b) (B-prop _ _) ⟩∎
       (set (set a (get a)) (get (set a (get a))) ≡ set a (get a))          ∎)) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a → B → B →
        set (set a (get a)) (get (set a (get a))) ≡
        set a (get a)))                                             ↝⟨ (∃-cong λ get →
                                                                        Σ-cong (A→B→A↔A→A get) λ set →
                                                                          drop-⊤-left-× λ _ →
                                                                            _⇔_.to contractible⇔↔⊤ $
                                                                              Π-closure ext 0 λ _ →
                                                                              Π-closure ext 0 λ _ →
                                                                              +⇒≡ B-prop) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → B → f (f a) ≡ f a))                                 ↝⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a →
                                                                          drop-⊤-left-Π ext (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → f (f a) ≡ f a))                                     ↝⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                                        ∀-cong ext λ a →
                                                                          drop-⊤-left-Π ext (B↔⊤ (get a))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → f (f a) ≡ f a))                                         ↝⟨ (∃-cong λ _ → ∃-cong λ f →
                                                                        Σ-cong (Eq.extensionality-isomorphism ext) λ f≡id →
                                                                        ∀-cong ext λ a →
                                                                        ≡⇒↝ _ (cong₂ _≡_ (trans (f≡id (f a)) (f≡id a)) (f≡id a ))) ⟩
  ((A → B) ×
   ∃ λ (f : A → A) →
     f ≡ P.id ×
     (∀ a → a ≡ a))                                                 ↝⟨ (∃-cong λ _ → Σ-assoc) ⟩

  (A → B) ×
  (∃ λ (f : A → A) → f ≡ P.id) ×
  (∀ a → a ≡ a)                                                     ↝⟨ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                                          _⇔_.to contractible⇔↔⊤ $
                                                                            singleton-contractible _) ⟩□
  (A → B) × (∀ a → a ≡ a)                                           □

  where
  B↔⊤ : B → B ↔ ⊤
  B↔⊤ b =
    _⇔_.to contractible⇔↔⊤ $
      propositional⇒inhabited⇒contractible B-prop b

  A→B→A↔A→A : (A → B) → (A → B → A) ↔ (A → A)
  A→B→A↔A→A get =
    (A → B → A)  ↝⟨ ∀-cong ext (λ a → drop-⊤-left-Π ext $ B↔⊤ (get a)) ⟩□
    (A → A)      □

-- Lens A ⊤ is isomorphic to (a : A) → a ≡ a.

lens-to-⊤↔ : Lens A ⊤ ↔ ((a : A) → a ≡ a)
lens-to-⊤↔ {A = A} =
  Lens A ⊤                     ↝⟨ lens-to-proposition↔ (mono₁ 0 ⊤-contractible) ⟩
  (A → ⊤) × ((a : A) → a ≡ a)  ↝⟨ drop-⊤-left-× (λ _ → →-right-zero) ⟩□
  ((a : A) → a ≡ a)            □

-- Lens A ⊥ is isomorphic to ¬ A.

lens-to-⊥↔ : Lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔ {A = A} =
  Lens A ⊥                     ↝⟨ lens-to-proposition↔ ⊥-propositional ⟩
  (A → ⊥) × ((a : A) → a ≡ a)  ↝⟨ →-cong ext F.id (Bij.⊥↔uninhabited ⊥-elim)
                                    ×-cong
                                  F.id ⟩
  ¬ A × ((a : A) → a ≡ a)      ↝⟨ drop-⊤-right lemma ⟩□
  ¬ A                          □
  where
  lemma : ¬ A → ((a : A) → a ≡ a) ↔ ⊤
  lemma ¬a = record
    { surjection = record
      { logical-equivalence = record
        { to   = _
        ; from = λ _ _ → refl _
        }
      ; right-inverse-of = λ _ → refl _
      }
    ; left-inverse-of = λ eq → ⟨ext⟩ λ a →
        ⊥-elim (¬a a)
    }

-- See also lens-from-⊥↔⊤ and
-- lens-from-contractible↔codomain-contractible below.

------------------------------------------------------------------------
-- Some lens results related to h-levels

-- If the domain of a lens is inhabited and has h-level n,
-- then the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} n l a =
  H-level n A  ↝⟨ H-level.respects-surjection surj n ⟩
  H-level n B  □
  where
  open Lens l

  surj : A ↠ B
  surj = record
    { logical-equivalence = record
      { to   = get
      ; from = set a
      }
    ; right-inverse-of = λ b →
        get (set a b)  ≡⟨ get-set a b ⟩∎
        b              ∎
    }

-- Lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited _ l (proj₁ c) c

-- If A and B have h-level n given the assumption that A is inhabited,
-- then Lens A B also has h-level n.

lens-preserves-h-level :
  ∀ n → (A → H-level n A) → (A → H-level n B) →
  H-level n (Lens A B)
lens-preserves-h-level n hA hB =
  H-level.respects-surjection (_↔_.surjection (inverse Lens-as-Σ)) n $
  Σ-closure n (Π-closure ext n λ a →
               hB a) λ _ →
  Σ-closure n (Π-closure ext n λ a →
               Π-closure ext n λ _ →
               hA a) λ _ →
  ×-closure n (Π-closure ext n λ a →
               Π-closure ext n λ _ →
               +⇒≡ $ mono₁ n (hB a)) $
  ×-closure n (Π-closure ext n λ a →
               +⇒≡ $ mono₁ n (hA a))
              (Π-closure ext n λ a →
               Π-closure ext n λ _ →
               Π-closure ext n λ _ →
               +⇒≡ $ mono₁ n (hA a))

-- If A has positive h-level n, then Lens A B also has h-level n.

lens-preserves-h-level-of-domain :
  ∀ n → H-level (1 + n) A → H-level (1 + n) (Lens A B)
lens-preserves-h-level-of-domain n hA =
  [inhabited⇒+]⇒+ n λ l →
    lens-preserves-h-level (1 + n) (λ _ → hA) λ a →
      h-level-respects-lens-from-inhabited _ l a hA

-- There is a type A such that Lens A ⊤ is not propositional (assuming
-- univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-type-of-refl-propositional.)

¬-lens-to-⊤-propositional :
  Univalence (# 0) →
  ∃ λ (A : Set a) → ¬ Is-proposition (Lens A ⊤)
¬-lens-to-⊤-propositional _ =
  A′ , (
  Is-proposition (Lens A′ ⊤)         ↝⟨ H-level.respects-surjection (_↔_.surjection lens-to-⊤↔) 1 ⟩
  Is-proposition ((a : A′) → a ≡ a)  ↝⟨ proj₂ $ Circle.¬-type-of-refl-propositional ⟩□
  ⊥₀                                 □)
  where
  A′ = _

------------------------------------------------------------------------
-- Some equality characterisation lemmas

abstract

  -- An equality characterisation lemma.

  equality-characterisation₁ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                 (subst (λ set → get l₁ (set a b) ≡ b) s
                    (get-set l₁ a b)) ≡
               get-set l₂ a b)
        ×
      (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
               (subst (λ set → set a (get l₁ a) ≡ a) s
                  (set-get l₁ a)) ≡
             set-get l₂ a)
        ×
      (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                     (set-set l₁ a b₁ b₂) ≡
                   set-set l₂ a b₁ b₂)

  equality-characterisation₁ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                            ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Lens-as-Σ)) ⟩

    l₁′ ≡ l₂′                                                          ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse Σ-assoc)) ⟩

    ((get l₁ , set l₁) , proj₂ (proj₂ l₁′))
      ≡
    ((get l₂ , set l₂) , proj₂ (proj₂ l₂′))                            ↝⟨ inverse Bij.Σ-≡,≡↔≡ ⟩

    (∃ λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           gs (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ Σ-cong (inverse ≡×≡↔≡) (λ gs → ≡⇒↝ _ $
                                                                          cong (λ (gs : (get l₁ , set l₁) ≡ (get l₂ , set l₂)) →
                                                                                  subst (λ { (get , set) →
                                                                                             (∀ a b → get (set a b) ≡ b) ×
                                                                                             (∀ a → set a (get a) ≡ a) ×
                                                                                             (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
                                                                                        gs (proj₂ (proj₂ l₁′))
                                                                                    ≡
                                                                                  proj₂ (proj₂ l₂′))
                                                                               (sym $ _↔_.right-inverse-of ≡×≡↔≡ gs)) ⟩
    (∃ λ (gs : get l₁ ≡ get l₂ × set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ gs) (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ inverse Σ-assoc ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) →
                (∀ a b → get (set a b) ≡ b) ×
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ l₁′)) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ (∃-cong λ g → ∃-cong λ s → ≡⇒↝ _ $
                                                                           cong (λ x → x ≡ proj₂ (proj₂ l₂′))
                                                                                (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     ( subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
             (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁)
     , subst (λ { (get , set) →
                  (∀ a → set a (get a) ≡ a) ×
                  (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁′)))
     ) ≡
     proj₂ (proj₂ l₂′))                                                ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
     get-set l₂
       ×
     subst (λ { (get , set) →
                (∀ a → set a (get a) ≡ a) ×
                (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂) })
           (_↔_.to ≡×≡↔≡ (g , s)) (proj₂ (proj₂ (proj₂ l₁′))) ≡
     proj₂ (proj₂ (proj₂ l₂′)))                                        ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ≡⇒↝ _ $
                                                                           cong (λ x → x ≡ proj₂ (proj₂ (proj₂ l₂′)))
                                                                                (push-subst-, {y≡z = _↔_.to ≡×≡↔≡ (g , s)} _ _)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
     get-set l₂
       ×
     ( subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
             (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁)
     , subst (λ { (get , set) →
                  ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
             (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁)
     ) ≡
     proj₂ (proj₂ (proj₂ l₂′)))                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ≡×≡↔≡) ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     subst (λ { (get , set) → ∀ a b → get (set a b) ≡ b })
           (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁) ≡
     get-set l₂
       ×
     subst (λ { (get , set) → ∀ a → set a (get a) ≡ a })
           (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁) ≡
     set-get l₂
       ×
     subst (λ { (get , set) →
                ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
           (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁) ≡
       set-set l₂)                                                     ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                           lemma₁ (λ { (get , set) a → ∀ b → get (set a b) ≡ b })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))
                                                                             ×-cong
                                                                           lemma₁ (λ { (get , set) a → set a (get a) ≡ a })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))
                                                                             ×-cong
                                                                           lemma₁ (λ { (get , set) a → ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                  (_↔_.to ≡×≡↔≡ (g , s))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a → subst (λ { (get , set) → ∀ b → get (set a b) ≡ b })
                  (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a) ≡
            get-set l₂ a)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
            set-get l₂ a)
       ×
     (∀ a → subst (λ { (get , set) →
                       ∀ b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a) ≡
            set-set l₂ a))                                             ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                           (∀-cong ext λ a →
                                                                              lemma₁ (λ { (get , set) b → get (set a b) ≡ b })
                                                                                     (_↔_.to ≡×≡↔≡ (g , s)))
                                                                             ×-cong
                                                                           F.id
                                                                             ×-cong
                                                                           (∀-cong ext λ a →
                                                                              lemma₁ (λ { (get , set) b₁ → ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                     (_↔_.to ≡×≡↔≡ (g , s)))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                    (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b) ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
            set-get l₂ a)
       ×
     (∀ a b₁ → subst (λ { (get , set) →
                          ∀ b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                     (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁) ≡
               set-set l₂ a b₁))                                       ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∀-cong ext λ a → ∀-cong ext λ b₁ →
                                                                             lemma₁ (λ { (get , set) b₂ → set (set a b₁) b₂ ≡ set a b₂ })
                                                                                    (_↔_.to ≡×≡↔≡ (g , s))) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ { (get , set) → get (set a b) ≡ b })
                    (_↔_.to ≡×≡↔≡ (g , s)) (get-set l₁ a b) ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ { (get , set) → set a (get a) ≡ a })
                  (_↔_.to ≡×≡↔≡ (g , s)) (set-get l₁ a) ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ { (get , set) →
                             set (set a b₁) b₂ ≡ set a b₂ })
                        (_↔_.to ≡×≡↔≡ (g , s)) (set-set l₁ a b₁ b₂) ≡
                  set-set l₂ a b₁ b₂))                                 ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                           (∀-cong ext λ a → ∀-cong ext λ b →
                                                                            lemma₂ (λ { (get , set) → get (set a b) ≡ b }) g s)
                                                                             ×-cong
                                                                           (∀-cong ext λ a →
                                                                            lemma₂ (λ { (get , set) → set a (get a) ≡ a }) g s)
                                                                             ×-cong
                                                                           (∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                            lemma₂ (λ { (get , set) → set (set a b₁) b₂ ≡ set a b₂ }) g s)) ⟩
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                (subst (λ set → get l₁ (set a b) ≡ b) s
                   (get-set l₁ a b)) ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a)) ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ →
        subst (λ get → set l₂ (set l₂ a b₁) b₂ ≡ set l₂ a b₂) g
          (subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
             (set-set l₁ a b₁ b₂)) ≡
        set-set l₂ a b₁ b₂))                                           ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (λ x → x ≡ _) $ subst-const g) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                (subst (λ set → get l₁ (set a b) ≡ b) s
                   (get-set l₁ a b)) ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a)) ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                    (set-set l₁ a b₁ b₂) ≡
                  set-set l₂ a b₁ b₂))                                 □
    where
    open Lens

    l₁′ = _↔_.to Lens-as-Σ l₁
    l₂′ = _↔_.to Lens-as-Σ l₂

    abstract

      lemma₁ :
        ∀ (C : A → B → Set c) (eq : u ≡ v) {f g} →
        (subst (λ x → ∀ y → C x y) eq f ≡ g)
          ↔
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)
      lemma₁ C eq {f} {g} =
        subst (λ x → ∀ y → C x y) eq f ≡ g              ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (∀ y → subst (λ x → ∀ y → C x y) eq f y ≡ g y)  ↝⟨ (∀-cong ext λ y → ≡⇒↝ _ $
                                                            cong (λ x → x ≡ _) (sym $ push-subst-application eq _)) ⟩□
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)      □

    lemma₂ :
      ∀ (P : A × B → Set p) (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : y₁ ≡ y₂) {p p′} →
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡ p′)
        ↔
      (subst (λ x → P (x , y₂)) x₁≡x₂ (subst (λ y → P (x₁ , y)) y₁≡y₂ p)
         ≡
       p′)
    lemma₂ P x₁≡x₂ y₁≡y₂ {p = p} = ≡⇒↝ _ $ cong (_≡ _) $ elim¹
      (λ y₁≡y₂ →
         subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , y₁≡y₂)) p ≡
         subst (λ x → P (x , _)) x₁≡x₂
           (subst (λ y → P (_ , y)) y₁≡y₂ p))
      (subst P (_↔_.to ≡×≡↔≡ (x₁≡x₂ , refl _)) p                     ≡⟨⟩

       subst P (cong₂ _,_ x₁≡x₂ (refl _)) p                          ≡⟨⟩

       subst P (trans (cong (_, _) x₁≡x₂) (cong (_ ,_) (refl _))) p  ≡⟨ cong (λ eq → subst P (trans (cong (_, _) x₁≡x₂) eq) p) $ cong-refl _ ⟩

       subst P (trans (cong (_, _) x₁≡x₂) (refl _)) p                ≡⟨ cong (λ eq → subst P eq p) $ trans-reflʳ _ ⟩

       subst P (cong (_, _) x₁≡x₂) p                                 ≡⟨ sym $ subst-∘ _ _ _ ⟩

       subst (λ x → P (x , _)) x₁≡x₂ p                               ≡⟨ cong (subst (λ x → P (x , _)) x₁≡x₂) $ sym $ subst-refl _ _ ⟩∎

       subst (λ x → P (x , _)) x₁≡x₂
         (subst (λ y → P (_ , y)) (refl _) p)                        ∎)
      _

  -- Another equality characterisation lemma.

  equality-characterisation₂ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      (∀ a b →
         trans (sym (cong₂ (λ set get → get (set a b)) s g))
           (get-set l₁ a b) ≡
         get-set l₂ a b) ×
      (∀ a →
         trans (sym (cong₂ (λ set get → set a (get a)) s g))
           (set-get l₁ a) ≡
         set-get l₂ a) ×
      (∀ a b₁ b₂ →
         subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
           (set-set l₁ a b₁ b₂) ≡
         set-set l₂ a b₁ b₂)

  equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                          ↝⟨ equality-characterisation₁ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
       (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                  (subst (λ set → get l₁ (set a b) ≡ b) s
                     (get-set l₁ a b)) ≡
                get-set l₂ a b)
         ×
       (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
                (subst (λ set → set a (get l₁ a) ≡ a) s
                   (set-get l₁ a)) ≡
              set-get l₂ a)
         ×
       (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                      (set-set l₁ a b₁ b₂) ≡
                    set-set l₂ a b₁ b₂))                             ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                         (∀-cong ext λ a → ∀-cong ext λ b → ≡⇒↝ _ $ cong (_≡ _) $
                                                                          lemma₁ g s a b)
                                                                           ×-cong
                                                                         (∀-cong ext λ a → ≡⇒↝ _ $ cong (_≡ _) $
                                                                          lemma₂ g s a)
                                                                           ×-cong
                                                                         F.id) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
       (∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                  (get-set l₁ a b) ≡
                get-set l₂ a b) ×
       (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                (set-get l₁ a) ≡
              set-get l₂ a) ×
       (∀ a b₁ b₂ →
          subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
            (set-set l₁ a b₁ b₂) ≡
          set-set l₂ a b₁ b₂))                                       □
    where
    open Lens

    lemma₁ : ∀ _ _ _ _ → _
    lemma₁ g s a b =
      subst (λ get → get (set l₂ a b) ≡ b) g
        (subst (λ set → get l₁ (set a b) ≡ b) s
           (get-set l₁ a b))                                     ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g eq) $
                                                                    subst-in-terms-of-trans-and-cong {x≡y = s} {fx≡gx = (get-set l₁ a b)} ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (trans (get-set l₁ a b) (cong (const b) s)))          ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g
                                                                                   (trans (sym (cong (λ set → get l₁ (set a b)) s))
                                                                                      (trans _ eq))) $
                                                                    cong-const s ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (trans (get-set l₁ a b) (refl _)))                    ≡⟨ cong (λ eq → subst (λ get → get (set l₂ a b) ≡ b) g (trans _ eq)) $
                                                                    trans-reflʳ _ ⟩
      subst (λ get → get (set l₂ a b) ≡ b) g
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (get-set l₁ a b))                                     ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = g}
                                                                      {fx≡gx = trans _ (get-set l₁ a b)} ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                  (get-set l₁ a b))
           (cong (const b) g))                                   ≡⟨ cong (λ eq → trans (sym (cong (λ get → get (set l₂ a b)) g))
                                                                                   (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                                                                                             (get-set l₁ a b))
                                                                                      eq)) $
                                                                    cong-const g ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (trans (sym (cong (λ set → get l₁ (set a b)) s))
                  (get-set l₁ a b))
           (refl _))                                             ≡⟨ cong (trans _) $
                                                                    trans-reflʳ _ ⟩
      trans (sym (cong (λ get → get (set l₂ a b)) g))
        (trans (sym (cong (λ set → get l₁ (set a b)) s))
           (get-set l₁ a b))                                     ≡⟨ sym $ trans-assoc _ _ (get-set l₁ a b) ⟩

      trans (trans (sym (cong (λ get → get (set l₂ a b)) g))
               (sym (cong (λ set → get l₁ (set a b)) s)))
        (get-set l₁ a b)                                         ≡⟨ cong (λ eq → trans eq (get-set l₁ a b)) $ sym $
                                                                    sym-trans _ (cong (λ get → get (set l₂ a b)) g) ⟩
      trans (sym (trans (cong (λ set → get l₁ (set a b)) s)
                    (cong (λ get → get (set l₂ a b)) g)))
        (get-set l₁ a b)                                         ≡⟨⟩

      trans (sym (cong₂ (λ set get → get (set a b)) s g))
        (get-set l₁ a b)                                         ∎

    lemma₂ : ∀ _ _ _ → _
    lemma₂ g s a =
      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a))                                       ≡⟨⟩

      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a))                                       ≡⟨ cong (subst (λ get → set l₂ a (get a) ≡ a) g) $
                                                                    subst-in-terms-of-trans-and-cong {x≡y = s} {fx≡gx = set-get l₁ a} ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (trans (set-get l₁ a) (cong (const a) s)))            ≡⟨ cong (λ eq → subst (λ get → set l₂ a (get a) ≡ a) g
                                                                                    (trans (sym (cong (λ set → set a (get l₁ a)) s))
                                                                                       (trans _ eq))) $
                                                                    cong-const s ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (trans (set-get l₁ a) (refl _)))                      ≡⟨ cong (λ eq → subst (λ get → set l₂ a (get a) ≡ a) g (trans _ eq)) $
                                                                    trans-reflʳ _ ⟩
      subst (λ get → set l₂ a (get a) ≡ a) g
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (set-get l₁ a))                                       ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = g}
                                                                      {fx≡gx = trans (sym (cong (λ set → set a (get l₁ a)) s)) (set-get l₁ a)} ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                  (set-get l₁ a))
           (cong (const a) g))                                   ≡⟨ cong (λ eq → trans (sym (cong (λ get → set l₂ a (get a)) g))
                                                                                   (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                                                                                             (set-get l₁ a))
                                                                                      eq)) $
                                                                    cong-const g ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (trans (sym (cong (λ set → set a (get l₁ a)) s))
                  (set-get l₁ a))
           (refl _))                                             ≡⟨ cong (trans _) $
                                                                    trans-reflʳ _ ⟩
      trans (sym (cong (λ get → set l₂ a (get a)) g))
        (trans (sym (cong (λ set → set a (get l₁ a)) s))
           (set-get l₁ a))                                       ≡⟨ sym $ trans-assoc _ _ (set-get l₁ a) ⟩

      trans (trans (sym (cong (λ get → set l₂ a (get a)) g))
               (sym (cong (λ set → set a (get l₁ a)) s)))
        (set-get l₁ a)                                           ≡⟨ cong (λ eq → trans eq (set-get l₁ a)) $ sym $
                                                                    sym-trans _ (cong (λ get → set l₂ a (get a)) g) ⟩
      trans (sym (trans (cong (λ set → set a (get l₁ a)) s)
                    (cong (λ get → set l₂ a (get a)) g)))
        (set-get l₁ a)                                           ≡⟨⟩

      trans (sym (cong₂ (λ set get → set a (get a)) s g))
        (set-get l₁ a)                                           ∎

  -- And another one.

  equality-characterisation₃ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : get l₁ ≡ get l₂) →
    ∃ λ (s : set l₁ ≡ set l₂) →
      (∀ a b →
         trans (sym (cong₂ (λ set get → get (set a b)) s g))
           (get-set l₁ a b) ≡
         get-set l₂ a b) ×
      (∀ a →
         trans (sym (cong₂ (λ set get → set a (get a)) s g))
           (set-get l₁ a) ≡
         set-get l₂ a) ×
      (∀ a b₁ b₂ →
         trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
         trans (cong (λ set → set (set a b₁) b₂) s)
           (set-set l₂ a b₁ b₂))

  equality-characterisation₃ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                          ↝⟨ equality-characterisation₂ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
       (∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                  (get-set l₁ a b) ≡
                get-set l₂ a b) ×
       (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                (set-get l₁ a) ≡
              set-get l₂ a) ×
       (∀ a b₁ b₂ →
          subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
            (set-set l₁ a b₁ b₂) ≡
          set-set l₂ a b₁ b₂))                                       ↝⟨ (∃-cong λ g → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                         ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ → ≡⇒↝ _ $
                                                                         lemma g s a b₁ b₂) ⟩□
    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
       (∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                  (get-set l₁ a b) ≡
                get-set l₂ a b) ×
       (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                (set-get l₁ a) ≡
              set-get l₂ a) ×
       (∀ a b₁ b₂ →
          trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
          trans (cong (λ set → set (set a b₁) b₂) s)
            (set-set l₂ a b₁ b₂)))                                   □
    where
    open Lens

    lemma : ∀ _ _ _ _ _ → _
    lemma g s a b₁ b₂ =
      subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
        (set-set l₁ a b₁ b₂) ≡
      set-set l₂ a b₁ b₂                                        ≡⟨ cong (_≡ _) $
                                                                   subst-in-terms-of-trans-and-cong {x≡y = s} {fx≡gx = set-set l₁ a b₁ b₂} ⟩
      trans (sym (cong (λ set → set (set a b₁) b₂) s))
        (trans (set-set l₁ a b₁ b₂)
           (cong (λ set → set a b₂) s)) ≡
      set-set l₂ a b₁ b₂                                        ≡⟨ [trans≡]≡[≡trans-symˡ] _ _ _ ⟩

      trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
      trans (sym (sym (cong (λ set → set (set a b₁) b₂) s)))
        (set-set l₂ a b₁ b₂)                                    ≡⟨ cong (λ eq → trans _ (cong (λ set → set a b₂) s) ≡
                                                                                trans eq (set-set l₂ a b₁ b₂)) $
                                                                   sym-sym (cong (λ set → set (set a b₁) b₂) s) ⟩
      trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
      trans (cong (λ set → set (set a b₁) b₂) s)
        (set-set l₂ a b₁ b₂)                                    ∎

  -- And yet another one.

  equality-characterisation₄ :
    let open Lens in

    l₁ ≡ l₂
      ↔
    ∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
    ∃ λ (s : ∀ a b → set l₁ a b ≡ set l₂ a b) →
      (∀ a b →
         trans (sym (trans (cong (get l₁) (s a b))
                       (g (set l₂ a b))))
           (get-set l₁ a b) ≡
         get-set l₂ a b) ×
      (∀ a →
         trans (sym (trans (s a (get l₁ a))
                       (cong (set l₂ a) (g a))))
           (set-get l₁ a) ≡
         set-get l₂ a) ×
      (∀ a b₁ b₂ →
         trans (set-set l₁ a b₁ b₂) (s a b₂) ≡
         trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
           (set-set l₂ a b₁ b₂))

  equality-characterisation₄ {l₁ = l₁} {l₂ = l₂} =
    l₁ ≡ l₂                                                             ↝⟨ equality-characterisation₃ ⟩

    (∃ λ (g : get l₁ ≡ get l₂) →
     ∃ λ (s : set l₁ ≡ set l₂) →
       (∀ a b → trans (sym (cong₂ (λ set get → get (set a b)) s g))
                  (get-set l₁ a b) ≡
                get-set l₂ a b) ×
       (∀ a → trans (sym (cong₂ (λ set get → set a (get a)) s g))
                (set-get l₁ a) ≡
              set-get l₂ a) ×
       (∀ a b₁ b₂ →
          trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
          trans (cong (λ set → set (set a b₁) b₂) s)
            (set-set l₂ a b₁ b₂)))                                      ↝⟨ (Σ-cong (inverse $ Eq.extensionality-isomorphism ext) λ g →
                                                                            Σ-cong (inverse $
                                                                                    Eq.extensionality-isomorphism ext F.∘
                                                                                    ∀-cong ext λ _ → Eq.extensionality-isomorphism ext) λ s →
                                                                            (∀-cong ext λ a → ∀-cong ext λ b →
                                                                             ≡⇒↝ _ $ cong (λ eq → trans (sym eq) (get-set l₁ a b) ≡ _) (
        cong₂ (λ set get → get (set a b)) s g                                  ≡⟨⟩

        trans (cong (λ set → get l₁ (set a b)) s)
          (cong (λ get → get (set l₂ a b)) g)                                  ≡⟨ cong (λ eq → trans eq (ext⁻¹ g (set l₂ a b))) $ sym $
                                                                                  cong-∘ _ _ s ⟩
        trans (cong (get l₁ ⊚ (_$ b)) (ext⁻¹ s a))
          (ext⁻¹ g (set l₂ a b))                                               ≡⟨ cong (λ eq → trans eq (ext⁻¹ g (set l₂ a b))) $ sym $
                                                                                  cong-∘ _ _ (ext⁻¹ s a) ⟩∎
        trans (cong (get l₁) (ext⁻¹ (ext⁻¹ s a) b))
          (ext⁻¹ g (set l₂ a b))                                               ∎))
                                                                              ×-cong
                                                                            (∀-cong ext λ a →
                                                                             ≡⇒↝ _ $ cong (λ eq → trans (sym eq) (set-get l₁ a) ≡ _) (
        cong₂ (λ set get → set a (get a)) s g                                  ≡⟨⟩

        trans (cong (λ set → set a (get l₁ a)) s)
          (cong (λ get → set l₂ a (get a)) g)                                  ≡⟨ sym $ cong₂ trans (cong-∘ _ _ s) (cong-∘ _ _ g) ⟩

        trans (ext⁻¹ (ext⁻¹ s a) (get l₁ a))
          (cong (set l₂ a) (ext⁻¹ g a))                                        ∎))
                                                                              ×-cong
                                                                            ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                             ≡⇒↝ _ $
                                                                             cong₂ (λ p q → trans _ p ≡
                                                                                            trans (cong (λ set → set (set a b₁) b₂) q)
                                                                                              (set-set l₂ a b₁ b₂)) (
        cong (λ set → set a b₂) s                                              ≡⟨ sym $ cong-∘ _ _ s ⟩∎

        ext⁻¹ (ext⁻¹ s a) b₂                                                   ∎)
                                                                               (
        s                                                                      ≡⟨ sym $ _≃_.right-inverse-of
                                                                                          (Eq.extensionality-isomorphism bad-ext) _ ⟩
        ⟨ext⟩ (ext⁻¹ s)                                                        ≡⟨ (cong ⟨ext⟩ $ ⟨ext⟩ λ _ → sym $
                                                                                   _≃_.right-inverse-of
                                                                                     (Eq.extensionality-isomorphism bad-ext) _) ⟩∎
        ⟨ext⟩ (⟨ext⟩ ⊚ ext⁻¹ ⊚ ext⁻¹ s)                                        ∎)) ⟩□

    (∃ λ (g : ∀ a → get l₁ a ≡ get l₂ a) →
     ∃ λ (s : ∀ a b → set l₁ a b ≡ set l₂ a b) →
       (∀ a b →
          trans (sym (trans (cong (get l₁) (s a b))
                        (g (set l₂ a b))))
            (get-set l₁ a b) ≡
          get-set l₂ a b) ×
       (∀ a →
          trans (sym (trans (s a (get l₁ a))
                        (cong (set l₂ a) (g a))))
            (set-get l₁ a) ≡
          set-get l₂ a) ×
       (∀ a b₁ b₂ →
          trans (set-set l₁ a b₁ b₂) (s a b₂) ≡
          trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
            (set-set l₂ a b₁ b₂)))                                      □
    where
    open Lens

  -- A lemma that can be used to prove that two lenses with
  -- definitionally equal getters and setters are equal.

  equal-laws→≡ :
    {get : A → B} {set : A → B → A}
    {l₁′ l₂′ : (∀ a b → get (set a b) ≡ b) ×
               (∀ a → set a (get a) ≡ a) ×
               (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂)} →

    let l₁ = _↔_.from Lens-as-Σ (get , set , l₁′)
        l₂ = _↔_.from Lens-as-Σ (get , set , l₂′)
        open Lens
    in

    (∀ a b → get-set l₁ a b ≡ get-set l₂ a b) →
    (∀ a → set-get l₁ a ≡ set-get l₂ a) →
    (∀ a b₁ b₂ → set-set l₁ a b₁ b₂ ≡ set-set l₂ a b₁ b₂) →
    l₁ ≡ l₂
  equal-laws→≡ {l₁′ = l₁′} {l₂′ = l₂′} hyp₁ hyp₂ hyp₃ =
    _↔_.from equality-characterisation₂
      ( refl _
      , refl _
      , (λ a b →
           trans (sym (cong₂ (λ set get → get (set a b))
                         (refl _) (refl _)))
             (get-set l₁″ a b)                            ≡⟨ cong (λ eq → trans (sym eq) _) $ cong₂-refl _ ⟩

           trans (sym (refl _)) (get-set l₁″ a b)         ≡⟨ cong (flip trans _) sym-refl ⟩

           trans (refl _) (get-set l₁″ a b)               ≡⟨ trans-reflˡ _ ⟩

           get-set l₁″ a b                                ≡⟨ hyp₁ _ _ ⟩∎

           get-set l₂″ a b                                ∎)
      , (λ a →
           trans (sym (cong₂ (λ set get → set a (get a))
                         (refl _) (refl _)))
             (set-get l₁″ a)                              ≡⟨ cong (λ eq → trans (sym eq) _) $ cong₂-refl _ ⟩

           trans (sym (refl _)) (set-get l₁″ a)           ≡⟨ cong (flip trans _) sym-refl ⟩

           trans (refl _) (set-get l₁″ a)                 ≡⟨ trans-reflˡ _ ⟩

           set-get l₁″ a                                  ≡⟨ hyp₂ _ ⟩∎

           set-get l₂″ a                                  ∎)
      , (λ a b₁ b₂ →
           subst (λ set → set (set a b₁) b₂ ≡ set a b₂) (refl _)
             (set-set l₁″ a b₁ b₂)                                ≡⟨ subst-refl _ _ ⟩

           set-set l₁″ a b₁ b₂                                    ≡⟨ hyp₃ _ _ _ ⟩∎

           set-set l₂″ a b₁ b₂                                    ∎)
      )
    where
    open Lens

    l₁″ = _↔_.from Lens-as-Σ (_ , _ , l₁′)
    l₂″ = _↔_.from Lens-as-Σ (_ , _ , l₂′)

-- An equality characterisation lemma for lenses from sets.

equality-characterisation-for-sets :
  let open Lens in

  {l₁ l₂ : Lens A B} →

  Is-set A →

  l₁ ≡ l₂
    ↔
  set l₁ ≡ set l₂
equality-characterisation-for-sets
  {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} A-set =

  l₁ ≡ l₂                                                         ↝⟨ equality-characterisation₁ ⟩

  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b → subst (λ get → get (set l₂ a b) ≡ b) g
                (subst (λ set → get l₁ (set a b) ≡ b) s
                   (get-set l₁ a b))
                ≡
              get-set l₂ a b)
       ×
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a))
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                    (set-set l₁ a b₁ b₂)
                    ≡
                  set-set l₂ a b₁ b₂))                            ↝⟨ (∃-cong λ _ → ∃-cong λ _ → drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                                      Π-closure ext 0 λ a →
                                                                      Π-closure ext 0 λ _ →
                                                                      +⇒≡ (B-set a)) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a → subst (λ get → set l₂ a (get a) ≡ a) g
              (subst (λ set → set a (get l₁ a) ≡ a) s
                 (set-get l₁ a))
              ≡
            set-get l₂ a)
       ×
     (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                    (set-set l₁ a b₁ b₂)
                    ≡
                  set-set l₂ a b₁ b₂))                            ↝⟨ (∃-cong λ _ → ∃-cong λ _ → drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                                      Π-closure ext 0 λ _ →
                                                                      +⇒≡ A-set) ⟩
  (∃ λ (g : get l₁ ≡ get l₂) →
   ∃ λ (s : set l₁ ≡ set l₂) →
     (∀ a b₁ b₂ → subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
                    (set-set l₁ a b₁ b₂)
                    ≡
                  set-set l₂ a b₁ b₂))                            ↝⟨ (∃-cong λ _ → drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                      Π-closure ext 0 λ _ →
                                                                      Π-closure ext 0 λ _ →
                                                                      Π-closure ext 0 λ _ →
                                                                      +⇒≡ A-set) ⟩

  get l₁ ≡ get l₂ × set l₁ ≡ set l₂                               ↝⟨ (drop-⊤-left-× λ setters-equal → _⇔_.to contractible⇔↔⊤ $
                                                                      propositional⇒inhabited⇒contractible
                                                                        (Π-closure ext 2 λ a →
                                                                         B-set a)
                                                                        (getters-equal-if-setters-equal l₁ l₂ setters-equal)) ⟩□
  set l₁ ≡ set l₂                                                 □
  where
  open Lens

  B-set : A → Is-set B
  B-set a = h-level-respects-lens-from-inhabited 2 l₁ a A-set

------------------------------------------------------------------------
-- Some existence results

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ∃ λ (A : Set a) → ∃ λ (B : A → Set b) →
    ¬ Lens (Σ A B) A
no-first-projection-lens =
  Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

-- There are two lenses with equal setters that are not equal
-- (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.∃≢refl.)

equal-setters-but-not-equal :
  Univalence lzero →
  ∃ λ (A : Set) →
  ∃ λ (B : Set) →
  ∃ λ (l₁ : Lens A B) →
  ∃ λ (l₂ : Lens A B) →
    Lens.set l₁ ≡ Lens.set l₂ ×
    l₁ ≢ l₂
equal-setters-but-not-equal _ =
  𝕊¹ , ⊤ , l₁′ , l₂′ , refl _ , l₁′≢l₂′
  where
  open Lens

  lemma : Lens 𝕊¹ ⊤ ≃ ((x : 𝕊¹) → x ≡ x)
  lemma =
    Lens 𝕊¹ ⊤                      ↔⟨ lens-to-proposition↔ (mono₁ 0 ⊤-contractible) ⟩
    (𝕊¹ → ⊤) × ((x : 𝕊¹) → x ≡ x)  ↔⟨ (drop-⊤-left-× λ _ → →-right-zero) ⟩□
    ((x : 𝕊¹) → x ≡ x)             □

  l₁′ : Lens 𝕊¹ ⊤
  l₁′ = _≃_.from lemma (proj₁ Circle.∃≢refl)

  l₂′ : Lens 𝕊¹ ⊤
  l₂′ = _≃_.from lemma refl

  set-l₁′≡set-l₂′ : set l₁′ ≡ set l₂′
  set-l₁′≡set-l₂′ = refl _

  l₁′≢l₂′ : l₁′ ≢ l₂′
  l₁′≢l₂′ =
    l₁′ ≡ l₂′                   ↔⟨ Eq.≃-≡ (inverse lemma) {x = proj₁ Circle.∃≢refl} {y = refl} ⟩
    proj₁ Circle.∃≢refl ≡ refl  ↝⟨ proj₂ Circle.∃≢refl ⟩□
    ⊥                           □

------------------------------------------------------------------------
-- More lens isomorphisms

-- Lens ⊥ B is isomorphic to the unit type.

lens-from-⊥↔⊤ : Lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ =
  _⇔_.to contractible⇔↔⊤ $
    record
      { get = ⊥-elim
      ; set = ⊥-elim
      ; get-set = λ a → ⊥-elim a
      ; set-get = λ a → ⊥-elim a
      ; set-set = λ a → ⊥-elim a
      } ,
    λ l → _↔_.from equality-characterisation₁
            ( ⟨ext⟩ (λ a → ⊥-elim a)
            , ⟨ext⟩ (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            , (λ a → ⊥-elim a)
            )

-- If A is contractible, then Lens A B is isomorphic to
-- Contractible B.

lens-from-contractible↔codomain-contractible :
  Contractible A →
  Lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible cA@(a , irrA) =
  _≃_.bijection $
  _↠_.from (Eq.≃↠⇔ (lens-preserves-h-level-of-domain 0 (mono₁ 0 cA))
                   (H-level-propositional ext 0)) (record
    { to   = flip contractible-to-contractible cA
    ; from = λ (b , irrB) → record
        { get     = λ _ → b
        ; set     = λ _ _ → a
        ; get-set = λ _ → irrB
        ; set-get = irrA
        ; set-set = λ _ _ _ → irrA a
        }
    })

------------------------------------------------------------------------
-- Lens combinators

module Lens-combinators where

  -- If two types are isomorphic, then there is a lens between them.

  ↔→lens :
    {A : Set a} {B : Set b} →
    A ↔ B → Lens A B
  ↔→lens A↔B = record
    { get     = to
    ; set     = const from
    ; get-set = const right-inverse-of
    ; set-get = left-inverse-of
    ; set-set = λ _ _ _ → refl _
    }
    where
    open _↔_ A↔B

  -- If two types are equivalent, then there is a lens between them.

  ≃→lens :
    {A : Set a} {B : Set b} →
    A ≃ B → Lens A B
  ≃→lens = ↔→lens ⊚ _≃_.bijection

  -- Identity lens.

  id : Lens A A
  id = ↔→lens F.id

  -- Composition of lenses.

  infixr 9 _∘_

  _∘_ : Lens B C → Lens A B → Lens A C
  l₁ ∘ l₂ = record
    { get     = λ a → get l₁ (get l₂ a)
    ; set     = λ a c →
                let b = set l₁ (get l₂ a) c in
                set l₂ a b
    ; get-set = λ a c →
        let b = set l₁ (get l₂ a) c in
        get l₁ (get l₂ (set l₂ a b))  ≡⟨ cong (get l₁) $ get-set l₂ a b ⟩
        get l₁ b                      ≡⟨⟩
        get l₁ (set l₁ (get l₂ a) c)  ≡⟨ get-set l₁ (get l₂ a) c ⟩∎
        c                             ∎
    ; set-get = λ a →
        set l₂ a (set l₁ (get l₂ a) (get l₁ (get l₂ a)))  ≡⟨ cong (set l₂ a) $ set-get l₁ (get l₂ a) ⟩
        set l₂ a (get l₂ a)                               ≡⟨ set-get l₂ a ⟩∎
        a                                                 ∎
    ; set-set = λ a c₁ c₂ →
        let b₁ = set l₁ (get l₂ a) c₁
            b₂ = set l₁ (get l₂ a) c₂

            lemma =
              set l₁ (get l₂ (set l₂ a b₁))  c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
              set l₁ b₁                      c₂  ≡⟨⟩
              set l₁ (set l₁ (get l₂ a) c₁)  c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩∎
              set l₁ (get l₂ a)              c₂  ∎

        in
        set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ set-set l₂ a b₁ _ ⟩
        set l₂ a             (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ a) lemma ⟩∎
        set l₂ a             b₂                                  ∎
    }
    where
    open Lens

  -- Note that composition can be defined in several different ways.
  -- Here is one alternative implementation.

  infixr 9 _∘′_

  _∘′_ : Lens B C → Lens A B → Lens A C
  l₁ ∘′ l₂ = record (l₁ ∘ l₂)
    { set-set = λ a c₁ c₂ →
        let b₁ = set l₁ (get l₂ a) c₁
            b₂ = set l₁ (get l₂ a) c₂

            lemma =
              set l₁ (get l₂ (set l₂ a b₁))  c₂  ≡⟨ cong (λ x → set l₁ x c₂) $ get-set l₂ a b₁ ⟩
              set l₁ b₁                      c₂  ≡⟨⟩
              set l₁ (set l₁ (get l₂ a) c₁)  c₂  ≡⟨ set-set l₁ (get l₂ a) c₁ c₂ ⟩∎
              set l₁ (get l₂ a)              c₂  ∎

        in
        set l₂ (set l₂ a b₁) (set l₁ (get l₂ (set l₂ a b₁)) c₂)  ≡⟨ cong (set l₂ (set l₂ a b₁)) lemma ⟩
        set l₂ (set l₂ a b₁) b₂                                  ≡⟨ set-set l₂ a b₁ _ ⟩∎
        set l₂ a             b₂                                  ∎
    }
    where
    open Lens

  -- This implementation is pointwise equal to the other one. However,
  -- I don't know if there is some other definition that is distinct
  -- from these two (if we require that the definitions are
  -- polymorphic and that the three composition laws below hold).

  ∘≡∘′ : l₁ ∘ l₂ ≡ l₁ ∘′ l₂
  ∘≡∘′ {l₁ = l₁} {l₂ = l₂} = equal-laws→≡
    (λ _ _ → refl _)
    (λ _ → refl _)
    (λ a c₁ c₂ →
       let b₁ = set l₁ (get l₂ a) c₁
           b₂ = set l₁ (get l₂ a) c₂
           a′ = set l₂ a b₁
           b′ = set l₁ (get l₂ a′) c₂

           eq : b′ ≡ b₂
           eq = trans (cong (λ x → set l₁ x c₂)
                         (get-set l₂ a b₁))
                  (set-set l₁ (get l₂ a) c₁ c₂)
       in
       set-set (l₁ ∘ l₂) a c₁ c₂                                   ≡⟨⟩

       trans (set-set l₂ a b₁ b′) (cong (set l₂ a) eq)             ≡⟨ elim¹
                                                                        (λ {b₂} eq → trans (set-set l₂ a b₁ b′) (cong (set l₂ a) eq) ≡
                                                                                     trans (cong (set l₂ a′) eq) (set-set l₂ a b₁ b₂))
                                                                        (
           trans (set-set l₂ a b₁ b′) (cong (set l₂ a) (refl _))         ≡⟨ cong (trans _) $ cong-refl _ ⟩
           trans (set-set l₂ a b₁ b′) (refl _)                           ≡⟨ trans-reflʳ _ ⟩
           set-set l₂ a b₁ b′                                            ≡⟨ sym $ trans-reflˡ _ ⟩
           trans (refl _) (set-set l₂ a b₁ b′)                           ≡⟨ cong (flip trans _) $ sym $ cong-refl _ ⟩∎
           trans (cong (set l₂ a′) (refl _)) (set-set l₂ a b₁ b′)        ∎)
                                                                        eq ⟩
       trans (cong (set l₂ a′) eq) (set-set l₂ a b₁ b₂)            ≡⟨⟩

       set-set (l₁ ∘′ l₂) a c₁ c₂                                  ∎)
    where
    open Lens

  -- id is a left identity of _∘_.

  left-identity : (l : Lens A B) → id ∘ l ≡ l
  left-identity l = equal-laws→≡
    (λ a b →
       trans (cong P.id (get-set a b)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
       cong P.id (get-set a b)                   ≡⟨ sym $ cong-id _ ⟩∎
       get-set a b                               ∎)
    (λ a →
       trans (cong (set a) (refl _)) (set-get a)  ≡⟨ cong (flip trans _) $ cong-refl _ ⟩
       trans (refl _) (set-get a)                 ≡⟨ trans-reflˡ _ ⟩∎
       set-get a                                  ∎)
    (λ a b₁ b₂ →
       trans (set-set a b₁ b₂)
         (cong (set a)
            (trans (cong (λ _ → b₂) (get-set a b₁)) (refl _)))  ≡⟨ cong (λ eq → trans _ (cong (set a) eq)) $ trans-reflʳ _ ⟩

       trans (set-set a b₁ b₂)
         (cong (set a) (cong (λ _ → b₂) (get-set a b₁)))        ≡⟨ cong (λ eq → trans _ (cong (set a) eq)) $ cong-const _ ⟩

       trans (set-set a b₁ b₂) (cong (set a) (refl _))          ≡⟨ cong (trans _) $ cong-refl _ ⟩

       trans (set-set a b₁ b₂) (refl _)                         ≡⟨ trans-reflʳ _ ⟩∎

       set-set a b₁ b₂                                          ∎)
    where
    open Lens l

  -- id is a right identity of _∘_.

  right-identity : (l : Lens A B) → l ∘ id ≡ l
  right-identity l = equal-laws→≡
    (λ a b →
       trans (cong get (refl _)) (get-set a b)  ≡⟨ cong (flip trans _) $ cong-refl _ ⟩
       trans (refl _) (get-set a b)             ≡⟨ trans-reflˡ _ ⟩∎
       get-set a b                              ∎)
    (λ a →
       trans (cong P.id (set-get a)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
       cong P.id (set-get a)                   ≡⟨ sym $ cong-id _ ⟩∎
       set-get a                               ∎)
    (λ a b₁ b₂ →
       trans (refl _) (cong P.id (trans (cong (λ a → set a b₂) (refl _))
                                    (set-set a b₁ b₂)))                   ≡⟨ trans-reflˡ _ ⟩

       cong P.id (trans (cong (λ a → set a b₂) (refl _))
                    (set-set a b₁ b₂))                                    ≡⟨ sym $ cong-id _ ⟩

       trans (cong (λ a → set a b₂) (refl _)) (set-set a b₁ b₂)           ≡⟨ cong (flip trans _) $ cong-refl _ ⟩

       trans (refl _) (set-set a b₁ b₂)                                   ≡⟨ trans-reflˡ _ ⟩∎

       set-set a b₁ b₂                                                    ∎)
    where
    open Lens l

  -- _∘_ is associative.

  associativity :
    (l₁ : Lens C D) (l₂ : Lens B C) (l₃ : Lens A B) →
    l₁ ∘ (l₂ ∘ l₃) ≡ (l₁ ∘ l₂) ∘ l₃
  associativity l₁ l₂ l₃ = equal-laws→≡ lemma₁ lemma₂ lemma₃
    where
    open Lens

    lemma₁ = λ a d →
      let
        f  = get l₁
        g  = get l₂
        b  = get l₃ a
        c  = g b
        c′ = set l₁ c d
        x  = get-set l₃ a (set l₂ b c′)
        y  = get-set l₂ b c′
        z  = get-set l₁ c d
      in
      trans (cong f $ trans (cong g x) y) z           ≡⟨ cong (λ x → trans x z) (cong-trans f _ y) ⟩
      trans (trans (cong f $ cong g x) (cong f y)) z  ≡⟨ trans-assoc _ _ z ⟩
      trans (cong f $ cong g x) (trans (cong f y) z)  ≡⟨ cong (λ x → trans x (trans (cong f y) z)) (cong-∘ f g x) ⟩∎
      trans (cong (f ⊚ g) x) (trans (cong f y) z)     ∎

    lemma₂ = λ a →
      let
        b = get l₃ a
        f = set l₃ a
        g = set l₂ b
        x = set-get l₁ (get l₂ b)
        y = set-get l₂ b
        z = set-get l₃ a
      in
      trans (cong (f ⊚ g) x) (trans (cong f y) z)     ≡⟨ sym $ trans-assoc _ _ z ⟩
      trans (trans (cong (f ⊚ g) x) (cong f y)) z     ≡⟨ cong (λ x → trans (trans x (cong f y)) z) (sym $ cong-∘ f g x) ⟩
      trans (trans (cong f (cong g x)) (cong f y)) z  ≡⟨ cong (λ x → trans x z) (sym $ cong-trans f _ y) ⟩∎
      trans (cong f $ trans (cong g x) y) z           ∎

    lemma₃ = λ a d₁ d₂ →
      let
        f   = set l₃ a
        g   = set l₂ (get l₃ a)
        h   = λ x → set l₁ x d₂
        i   = get l₂

        c₁  = set l₁ (get (l₂ ∘ l₃) a) d₁
        c₂  = h (i (get l₃ a))
        c₂′ = h (i (get l₃ (set (l₂ ∘ l₃) a c₁)))
        c₂″ = h (i (set l₂ (get l₃ a) c₁))

        b₁  = set l₂ (get l₃ a) c₁
        b₁′ = get l₃ (set l₃ a b₁)

        x   = set-set l₃ a b₁ (set l₂ b₁′ c₂′)
        y   = get-set l₃ a b₁
        z   = set-set l₂ (get l₃ a) c₁
        u   = get-set l₂ (get l₃ a) c₁
        v   = set-set l₁ (get (l₂ ∘ l₃) a) d₁ d₂

        c₂′≡c₂″ =
          c₂′  ≡⟨ cong (h ⊚ i) y ⟩∎
          c₂″  ∎

        lemma₁₀ =
          trans (sym (cong (h ⊚ i) y)) (cong h (cong i y))  ≡⟨ cong (trans _) (cong-∘ h i y) ⟩
          trans (sym (cong (h ⊚ i) y)) (cong (h ⊚ i) y)     ≡⟨ trans-symˡ (cong (h ⊚ i) y) ⟩∎
          refl _                                            ∎

        lemma₉ =
          trans (cong (λ x → set l₂ x c₂′) y) (cong (set l₂ b₁) c₂′≡c₂″)  ≡⟨ cong (trans (cong (λ x → set l₂ x c₂′) y))
                                                                                  (cong-∘ (set l₂ b₁) (h ⊚ i) y) ⟩
          trans (cong (λ x → set l₂ x  (h (i b₁′))) y)
                (cong (λ x → set l₂ b₁ (h (i x  ))) y)                    ≡⟨ trans-cong-cong (λ x y → set l₂ x (h (i y))) y ⟩∎

          cong (λ x → set l₂ x (h (i x))) y                               ∎

        lemma₈ =
          sym (cong (set l₂ b₁) (sym c₂′≡c₂″))  ≡⟨ sym $ cong-sym (set l₂ b₁) (sym c₂′≡c₂″) ⟩
          cong (set l₂ b₁) (sym (sym c₂′≡c₂″))  ≡⟨ cong (cong (set l₂ b₁)) (sym-sym c₂′≡c₂″) ⟩∎
          cong (set l₂ b₁) c₂′≡c₂″              ∎

        lemma₇ =
          trans (cong g (sym c₂′≡c₂″)) (cong g (cong h (cong i y)))  ≡⟨ sym $ cong-trans g _ (cong h (cong i y)) ⟩
          cong g (trans (sym c₂′≡c₂″) (cong h (cong i y)))           ≡⟨ cong (cong g) lemma₁₀ ⟩
          cong g (refl _)                                            ≡⟨ cong-refl _ ⟩∎
          refl _                                                     ∎

        lemma₆ =
          trans (cong (λ x → set l₂ x c₂′) y)
                (trans (cong (set l₂ b₁) c₂′≡c₂″)
                       (trans (z c₂″) (cong g (sym c₂′≡c₂″))))       ≡⟨ sym $ trans-assoc _ _ (trans _ (cong g (sym c₂′≡c₂″))) ⟩

          trans (trans (cong (λ x → set l₂ x c₂′) y)
                       (cong (set l₂ b₁) c₂′≡c₂″))
                (trans (z c₂″) (cong g (sym c₂′≡c₂″)))               ≡⟨ cong (λ e → trans e (trans (z c₂″) (cong g (sym c₂′≡c₂″)))) lemma₉ ⟩

          trans (cong (λ x → set l₂ x (h (i x))) y)
                (trans (z c₂″) (cong g (sym c₂′≡c₂″)))               ≡⟨ sym $ trans-assoc _ _ (cong g (sym c₂′≡c₂″)) ⟩∎

          trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
                (cong g (sym c₂′≡c₂″))                               ∎

        lemma₅ =
          z c₂′                                                  ≡⟨ sym $ dcong z (sym c₂′≡c₂″) ⟩

          subst (λ x → set l₂ b₁ x ≡ g x) (sym c₂′≡c₂″) (z c₂″)  ≡⟨ subst-in-terms-of-trans-and-cong {f = set l₂ b₁} {g = g} {x≡y = sym c₂′≡c₂″} ⟩

          trans (sym (cong (set l₂ b₁) (sym c₂′≡c₂″)))
                (trans (z c₂″) (cong g (sym c₂′≡c₂″)))           ≡⟨ cong (λ e → trans e (trans (z c₂″) (cong g (sym c₂′≡c₂″)))) lemma₈ ⟩∎

          trans (cong (set l₂ b₁) c₂′≡c₂″)
                (trans (z c₂″) (cong g (sym c₂′≡c₂″)))           ∎

        lemma₄ =
          trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                (cong g (cong h (cong i y)))                            ≡⟨ cong (λ e → trans (trans (cong (λ x → set l₂ x c₂′) y) e)
                                                                                                    (cong g (cong h (cong i y))))
                                                                                lemma₅ ⟩
          trans (trans (cong (λ x → set l₂ x c₂′) y)
                       (trans (cong (set l₂ b₁) c₂′≡c₂″)
                              (trans (z c₂″) (cong g (sym c₂′≡c₂″)))))
                (cong g (cong h (cong i y)))                            ≡⟨ cong (λ e → trans e (cong g (cong h (cong i y)))) lemma₆ ⟩

          trans (trans (trans (cong (λ x → set l₂ x (h (i x))) y)
                              (z c₂″))
                       (cong g (sym c₂′≡c₂″)))
                (cong g (cong h (cong i y)))                            ≡⟨ trans-assoc _ _ (cong g (cong h (cong i y))) ⟩

          trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
                (trans (cong g (sym c₂′≡c₂″))
                       (cong g (cong h (cong i y))))                    ≡⟨ cong (trans (trans _ (z c₂″))) lemma₇ ⟩

          trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
                (refl _)                                                ≡⟨ trans-reflʳ _ ⟩∎

          trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″)             ∎

        lemma₃ =
          cong g (trans (cong h (trans (cong i y) u)) v)           ≡⟨ cong (λ e → cong g (trans e v)) (cong-trans h _ u) ⟩

          cong g (trans (trans (cong h (cong i y)) (cong h u)) v)  ≡⟨ cong (cong g) (trans-assoc _ _ v) ⟩

          cong g (trans (cong h (cong i y)) (trans (cong h u) v))  ≡⟨ cong-trans g _ (trans _ v) ⟩∎

          trans (cong g (cong h (cong i y)))
                (cong g (trans (cong h u) v))                      ∎

        lemma₂ =
          trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                (cong g (trans (cong h (trans (cong i y) u)) v))      ≡⟨ cong (trans (trans _ (z c₂′))) lemma₃ ⟩

          trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                (trans (cong g (cong h (cong i y)))
                       (cong g (trans (cong h u) v)))                 ≡⟨ sym $ trans-assoc _ _ (cong g (trans _ v)) ⟩

          trans (trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                       (cong g (cong h (cong i y))))
                (cong g (trans (cong h u) v))                         ≡⟨ cong (λ e → trans e (cong g (trans (cong h u) v))) lemma₄ ⟩

          trans (trans (cong (λ x → set l₂ x (h (i x))) y) (z c₂″))
                (cong g (trans (cong h u) v))                         ≡⟨ trans-assoc _ _ (cong g (trans _ v)) ⟩∎

          trans (cong (λ x → set l₂ x (h (i x))) y)
                (trans (z c₂″) (cong g (trans (cong h u) v)))         ∎

        lemma₁ =
          trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
                (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))  ≡⟨ cong (λ e → trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
                                                                                             e)
                                                                                (sym $ cong-∘ f g (trans _ v)) ⟩
          trans (cong f (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′)))
                (cong f (cong g (trans (cong h (trans (cong i y) u))
                                       v)))                             ≡⟨ sym $ cong-trans f (trans _ (z c₂′)) (cong g (trans _ v)) ⟩

          cong f (trans (trans (cong (λ x → set l₂ x c₂′) y) (z c₂′))
                        (cong g (trans (cong h (trans (cong i y) u))
                                       v)))                             ≡⟨ cong (cong f) lemma₂ ⟩∎

          cong f (trans (cong (λ x → set l₂ x (h (i x))) y)
                        (trans (z c₂″) (cong g (trans (cong h u) v))))  ∎
      in
      trans (trans x (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                    (z c₂′))))
            (cong (f ⊚ g) (trans (cong h (trans (cong i y) u)) v))    ≡⟨ trans-assoc _ _ (cong (f ⊚ g) (trans _ v)) ⟩

      trans x (trans (cong f (trans (cong (λ x → set l₂ x c₂′) y)
                                    (z c₂′)))
                     (cong (f ⊚ g)
                           (trans (cong h (trans (cong i y) u)) v)))  ≡⟨ cong (trans x) lemma₁ ⟩∎

      trans x (cong f (trans (cong (λ x → set l₂ x (h (i x))) y)
                             (trans (z c₂″)
                                    (cong g (trans (cong h u) v)))))  ∎

  -- Every lens of type Lens A A that satisfies a certain right
  -- identity law is equal to the identity lens.

  id-unique :
    (id′ : Lens A A) →
    ((l : Lens A A) → l ∘ id′ ≡ l) →
    id′ ≡ id
  id-unique id′ right-identity =
    id′       ≡⟨ sym $ left-identity _ ⟩
    id ∘ id′  ≡⟨ right-identity _ ⟩∎
    id        ∎

  -- An equality characterisation lemma that can be used when one of
  -- the lenses is the identity.

  equality-characterisation-id :
    {l : Lens A A} → let open Lens l in

    l ≡ id
      ↔
    ∃ λ (g : ∀ a → get a ≡ a) →
    ∃ λ (s : ∀ a b → set a b ≡ b) →
      (∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
      (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
      (∀ a b₁ b₂ →
         trans (set-set a b₁ b₂) (s a b₂) ≡
         cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
  equality-characterisation-id {l = l} =
    l ≡ id                                                              ↝⟨ equality-characterisation₄ ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
       (∀ a b →
          trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
          refl _) ×
       (∀ a →
          trans (sym (trans (s a (get a)) (cong P.id (g a))))
            (set-get a) ≡
          refl _) ×
       (∀ a b₁ b₂ →
          trans (set-set a b₁ b₂) (s a b₂) ≡
          trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
            (refl _)))                                                  ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∃-cong λ _ →
                                                                            (∀-cong ext λ _ →
                                                                             ≡⇒↝ _ $ cong (λ eq → trans (sym (trans _ eq)) (set-get _) ≡ _) $ sym $
                                                                             cong-id (g _))
                                                                             ×-cong
                                                                            ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                             ≡⇒↝ _ $ cong (_ ≡_) $ trans-reflʳ _) ⟩
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
       (∀ a b →
          trans (sym (trans (cong get (s a b)) (g b))) (get-set a b) ≡
          refl _) ×
       (∀ a →
          trans (sym (trans (s a (get a)) (g a))) (set-get a) ≡
          refl _) ×
       (∀ a b₁ b₂ →
          trans (set-set a b₁ b₂) (s a b₂) ≡
          cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        ↝⟨ (∃-cong λ g → ∃-cong λ s →
                                                                            (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                             ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                             ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                              ×-cong
                                                                            (∀-cong ext λ _ →
                                                                             ≡-comm F.∘ ≡⇒↝ _ (cong (_≡ _) $ trans-reflʳ _) F.∘
                                                                             ≡⇒↝ _ (sym $ [trans≡]≡[≡trans-symˡ] _ _ _) F.∘ ≡-comm)
                                                                              ×-cong
                                                                            F.id) ⟩□
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a b → set a b ≡ b) →
       (∀ a b → get-set a b ≡ trans (cong get (s a b)) (g b)) ×
       (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
       (∀ a b₁ b₂ →
          trans (set-set a b₁ b₂) (s a b₂) ≡
          cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        □
    where
    open Lens l

  -- A lemma that can be used to show that a lens with a constant
  -- setter (such as the ones produced by getter-equivalence→lens
  -- below) is equal to the identity lens.

  constant-setter→≡id :
    {l′ : ∃ λ (get : A → A) →
          ∃ λ (set : A → A) →
            (A → ∀ a → get (set a) ≡ a) ×
            (∀ a → set (get a) ≡ a) ×
            (A → A → ∀ a → set a ≡ set a)} →

    let l   = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
        set = proj₁ (proj₂ l′)
        open Lens l hiding (set)
    in

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
       (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
       (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
       (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _)) →
    l ≡ id
  constant-setter→≡id {A = A} {l′ = l′} =
    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
       (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
       (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
       (∀ a a₁ a₂ → set-set a a₁ a₂ ≡ refl _))                          ↝⟨ (Σ-map P.id $ Σ-map P.id λ {s} → Σ-map P.id $ Σ-map P.id λ hyp a a₁ a₂ →

        trans (set-set a a₁ a₂) (s a₂)                                        ≡⟨ cong (λ eq → trans eq (s a₂)) $ hyp _ _ _ ⟩
        trans (refl _) (s a₂)                                                 ≡⟨ trans-reflˡ (s _) ⟩∎
        s a₂                                                                  ∎) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
       (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
       (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
       (∀ a a₁ a₂ → trans (set-set a a₁ a₂) (s a₂) ≡ s a₂))             ↔⟨ (∃-cong λ _ → ∃-cong λ s → ∃-cong λ _ → ∃-cong λ _ →
                                                                            ∀-cong ext λ a → ∀-cong ext λ a₁ → ∀-cong ext λ a₂ →
                                                                            ≡⇒↝ equivalence $ cong (trans _ (s _) ≡_) (
        s a₂                                                                  ≡⟨ sym $ cong-ext s ⟩
        cong (λ set → set a₂) (⟨ext⟩ s)                                       ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ s) ⟩
        cong (λ set → set (set a a₁) a₂) (cong const (⟨ext⟩ s))               ≡⟨ cong (cong (λ set → set (set a a₁) a₂)) $ sym $
                                                                                 ext-const (⟨ext⟩ s) ⟩∎
        cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s)                ∎)) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : ∀ a → set a ≡ a) →
       (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₂)) (g a₂)) ×
       (∀ a → set-get a ≡ trans (s (get a)) (g a)) ×
       (∀ a a₁ a₂ →
          trans (set-set a a₁ a₂) (s a₂) ≡
          cong (λ set → set (set a a₁) a₂) (⟨ext⟩ λ _ → ⟨ext⟩ s)))      ↝⟨ Σ-map P.id (Σ-map const P.id) ⟩

    (∃ λ (g : ∀ a → get a ≡ a) →
     ∃ λ (s : A → ∀ a → set a ≡ a) →
       (∀ a₁ a₂ → get-set a₁ a₂ ≡ trans (cong get (s a₁ a₂)) (g a₂)) ×
       (∀ a → set-get a ≡ trans (s a (get a)) (g a)) ×
       (∀ a a₁ a₂ →
          trans (set-set a a₁ a₂) (s a a₂) ≡
          cong (λ set → set (set a a₁) a₂) (⟨ext⟩ (⟨ext⟩ ⊚ s))))        ↔⟨ inverse equality-characterisation-id ⟩□

    l″ ≡ id                                                             □
    where
    l″  = _↔_.from Lens-as-Σ (Σ-map P.id (Σ-map const P.id) l′)
    set = proj₁ (proj₂ l′)

    open Lens l″ hiding (set)

  -- An identity function for lenses for which the forward direction
  -- is an equivalence.
  --
  -- Note that the setter of the resulting lens is definitionally
  -- equal to a constant function returning the right-to-left
  -- direction of the equivalence.
  --
  -- Note also that two proofs, set-get and set-set, have been
  -- "obfuscated". They could have been shorter, but then it might not
  -- have been possible to prove getter-equivalence→lens≡.

  getter-equivalence→lens :
    (l : Lens A B) →
    Is-equivalence (Lens.get l) →
    Lens A B
  getter-equivalence→lens l is-equiv = record
    { get     = to
    ; set     = const from
    ; get-set = const right-inverse-of
    ; set-get = λ a →
                from (to a)                ≡⟨ cong from (sym (get-set a (to a))) ⟩
                from (get (set a (to a)))  ≡⟨⟩
                from (to (set a (get a)))  ≡⟨ cong (from ⊚ to) (set-get a) ⟩
                from (to a)                ≡⟨ left-inverse-of _ ⟩∎
                a                          ∎
    ; set-set = λ a b₁ b₂ →
                let s = from≡set l is-equiv in
                from b₂            ≡⟨ cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)) ⟩
                set (set a b₁) b₂  ≡⟨ set-set a b₁ b₂ ⟩
                set a b₂           ≡⟨ sym (s a b₂) ⟩∎
                from b₂            ∎
    }
    where
    A≃B = Eq.⟨ _ , is-equiv ⟩

    open _≃_ A≃B
    open Lens l

  -- The function getter-equivalence→lens returns its input.

  getter-equivalence→lens≡ :
    ∀ (l : Lens A B) is-equiv →
    getter-equivalence→lens l is-equiv ≡ l
  getter-equivalence→lens≡ l is-equiv =
    _↔_.from equality-characterisation₄
      ( g
      , s
      , lemma₁
      , lemma₂
      , lemma₃
      )
    where
    open Lens

    A≃B = Eq.⟨ get l , is-equiv ⟩

    open _≃_ A≃B

    l′ = getter-equivalence→lens l is-equiv

    g = λ _ → refl _

    s = from≡set l is-equiv

    lemma₁ = λ a b →
      let lem =
            cong (get l) (s a b)                               ≡⟨⟩

            cong (get l)
              (trans (cong from (sym (get-set l a b)))
                 (left-inverse-of _))                          ≡⟨ cong-trans _ _ (left-inverse-of _) ⟩

            trans (cong (get l)
                     (cong from (sym (get-set l a b))))
              (cong (get l) (left-inverse-of _))               ≡⟨ cong₂ trans
                                                                    (cong-∘ _ _ (sym (get-set l a b)))
                                                                    (left-right-lemma _) ⟩∎
            trans (cong (get l ⊚ from) (sym (get-set l a b)))
              (right-inverse-of _)                             ∎
      in
      trans (sym (trans (cong (get l) (s a b))
                    (g (set l a b))))
        (get-set l′ a b)                                        ≡⟨⟩

      trans (sym (trans (cong (get l) (s a b)) (refl _)))
        (right-inverse-of _)                                    ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) $
                                                                   trans-reflʳ _ ⟩
      trans (sym (cong (get l) (s a b)))
        (right-inverse-of _)                                    ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) lem ⟩

      trans (sym (trans (cong (get l ⊚ from)
                           (sym (get-set l a b)))
                    (right-inverse-of _)))
        (right-inverse-of _)                                    ≡⟨ elim¹
                                                                     (λ eq → trans (sym (trans (cong (get l ⊚ from) (sym eq))
                                                                                           (right-inverse-of _)))
                                                                               (right-inverse-of _) ≡ eq) (
        trans (sym (trans (cong (get l ⊚ from) (sym (refl _)))
                      (right-inverse-of _)))
          (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym (trans (cong (get l ⊚ from) eq) _)) _)
                                                                          sym-refl ⟩
        trans (sym (trans (cong (get l ⊚ from) (refl _))
                      (right-inverse-of _)))
          (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym (trans eq _)) _) $
                                                                          cong-refl _ ⟩
        trans (sym (trans (refl _) (right-inverse-of _)))
          (right-inverse-of _)                                         ≡⟨ cong (λ eq → trans (sym eq) (right-inverse-of _)) $
                                                                          trans-reflˡ (right-inverse-of _) ⟩
        trans (sym (right-inverse-of _))
          (right-inverse-of _)                                         ≡⟨ trans-symˡ (right-inverse-of _) ⟩∎

        refl _                                                         ∎)
                                                                     _ ⟩∎
      get-set l a b                                             ∎

    lemma₂ = λ a →
      trans (sym (trans (s a (get l a)) (cong (set l a) (g a))))
         (set-get l′ a)                                                  ≡⟨⟩

      trans (sym (trans (s a (get l a)) (cong (set l a) (refl _))))
         (set-get l′ a)                                                  ≡⟨ cong (λ eq → trans (sym (trans (s a (get l a)) eq)) (set-get l′ a)) $
                                                                            cong-refl _ ⟩

      trans (sym (trans (s a (get l a)) (refl _))) (set-get l′ a)        ≡⟨ cong (λ eq → trans (sym eq) (set-get l′ a)) $
                                                                            trans-reflʳ _ ⟩

      trans (sym (s a (get l a))) (set-get l′ a)                         ≡⟨⟩

      trans (sym (trans (cong from (sym (get-set l a (get l a))))
                    (left-inverse-of _)))
        (trans (cong from (sym (get-set l a (get l a))))
           (trans (cong (from ⊚ get l) (set-get l a))
              (left-inverse-of _)))                                      ≡⟨ cong (λ eq → trans (sym (trans
                                                                                                       (cong from (sym (get-set l a (get l a))))
                                                                                                       (left-inverse-of _)))
                                                                                           (trans (cong from (sym (get-set l a (get l a)))) eq)) $
                                                                            elim¹
                                                                              (λ eq → trans (cong (from ⊚ get l) eq) (left-inverse-of _) ≡
                                                                                      trans (left-inverse-of _) eq)
                                                                              (
          trans (cong (from ⊚ get l) (refl _))
            (left-inverse-of (set l a (get l a)))                              ≡⟨ cong (flip trans _) $ cong-refl _ ⟩

          trans (refl _) (left-inverse-of (set l a (get l a)))                 ≡⟨ trans-reflˡ _ ⟩

          left-inverse-of (set l a (get l a))                                  ≡⟨ sym $ trans-reflʳ _ ⟩∎

          trans (left-inverse-of (set l a (get l a))) (refl _)                 ∎)
                                                                              (set-get l a) ⟩
      trans (sym (trans (cong from
                           (sym (get-set l a (get l a))))
                    (left-inverse-of _)))
        (trans (cong from (sym (get-set l a (get l a))))
           (trans (left-inverse-of _) (set-get l a)))                    ≡⟨ cong (trans _) $ sym $
                                                                            trans-assoc _ _ (set-get l a) ⟩
      trans (sym (trans (cong from
                           (sym (get-set l a (get l a))))
                    (left-inverse-of _)))
        (trans (trans (cong from (sym (get-set l a (get l a))))
                 (left-inverse-of _))
           (set-get l a))                                                ≡⟨ trans-sym-[trans] _ _ ⟩∎

      set-get l a                                                        ∎

    lemma₃ = λ a b₁ b₂ →
      trans (set-set l′ a b₁ b₂) (s a b₂)                           ≡⟨⟩

      trans (trans (cong (λ set → set (set a b₁) b₂)
                      (⟨ext⟩ (⟨ext⟩ ⊚ s)))
               (trans (set-set l a b₁ b₂)
                  (sym (s a b₂))))
        (s a b₂)                                                    ≡⟨ cong (λ eq → trans eq (s a b₂)) $ sym $
                                                                       trans-assoc _ _ (sym (s a b₂)) ⟩
      trans (trans (trans (cong (λ set → set (set a b₁) b₂)
                             (⟨ext⟩ (⟨ext⟩ ⊚ s)))
                      (set-set l a b₁ b₂))
               (sym (s a b₂)))
        (s a b₂)                                                    ≡⟨ trans-[trans-sym]- _ (s a b₂) ⟩∎

      trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
        (set-set l a b₁ b₂)                                         ∎

------------------------------------------------------------------------
-- Isomorphisms expressed using lens quasi-inverses

private

  module B {a} =
    Bi-invertibility
      equality-with-J (Set a) Lens
      Lens-combinators.id Lens-combinators._∘_
  module BM {a} =
    B.More {a = a}
      Lens-combinators.left-identity
      Lens-combinators.right-identity
      Lens-combinators.associativity

-- A form of isomorphism between types, expressed using lenses.

open B public using (_≅_; Has-quasi-inverse)

-- An equality characterisation lemma for A ≅ B that applies when A is
-- a set.

equality-characterisation-for-sets-≅ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≅ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≅
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂            ↔⟨ BM.equality-characterisation-≅-domain (lens-preserves-h-level-of-domain 1 A-set) _ _ ⟩
  l₁₁ ≡ l₁₂          ↝⟨ equality-characterisation-for-sets A-set ⟩□
  set l₁₁ ≡ set l₁₂  □
  where
  open Lens

-- There is a split surjection from A ≅ B to A ≃ B.

≅↠≃ : (A ≅ B) ↠ (A ≃ B)
≅↠≃ {A = A} {B = B} = record
  { logical-equivalence = record
    { to   = λ (l₁ , l₂ , eq₁ , eq₂) → Eq.↔⇒≃ (record
               { surjection = record
                 { logical-equivalence = record
                   { to   = get l₁
                   ; from = get l₂
                   }
                 ; right-inverse-of = ext⁻¹ $
                     getters-equal-if-setters-equal (l₁ ∘ l₂) id
                       (cong set eq₁)
               }
               ; left-inverse-of = ext⁻¹ $
                   getters-equal-if-setters-equal (l₂ ∘ l₁) id
                     (cong set eq₂)
               })
    ; from = λ A≃B → ≃→lens A≃B
                   , ≃→lens (inverse A≃B)
                   , lemma A≃B
                   , (≃→lens (inverse A≃B) ∘ ≃→lens A≃B  ≡⟨ cong (λ A≃B′ → ≃→lens (inverse A≃B) ∘ ≃→lens A≃B′) $
                                                            sym $ Eq.inverse-involutive ext _ ⟩
                      ≃→lens (inverse A≃B) ∘
                      ≃→lens (inverse $ inverse A≃B)     ≡⟨ lemma (inverse A≃B) ⟩∎

                      id                                 ∎)
    }
  ; right-inverse-of = λ _ → Eq.lift-equality ext (refl _)
  }
  where
  open Lens
  open Lens-combinators

  lemma :
    (C≃D : C ≃ D) → ≃→lens C≃D ∘ ≃→lens (inverse C≃D) ≡ id
  lemma C≃D = _↔_.from equality-characterisation₂
    ( ⟨ext⟩ (_≃_.right-inverse-of C≃D)
    , (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
    , lemma₁
    , lemma₂
    , lemma₃
    )
    where
    lemma₁ = λ d₁ d₂ →
      let lemma =
            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)      ≡⟨ cong (cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))) $
                                                                     ext-const (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
              (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)     ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₂)))
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D)                  ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (_≃_.to C≃D ⊚ _≃_.from C≃D)
              (cong (λ set → set d₂)
                 (⟨ext⟩ $ _≃_.right-inverse-of C≃D))              ≡⟨ cong (cong (_≃_.to C≃D ⊚ _≃_.from C≃D)) $ cong-ext _ ⟩

            cong (_≃_.to C≃D ⊚ _≃_.from C≃D)
              (_≃_.right-inverse-of C≃D _)                        ≡⟨ sym $ cong-∘ _ _ (_≃_.right-inverse-of C≃D _) ⟩

            cong (_≃_.to C≃D)
              (cong (_≃_.from C≃D) (_≃_.right-inverse-of C≃D _))  ≡⟨ cong (cong (_≃_.to C≃D)) $ _≃_.right-left-lemma C≃D _ ⟩∎

            cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _)         ∎
      in

      trans (sym
        (trans (cong (λ set → _≃_.to C≃D (_≃_.from C≃D (set d₁ d₂)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D))
           (cong (λ get → get d₂)
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D))))
      (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
         (_≃_.right-inverse-of C≃D _))                                ≡⟨ cong₂ (λ p q → trans (sym (trans p q))
                                                                                          (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
                                                                                             (_≃_.right-inverse-of C≃D _)))
                                                                           lemma
                                                                           (cong-ext _) ⟩
      trans (sym
        (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
           (_≃_.right-inverse-of C≃D _)))
      (trans (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
         (_≃_.right-inverse-of C≃D _))                                ≡⟨ trans-symˡ (trans _ (_≃_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                          ∎

    lemma₂ = λ d →
      let lemma =
            cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
              (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)    ≡⟨ cong (cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))) $
                                                                   ext-const (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
              (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)   ≡⟨ cong-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

            cong (λ set → set (_≃_.to C≃D (_≃_.from C≃D d)))
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D)                ≡⟨ cong-ext _ ⟩∎

            _≃_.right-inverse-of C≃D _                          ∎
      in
      trans (sym
        (trans (cong (λ set → set d (_≃_.to C≃D (_≃_.from C≃D d)))
                  (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D))
           (cong (λ get → get d)
              (⟨ext⟩ $ _≃_.right-inverse-of C≃D))))
        (trans
           (cong (_≃_.to C≃D) (_≃_.left-inverse-of C≃D _))
           (_≃_.left-inverse-of (inverse C≃D) _))                   ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                         (cong₂ trans lemma (cong-ext _))
                                                                         (cong₂ trans
                                                                            (_≃_.left-right-lemma C≃D _)
                                                                            (Eq.left-inverse-of∘inverse C≃D)) ⟩
      trans (sym (trans (_≃_.right-inverse-of C≃D _)
                    (_≃_.right-inverse-of C≃D _)))
        (trans (_≃_.right-inverse-of C≃D _)
           (_≃_.right-inverse-of C≃D _))                            ≡⟨ trans-symˡ (trans _ (_≃_.right-inverse-of C≃D _)) ⟩∎

      refl _                                                        ∎

    lemma₃ = λ d d₁ d₂ →
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
        (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (trans (refl _)
           (cong (_≃_.to C≃D)
              (trans
                 (cong (λ _ → _≃_.from C≃D d₂)
                    (_≃_.right-inverse-of (inverse C≃D)
                       (_≃_.from C≃D d₁)))
                 (refl _))))                             ≡⟨ cong (λ eq → subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
                                                                           (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
                                                                           (trans (refl _) (cong (_≃_.to C≃D) eq))) $
                                                            trans-reflʳ _ ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
        (⟨ext⟩ λ _ → ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (trans (refl _)
           (cong (_≃_.to C≃D)
              (cong (λ _ → _≃_.from C≃D d₂)
                 (_≃_.right-inverse-of (inverse C≃D)
                    (_≃_.from C≃D d₁)))))                ≡⟨ cong₂ (λ p q → subst (λ set → set (set d d₁) d₂ ≡ set d d₂) p q)
                                                              (ext-const (⟨ext⟩ $ _≃_.right-inverse-of C≃D))
                                                              (trans-reflˡ _) ⟩
      subst (λ set → set (set d d₁) d₂ ≡ set d d₂)
        (cong const $ ⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (cong (_≃_.to C≃D)
           (cong (λ _ → _≃_.from C≃D d₂)
              (_≃_.right-inverse-of (inverse C≃D)
                 (_≃_.from C≃D d₁))))                    ≡⟨ sym $ subst-∘ _ _ (⟨ext⟩ $ _≃_.right-inverse-of C≃D) ⟩

      subst (λ set → set d₂ ≡ set d₂)
        (⟨ext⟩ $ _≃_.right-inverse-of C≃D)
        (cong (_≃_.to C≃D)
           (cong (λ _ → _≃_.from C≃D d₂)
              (_≃_.right-inverse-of (inverse C≃D)
                 (_≃_.from C≃D d₁))))                    ≡⟨ subst-ext _ _ ⟩

      subst (λ set → set ≡ set)
        (_≃_.right-inverse-of C≃D d₂)
        (cong (_≃_.to C≃D)
           (cong (λ _ → _≃_.from C≃D d₂)
              (_≃_.right-inverse-of (inverse C≃D)
                 (_≃_.from C≃D d₁))))                    ≡⟨ ≡⇒↝ _ (sym [subst≡]≡[trans≡trans]) (

          trans
            (cong (_≃_.to C≃D)
               (cong (λ _ → _≃_.from C≃D d₂)
                  (_≃_.right-inverse-of (inverse C≃D)
                     (_≃_.from C≃D d₁))))
            (_≃_.right-inverse-of C≃D d₂)                     ≡⟨ cong (λ eq → trans (cong (_≃_.to C≃D) eq)
                                                                                (_≃_.right-inverse-of C≃D d₂)) $
                                                                 cong-const (_≃_.right-inverse-of (inverse C≃D) _) ⟩
          trans
            (cong (_≃_.to C≃D) (refl _))
            (_≃_.right-inverse-of C≃D d₂)                     ≡⟨ cong (flip trans _) $ cong-refl _ ⟩

          trans (refl _) (_≃_.right-inverse-of C≃D d₂)        ≡⟨ trans-reflˡ _ ⟩

          _≃_.right-inverse-of C≃D d₂                         ≡⟨ sym $ trans-reflʳ _ ⟩

          trans (_≃_.right-inverse-of C≃D d₂) (refl _)        ∎) ⟩

      refl _                                             ∎

-- The right-to-left direction of ≅↠≃ maps identity to an isomorphism
-- for which the first projection is the identity.

≅↠≃-id≡id :
  let open Lens-combinators in
  proj₁ (_↠_.from ≅↠≃ F.id) ≡ id {A = A}
≅↠≃-id≡id = equal-laws→≡
  (λ _ _ → refl _)
  (λ a →
     _≃_.left-inverse-of F.id a               ≡⟨ sym $ _≃_.right-left-lemma F.id _ ⟩
     cong P.id (_≃_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                       ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                   ∎)
  (λ _ _ _ → refl _)
  where
  open Lens-combinators

-- If A is a set, then there is an equivalence between A ≃ B and A ≅ B.

≃≃≅ :
  Is-set A →
  (A ≃ B) ≃ (A ≅ B)
≃≃≅ {A = A} {B = B} A-set = Eq.↔⇒≃ $ inverse (record
  { surjection      = ≅↠≃
  ; left-inverse-of = λ (l₁ , l₂ , eq₁ , eq₂) →
      _↔_.from (equality-characterisation-for-sets-≅ A-set) $
      ⟨ext⟩ λ a → ⟨ext⟩ λ b →
        get l₂ b                                            ≡⟨ sym $ ext⁻¹ (ext⁻¹ (cong set eq₂) _) _ ⟩

        set l₁ (set l₁ a b)
          (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))         ≡⟨ set-set l₁ _ _ _ ⟩

        set l₁ a (set l₂ (get l₁ (set l₁ a b)) (get l₂ b))  ≡⟨ cong (λ b′ → set l₁ a (set l₂ b′ (get l₂ b))) $ get-set l₁ _ _ ⟩

        set l₁ a (set l₂ b (get l₂ b))                      ≡⟨ cong (set l₁ a) $ set-get l₂ _ ⟩∎

        set l₁ a b                                          ∎
  })
  where
  open Lens
  open Lens-combinators

-- The equivalence maps identity to an isomorphism for which the first
-- projection is the identity.

≃≃≅-id≡id :
  let open Lens-combinators in
  (A-set : Is-set A) →
  proj₁ (_≃_.to (≃≃≅ A-set) F.id) ≡ id
≃≃≅-id≡id _ = ≅↠≃-id≡id

-- There is not necessarily a split surjection from
-- Is-equivalence (Lens.get l) to Has-quasi-inverse l, if l is a lens
-- between types in the same universe (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-type-of-refl-propositional.)

¬Is-equivalence↠Has-quasi-inverse :
  Univalence a →
  ¬ ({A B : Set a}
     (l : Lens A B) →
     Is-equivalence (Lens.get l) ↠ Has-quasi-inverse l)
¬Is-equivalence↠Has-quasi-inverse _ surj =      $⟨ ⊤-contractible ⟩
  Contractible ⊤                                ↝⟨ H-level.respects-surjection lemma₁ 0 ⟩

  Contractible (∃ λ (g : (x : X) → x ≡ x) → _)  ↝⟨ flip proj₁-closure 0
                                                     (λ g → (λ _ x → sym (g x)) , lemma₂ g , lemma₃ g , lemma₄ g) ⟩

  Contractible ((x : X) → x ≡ x)                ↝⟨ mono₁ 0 ⟩

  Is-proposition ((x : X) → x ≡ x)              ↝⟨ ¬-prop ⟩□

  ⊥                                             □
  where
  open Lens-combinators

  X,¬-prop = Circle.¬-type-of-refl-propositional
  X        = proj₁ X,¬-prop
  ¬-prop   = proj₂ X,¬-prop

  lemma₁ =
    ⊤                                                                ↔⟨ inverse $ _⇔_.to contractible⇔↔⊤ $
                                                                        propositional⇒inhabited⇒contractible
                                                                          (Eq.propositional ext _)
                                                                          (_≃_.is-equivalence Eq.id) ⟩

    Is-equivalence (P.id {A = X})                                    ↝⟨ surj id ⟩

    Has-quasi-inverse id                                             ↔⟨ BM.Has-quasi-inverse≃id≡id-domain
                                                                          (id , left-identity _ , right-identity _) ⟩

    id ≡ id                                                          ↔⟨ equality-characterisation₄ ⟩□

    (∃ λ (g : ∀ x → x ≡ x) →
     ∃ λ (s : X → ∀ x → x ≡ x) →
       (∀ x y →
          trans (sym (trans (cong P.id (s x y)) (g y))) (refl _) ≡
          refl _) ×
       (∀ x →
          trans (sym (trans (s x x) (cong P.id (g x)))) (refl _) ≡
          refl _) ×
       (∀ x y z →
         trans (refl _) (s x z) ≡
         trans (cong (λ set → set (set x y) z) (⟨ext⟩ (⟨ext⟩ ⊚ s)))
           (refl _)))                                                □

  lemma₂ : (g : ∀ x → x ≡ x) (x y : X) → _
  lemma₂ g x y =
    trans (sym (trans (cong P.id (sym (g y))) (g y))) (refl _)  ≡⟨ trans-reflʳ _ ⟩
    sym (trans (cong P.id (sym (g y))) (g y))                   ≡⟨ cong (λ eq → sym (trans eq (g y))) $ sym $ cong-id _ ⟩
    sym (trans (sym (g y)) (g y))                               ≡⟨ cong sym $ trans-symˡ (g y) ⟩
    sym (refl _)                                                ≡⟨ sym-refl ⟩∎
    refl _                                                      ∎

  lemma₃ : (g : ∀ x → x ≡ x) (x : X) → _
  lemma₃ g x =
    trans (sym (trans (sym (g x)) (cong P.id (g x)))) (refl _)  ≡⟨ trans-reflʳ _ ⟩
    sym (trans (sym (g x)) (cong P.id (g x)))                   ≡⟨ cong (λ eq → sym (trans (sym (g x)) eq)) $ sym $ cong-id (g x) ⟩
    sym (trans (sym (g x)) (g x))                               ≡⟨ cong sym $ trans-symˡ (g x) ⟩
    sym (refl _)                                                ≡⟨ sym-refl ⟩∎
    refl _                                                      ∎

  lemma₄ : (g : ∀ x → x ≡ x) (x y z : X) → _
  lemma₄ g x y z =
    trans (refl _) (sym (g z))                                            ≡⟨ trans-reflˡ (sym (g z)) ⟩
    sym (g z)                                                             ≡⟨ sym $ cong-ext (sym ⊚ g) ⟩
    cong (_$ z) (⟨ext⟩ (sym ⊚ g))                                         ≡⟨ sym $ cong-∘ _ _ (⟨ext⟩ (sym ⊚ g)) ⟩
    cong (λ set → set (set x y) z) (cong const (⟨ext⟩ (sym ⊚ g)))         ≡⟨ cong (cong (λ set → set (set x y) z)) $ sym $ ext-const (⟨ext⟩ (sym ⊚ g)) ⟩
    cong (λ set → set (set x y) z) (⟨ext⟩ λ _ → ⟨ext⟩ (sym ⊚ g))          ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans (cong (λ set → set (set x y) z) (⟨ext⟩ λ _ → ⟨ext⟩ (sym ⊚ g)))
      (refl _)                                                            ∎

------------------------------------------------------------------------
-- Isomorphisms expressed using bi-invertibility for lenses

-- A form of isomorphism between types, expressed using lenses.

open B public using (_≊_; Is-bi-invertible)

-- An equality characterisation lemma for A ≊ B that applies when A is
-- a set.

equality-characterisation-for-sets-≊ :
  let open Lens in
  {f₁@(l₁₁ , _) f₂@(l₁₂ , _) : A ≊ B} →
  Is-set A →
  f₁ ≡ f₂ ↔ set l₁₁ ≡ set l₁₂
equality-characterisation-for-sets-≊
  {f₁ = f₁@(l₁₁ , _)} {f₂ = f₂@(l₁₂ , _)} A-set =
  f₁ ≡ f₂            ↔⟨ BM.equality-characterisation-≊ _ _ ⟩
  l₁₁ ≡ l₁₂          ↝⟨ equality-characterisation-for-sets A-set ⟩□
  set l₁₁ ≡ set l₁₂  □
  where
  open Lens

-- There is a split surjection from A ≊ B to A ≃ B.

≊↠≃ : (A ≊ B) ↠ (A ≃ B)
≊↠≃ = record
  { logical-equivalence = record
    { to   = _↠_.to ≅↠≃ ⊚ _↠_.from BM.≅↠≊
    ; from = _↠_.to BM.≅↠≊ ⊚ _↠_.from ≅↠≃
    }
  ; right-inverse-of = λ _ → Eq.lift-equality ext (refl _)
  }

-- The right-to-left direction maps identity to an isomorphism for
-- which the first projection is the identity.

≊↠≃-id≡id :
  let open Lens-combinators in
  proj₁ (_↠_.from ≊↠≃ F.id) ≡ id {A = A}
≊↠≃-id≡id = equal-laws→≡
  (λ _ _ → refl _)
  (λ a →
     _≃_.left-inverse-of F.id a               ≡⟨ sym $ _≃_.right-left-lemma F.id _ ⟩
     cong P.id (_≃_.right-inverse-of F.id a)  ≡⟨⟩
     cong P.id (refl _)                       ≡⟨ sym $ cong-id _ ⟩∎
     refl _                                   ∎)
  (λ _ _ _ → refl _)
  where
  open Lens-combinators

-- If A is a set, then there is an equivalence between A ≊ B and
-- A ≃ B.

≃≃≊ : Is-set A → (A ≃ B) ≃ (A ≊ B)
≃≃≊ {A = A} {B = B} A-set =
  A ≃ B  ↝⟨ ≃≃≅ A-set ⟩
  A ≅ B  ↝⟨ inverse $ BM.≊≃≅-domain (lens-preserves-h-level-of-domain 1 A-set) ⟩□
  A ≊ B  □

-- The equivalence ≃≃≊ maps identity to an isomorphism for which the
-- first projection is the identity.

≃≃≊-id≡id :
  let open Lens-combinators in
  (A-set : Is-set A) →
  proj₁ (_≃_.to (≃≃≊ A-set) F.id) ≡ id
≃≃≊-id≡id _ = ≊↠≃-id≡id

-- The right-to-left direction of ≃≃≊ maps bi-invertible lenses to
-- their getter functions.

to-from-≃≃≊≡get :
  (A-set : Is-set A) (A≊B@(l , _) : A ≊ B) →
  _≃_.to (_≃_.from (≃≃≊ A-set) A≊B) ≡ Lens.get l
to-from-≃≃≊≡get _ _ = refl _

-- The getter function of a bi-invertible lens is an equivalence.

Is-bi-invertible→Is-equivalence-get :
  (l : Lens A B) →
  Is-bi-invertible l → Is-equivalence (Lens.get l)
Is-bi-invertible→Is-equivalence-get l is-bi-inv =
  _≃_.is-equivalence (_↠_.to ≊↠≃ (l , is-bi-inv))

-- There is a bi-invertible lens which does not satisfy a certain
-- coherence law (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.∃≢refl.)

bi-invertible-but-not-coherent :
  Univalence lzero →
  ∃ λ (A : Set) →
  ∃ λ (l : Lens A A) →
    let open Lens l in
    Is-bi-invertible l ×
    ¬ (∀ a → cong get (set-get a) ≡ get-set a (get a))
bi-invertible-but-not-coherent _ =
    𝕊¹
  , l
  , B.Has-quasi-inverse→Is-bi-invertible l
      (l⁻¹ , l∘l⁻¹≡id , l⁻¹∘l≡id)
  , (((x : 𝕊¹) → cong (get l) (set-get l x) ≡ get-set l x (get l x))  ↔⟨⟩
     ((x : 𝕊¹) → cong P.id (refl _) ≡ proj₁ Circle.∃≢refl x)          ↝⟨ trans (cong-id _) ⊚_ ⟩
     ((x : 𝕊¹) → refl _ ≡ proj₁ Circle.∃≢refl x)                      ↔⟨ Eq.extensionality-isomorphism ext ⟩
     refl ≡ proj₁ Circle.∃≢refl                                       ↝⟨ proj₂ Circle.∃≢refl ⊚ sym ⟩□
     ⊥                                                                □)
  where
  open Lens
  open Lens-combinators

  l : Lens 𝕊¹ 𝕊¹
  l = record
    { get     = P.id
    ; set     = const P.id
    ; get-set = λ _ → proj₁ Circle.∃≢refl
    ; set-get = λ _ → refl _
    ; set-set = λ _ _ _ → refl _
    }

  l⁻¹ = record
    { get     = P.id
    ; set     = const P.id
    ; get-set = λ _ → sym ⊚ proj₁ Circle.∃≢refl
    ; set-get = λ _ → refl _
    ; set-set = λ _ _ _ → refl _
    }

  l∘l⁻¹≡id : l ∘ l⁻¹ ≡ id
  l∘l⁻¹≡id = equal-laws→≡
    (λ x y →
       get-set (l ∘ l⁻¹) x y                            ≡⟨⟩

       trans (cong P.id $ sym $ proj₁ Circle.∃≢refl y)
         (proj₁ Circle.∃≢refl y)                        ≡⟨ cong (λ eq → trans eq (proj₁ Circle.∃≢refl y)) $ sym $
                                                           cong-id (sym $ proj₁ Circle.∃≢refl y) ⟩
       trans (sym $ proj₁ Circle.∃≢refl y)
         (proj₁ Circle.∃≢refl y)                        ≡⟨ trans-symˡ (proj₁ Circle.∃≢refl y) ⟩∎

       refl _                                           ∎)
    (λ x →
       set-get (l ∘ l⁻¹) x                  ≡⟨⟩
       trans (cong P.id (refl _)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
       cong P.id (refl _)                   ≡⟨ cong-refl _ ⟩∎
       refl _                               ∎)
    (λ x y z →
       set-set (l ∘ l⁻¹) x y z                                            ≡⟨⟩
       trans (refl _)
         (cong P.id (trans (cong (λ _ → z) (get-set l⁻¹ x y)) (refl _)))  ≡⟨ trans-reflˡ _ ⟩
       cong P.id (trans (cong (λ _ → z) (get-set l⁻¹ x y)) (refl _))      ≡⟨ sym $ cong-id _ ⟩
       trans (cong (λ _ → z) (get-set l⁻¹ x y)) (refl _)                  ≡⟨ trans-reflʳ _ ⟩
       cong (λ _ → z) (get-set l⁻¹ x y)                                   ≡⟨ cong-const _ ⟩∎
       refl _                                                             ∎)

  l⁻¹∘l≡id : l⁻¹ ∘ l ≡ id
  l⁻¹∘l≡id = equal-laws→≡
    (λ x y →
       get-set (l⁻¹ ∘ l) x y                                        ≡⟨⟩

       trans (cong P.id (proj₁ Circle.∃≢refl y))
         (sym $ proj₁ Circle.∃≢refl y)                              ≡⟨ cong (λ eq → trans eq (sym $ proj₁ Circle.∃≢refl y)) $ sym $
                                                                       cong-id (proj₁ Circle.∃≢refl y) ⟩

       trans (proj₁ Circle.∃≢refl y) (sym $ proj₁ Circle.∃≢refl y)  ≡⟨ trans-symʳ (proj₁ Circle.∃≢refl y) ⟩∎

       refl _                                                       ∎)
    (λ x →
       set-get (l⁻¹ ∘ l) x                  ≡⟨⟩
       trans (cong P.id (refl _)) (refl _)  ≡⟨ trans-reflʳ _ ⟩
       cong P.id (refl _)                   ≡⟨ cong-refl _ ⟩∎
       refl _                               ∎)
    (λ x y z →
       set-set (l⁻¹ ∘ l) x y z                                          ≡⟨⟩
       trans (refl _)
         (cong P.id (trans (cong (λ _ → z) (get-set l x y)) (refl _)))  ≡⟨ trans-reflˡ _ ⟩
       cong P.id (trans (cong (λ _ → z) (get-set l x y)) (refl _))      ≡⟨ sym $ cong-id _ ⟩
       trans (cong (λ _ → z) (get-set l x y)) (refl _)                  ≡⟨ trans-reflʳ _ ⟩
       cong (λ _ → z) (get-set l x y)                                   ≡⟨ cong-const _ ⟩∎
       refl _                                                           ∎)

-- There are two bi-invertible lenses with the same getter that are
-- not equal (assuming univalence).

bi-invertible-with-same-getter-but-not-equal :
  Univalence lzero →
  ∃ λ (A : Set) →
  ∃ λ (l₁ : Lens A A) →
  ∃ λ (l₂ : Lens A A) →
    Is-bi-invertible l₁ ×
    Is-bi-invertible l₂ ×
    Lens.get l₁ ≡ Lens.get l₂ ×
    l₁ ≢ l₂
bi-invertible-with-same-getter-but-not-equal univ =
  let A , l , bi-inv , not-coherent =
        bi-invertible-but-not-coherent univ
  in
    A
  , l
  , id
  , bi-inv
  , ((id , right-identity id) , (id , left-identity id))
  , refl _
  , (l ≡ id                                                      ↝⟨ (λ eq → subst (λ l → ∀ a → cong (get l) (set-get l a) ≡
                                                                                               get-set l a (get l a))
                                                                                  (sym eq)
                                                                                  (λ _ → cong-refl _)) ⟩
     (∀ a → cong (get l) (set-get l a) ≡ get-set l a (get l a))  ↝⟨ not-coherent ⟩□
     ⊥                                                           □)
  where
  open Lens
  open Lens-combinators

-- There is in general no split surjection from equivalences to
-- bi-invertible lenses, if the right-to-left direction of the split
-- surjection is required to map bi-invertible lenses to their getter
-- functions (assuming univalence).

¬≃↠≊ :
  Univalence lzero →
  ∃ λ (A : Set) →
  ¬ ∃ λ (≃↠≊ : (A ≃ A) ↠ (A ≊ A)) →
      (A≊A@(l , _) : A ≊ A) →
      _≃_.to (_↠_.from ≃↠≊ A≊A) ≡ Lens.get l
¬≃↠≊ univ =
  let A , l₁ , l₂ , bi-inv₁ , bi-inv₂ , getters-equal , l₁≢l₂ =
        bi-invertible-with-same-getter-but-not-equal univ
  in
    A
  , (λ (≃↠≊ , hyp) →                           $⟨ getters-equal ⟩

       Lens.get l₁ ≡ Lens.get l₂               ↝⟨ (λ eq → trans (hyp _) (trans eq (sym (hyp _)))) ⟩

       _≃_.to (_↠_.from ≃↠≊ (l₁ , bi-inv₁)) ≡
       _≃_.to (_↠_.from ≃↠≊ (l₂ , bi-inv₂))    ↝⟨ Eq.lift-equality ext ⟩

       _↠_.from ≃↠≊ (l₁ , bi-inv₁) ≡
       _↠_.from ≃↠≊ (l₂ , bi-inv₂)             ↝⟨ _↠_.to (Surjection.↠-≡ ≃↠≊) ⟩

       (l₁ , bi-inv₁) ≡ (l₂ , bi-inv₂)         ↝⟨ cong proj₁ ⟩

       l₁ ≡ l₂                                 ↝⟨ l₁≢l₂ ⟩□

       ⊥                                       □)

-- There is in general no equivalence between equivalences and
-- bi-invertible lenses, if the right-to-left direction of the
-- equivalence is required to map bi-invertible lenses to their getter
-- functions (assuming univalence).

¬≃≃≊ :
  Univalence lzero →
  ∃ λ (A : Set) →
  ¬ ∃ λ (≃≃≊ : (A ≃ A) ≃ (A ≊ A)) →
      (A≊A@(l , _) : A ≊ A) →
      _≃_.to (_≃_.from ≃≃≊ A≊A) ≡ Lens.get l
¬≃≃≊ univ =
  Σ-map P.id (_⊚ Σ-map _≃_.surjection P.id)
    (¬≃↠≊ univ)

-- If the getter function is an equivalence, then the lens is
-- bi-invertible.

Is-equivalence-get→Is-bi-invertible :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) → Is-bi-invertible l
Is-equivalence-get→Is-bi-invertible {A = A} {B = B} l′ is-equiv =
  block λ b →
                       $⟨ l⁻¹′ b , l∘l⁻¹≡id b , l⁻¹∘l≡id b ⟩
  Has-quasi-inverse l  ↝⟨ B.Has-quasi-inverse→Is-bi-invertible l ⟩
  Is-bi-invertible l   ↝⟨ subst Is-bi-invertible (getter-equivalence→lens≡ l′ is-equiv) ⟩□
  Is-bi-invertible l′  □
  where
  open Lens
  open Lens-combinators

  -- A lens that is equal to l′.

  l : Lens A B
  l = getter-equivalence→lens l′ is-equiv

  A≃B = Eq.⟨ get l , is-equiv ⟩

  open _≃_ A≃B

  -- An inverse of l.
  --
  -- Note that the set-get and set-set proofs have been "obfuscated".
  -- They could have been shorter, but then it might not have been
  -- possible to prove l∘l⁻¹≡id and l⁻¹∘l≡id.

  l⁻¹ : Lens B A
  l⁻¹ = record
    { get     = from
    ; set     = λ _ → get l
    ; get-set = λ _ a →
                  from (get l a)  ≡⟨ left-inverse-of a ⟩∎
                  a               ∎
    ; set-get = λ b →
                  get l (from b)                 ≡⟨ sym $ cong (get l) $ set-get l (from b) ⟩
                  get l (from (get l (from b)))  ≡⟨ right-inverse-of (get l (from b)) ⟩
                  get l (from b)                 ≡⟨ right-inverse-of b ⟩∎
                  b                              ∎
    ; set-set = λ b a₁ a₂ →
                  get l a₂                 ≡⟨ sym $ right-inverse-of _ ⟩
                  get l (from (get l a₂))  ≡⟨ sym $ cong (get l) (set-set l (from b) (get l a₁) (get l a₂)) ⟩
                  get l (from (get l a₂))  ≡⟨ right-inverse-of _ ⟩∎
                  get l a₂                 ∎
    }

  -- A blocked variant of l⁻¹.

  l⁻¹′ : Block "l⁻¹" → Lens B A
  l⁻¹′ ⊠ = l⁻¹

  -- The lens l⁻¹ is a right inverse of l.

  l∘l⁻¹≡id : ∀ b → l ∘ l⁻¹′ b ≡ id
  l∘l⁻¹≡id ⊠ = constant-setter→≡id
    ( right-inverse-of
    , right-inverse-of
    , (λ b₁ b₂ →
        get-set (l ∘ l⁻¹) b₁ b₂                                 ≡⟨⟩

        trans (cong (get l) (get-set l⁻¹ b₁ (from b₂)))
          (get-set l (from b₁) b₂)                              ≡⟨⟩

        trans (cong (get l) (left-inverse-of (from b₂)))
          (right-inverse-of b₂)                                 ≡⟨ cong (λ eq → trans (cong (get l) eq) (right-inverse-of b₂)) $ sym $
                                                                   right-left-lemma _ ⟩
        trans (cong (get l) (cong from (right-inverse-of b₂)))
          (right-inverse-of b₂)                                 ≡⟨ cong (λ eq → trans eq (right-inverse-of b₂)) $
                                                                   cong-∘ _ _ (right-inverse-of b₂) ⟩
        trans (cong (get l ⊚ from) (right-inverse-of b₂))
          (right-inverse-of b₂)                                 ≡⟨⟩

        trans (cong (get (l ∘ l⁻¹)) (right-inverse-of b₂))
          (right-inverse-of b₂)                                 ∎)
    , (λ b →
         set-get (l ∘ l⁻¹) b                                 ≡⟨⟩

         trans (cong (get l) (set-get l (from b)))
           (set-get l⁻¹ b)                                   ≡⟨⟩

         trans (cong (get l) (set-get l (from b)))
           (trans (sym (cong (get l) (set-get l (from b))))
              (trans (right-inverse-of (get l (from b)))
                 (right-inverse-of b)))                      ≡⟨ trans--[trans-sym] _ _ ⟩

         trans (right-inverse-of (get l (from b)))
           (right-inverse-of b)                              ≡⟨⟩

         trans (right-inverse-of (get (l ∘ l⁻¹) b))
           (right-inverse-of b)                              ∎)
    , (λ b b₁ b₂ →
         set-set (l ∘ l⁻¹) b b₁ b₂                                      ≡⟨⟩

         trans (set-set l⁻¹ b (from b₁) (from b₂))
           (cong (get l)
              (trans (cong (λ _ → from b₂)
                        (get-set l⁻¹ b (from b₁)))
                 (set-set l (from b) b₁ b₂)))                           ≡⟨⟩

         trans (set-set l⁻¹ b (from b₁) (from b₂))
           (cong (get l)
              (trans (cong (λ _ → from b₂)
                        (left-inverse-of (from b₁)))
                 (set-set l (from b) b₁ b₂)))                           ≡⟨ cong (λ eq → trans (set-set l⁻¹ b (from b₁) (from b₂))
                                                                                           (cong (get l) (trans eq (set-set l (from b) b₁ b₂)))) $
                                                                           cong-const (left-inverse-of (from b₁)) ⟩
         trans (set-set l⁻¹ b (from b₁) (from b₂))
           (cong (get l) (trans (refl _) (set-set l (from b) b₁ b₂)))   ≡⟨ cong (λ eq → trans (set-set l⁻¹ b (from b₁) (from b₂))
                                                                                           (cong (get l) eq)) $
                                                                           trans-reflˡ (set-set l (from b) b₁ b₂) ⟩
         trans (set-set l⁻¹ b (from b₁) (from b₂))
           (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨⟩

         trans (trans (sym (right-inverse-of _))
                  (trans (sym (cong (get l)
                                 (set-set l (from b) (get l (from b₁))
                                    (get l (from b₂)))))
                     (right-inverse-of _)))
           (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ cong (λ b′ → trans (trans (sym (right-inverse-of _))
                                                                                                 (trans (sym (cong (get l)
                                                                                                                (set-set l (from b) b′
                                                                                                                   (get l (from b₂)))))
                                                                                                    (right-inverse-of _)))
                                                                                          (cong (get l) (set-set l (from b) b₁ b₂))) $
                                                                           right-inverse-of _ ⟩
         trans (trans (sym (right-inverse-of _))
                  (trans (sym (cong (get l)
                                 (set-set l (from b) b₁
                                    (get l (from b₂)))))
                     (right-inverse-of _)))
           (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ cong (λ f → trans (trans (sym (f _))
                                                                                                (trans (sym (cong (get l)
                                                                                                               (set-set l (from b) b₁
                                                                                                                  (get l (from b₂)))))
                                                                                                   (f _)))
                                                                                         (cong (get l) (set-set l (from b) b₁ b₂))) $ sym $
                                                                           _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext)
                                                                             right-inverse-of ⟩
         trans (trans (sym (ext⁻¹ (⟨ext⟩ right-inverse-of) _))
                  (trans (sym (cong (get l)
                                 (set-set l (from b) b₁
                                    (get l (from b₂)))))
                     (ext⁻¹ (⟨ext⟩ right-inverse-of) _)))
           (cong (get l) (set-set l (from b) b₁ b₂))                    ≡⟨ elim₁
                                                                             (λ {f} (p : f ≡ P.id) →
                                                                                (q : ∀ b → f b ≡ f b) →
                                                                                trans (trans (sym (ext⁻¹ p (f b₂)))
                                                                                         (trans (sym (q (f b₂))) (ext⁻¹ p (f b₂))))
                                                                                  (q b₂) ≡
                                                                                refl _)
                                                                             (λ q →
             trans (trans (sym (ext⁻¹ (refl P.id) _))
                      (trans (sym (q _)) (ext⁻¹ (refl P.id) _)))
               (q _)                                                            ≡⟨ cong (λ eq → trans (trans (sym eq) (trans (sym (q _)) eq))
                                                                                                  (q _)) $
                                                                                   ext⁻¹-refl _ ⟩
             trans (trans (sym (refl _))
                      (trans (sym (q _)) (refl _)))
               (q _)                                                            ≡⟨ cong₂ (λ p r → trans (trans p r) (q _))
                                                                                     sym-refl
                                                                                     (trans-reflʳ _) ⟩

             trans (trans (refl _) (sym (q _))) (q _)                           ≡⟨ cong (λ eq → trans eq (q _)) $ trans-reflˡ (sym (q _)) ⟩

             trans (sym (q _)) (q _)                                            ≡⟨ trans-symˡ (q _) ⟩∎

             refl _                                                             ∎)
                                                                             (⟨ext⟩ right-inverse-of)
                                                                             (cong (get l) ⊚ set-set l (from b) b₁) ⟩
         refl _                                                         ∎)
    )

  -- The lens l⁻¹ is a left inverse of l.

  l⁻¹∘l≡id : ∀ b → l⁻¹′ b ∘ l ≡ id
  l⁻¹∘l≡id ⊠ = constant-setter→≡id
    ( left-inverse-of
    , left-inverse-of
    , (λ a₁ a₂ →
         get-set (l⁻¹ ∘ l) a₁ a₂                                ≡⟨⟩

         trans (cong from (get-set l a₁ (to a₂)))
           (get-set l⁻¹ (get l a₁) a₂)                          ≡⟨⟩

         trans (cong from (right-inverse-of (to a₂)))
           (left-inverse-of a₂)                                 ≡⟨ cong (λ eq → trans (cong from eq) (left-inverse-of _)) $ sym $
                                                                   left-right-lemma _ ⟩
         trans (cong from (cong (get l) (left-inverse-of a₂)))
           (left-inverse-of a₂)                                 ≡⟨ cong (λ eq → trans eq (left-inverse-of _)) $
                                                                   cong-∘ _ _ (left-inverse-of _) ⟩
         trans (cong (from ⊚ get l) (left-inverse-of a₂))
           (left-inverse-of a₂)                                 ≡⟨⟩

         trans (cong (get (l⁻¹ ∘ l)) (left-inverse-of a₂))
           (left-inverse-of a₂)                                 ∎)
    , (λ a →
         let lemma₁ =
               cong from
                 (trans (sym (cong (get l)
                                (set-get l (from (get l a)))))
                    (trans (right-inverse-of _)
                       (right-inverse-of _)))                            ≡⟨ cong-trans _ _ (trans _ (right-inverse-of _)) ⟩

               trans (cong from (sym (cong (get l)
                                        (set-get l (from (get l a))))))
                 (cong from (trans (right-inverse-of _)
                               (right-inverse-of _)))                    ≡⟨ cong (λ eq → trans (cong from eq)
                                                                                           (cong from (trans (right-inverse-of _)
                                                                                                         (right-inverse-of _)))) $ sym $
                                                                            cong-sym _ (set-get l (from (get l a))) ⟩
               trans (cong from (cong (get l)
                                   (sym (set-get l (from (get l a))))))
                 (cong from (trans (right-inverse-of _)
                               (right-inverse-of _)))                    ≡⟨ cong₂ trans
                                                                              (cong-∘ _ _ (sym (set-get l (from (get l a)))))
                                                                              (cong-trans _ _ (right-inverse-of _)) ⟩
               trans (cong (from ⊚ get l)
                        (sym (set-get l (from (get l a)))))
                 (trans (cong from (right-inverse-of _))
                    (cong from (right-inverse-of _)))                    ≡⟨ cong₂ (λ p q → trans (cong (from ⊚ get l)
                                                                                                    (sym (set-get l (from (get l a)))))
                                                                                             (trans p q))
                                                                              (right-left-lemma _)
                                                                              (right-left-lemma _) ⟩∎
               trans (cong (from ⊚ get l)
                        (sym (set-get l (from (get l a)))))
                 (trans (left-inverse-of _)
                    (left-inverse-of _))                                 ∎

             f = from ⊚ get l

             lemma₂ : ∀ _ → _
             lemma₂ = λ a →
               trans (left-inverse-of (f a))
                 (left-inverse-of a)                        ≡⟨ cong (λ g → trans (g (f a)) (g a)) $ sym $
                                                               _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext)
                                                                 left-inverse-of ⟩∎
               trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))
                 (ext⁻¹ (⟨ext⟩ left-inverse-of) a)          ∎

             lemma₃ =
               trans (ext⁻¹ (refl P.id) a) (ext⁻¹ (refl P.id) a)  ≡⟨ cong₂ trans (ext⁻¹-refl _) (ext⁻¹-refl _) ⟩
               trans (refl _) (refl _)                            ≡⟨ trans-refl-refl ⟩∎
               refl _                                             ∎
         in
         trans (cong from (set-get l⁻¹ (get l a)))
           (set-get l a)                                            ≡⟨⟩

         trans (cong from
                  (trans (sym (cong (get l)
                                 (set-get l (from (get l a)))))
                     (trans (right-inverse-of _)
                        (right-inverse-of _))))
           (set-get l a)                                            ≡⟨ cong (λ eq → trans eq (set-get l a)) lemma₁ ⟩

         trans (trans (cong f (sym (set-get l (f a))))
                  (trans (left-inverse-of (f (f a)))
                     (left-inverse-of (f a))))
           (set-get l a)                                            ≡⟨ cong (λ eq → trans (trans (cong f (sym (set-get l (f a)))) eq)
                                                                                      (set-get l a)) $
                                                                       lemma₂ _ ⟩
         trans (trans (cong f (sym (set-get l (f a))))
                  (trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f (f a)))
                     (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))))
           (set-get l a)                                            ≡⟨ elim₁
                                                                         (λ {f} (p : f ≡ P.id) →
                                                                            (q : ∀ a → f a ≡ a) →
                                                                            trans (trans (cong f (sym (q (f a))))
                                                                                     (trans (ext⁻¹ p (f (f a))) (ext⁻¹ p (f a))))
                                                                              (q a) ≡
                                                                            trans (ext⁻¹ p (f a)) (ext⁻¹ p a))
                                                                         (λ q →
             trans (trans (cong P.id (sym (q a)))
                      (trans (ext⁻¹ (refl P.id) a)
                         (ext⁻¹ (refl P.id) a)))
               (q a)                                                        ≡⟨ cong₂ (λ p r → trans (trans p r) (q a))
                                                                                 (sym $ cong-id _)
                                                                                 lemma₃ ⟩

             trans (trans (sym (q a)) (refl _)) (q a)                       ≡⟨ cong (flip trans _) $ trans-reflʳ _ ⟩

             trans (sym (q a)) (q a)                                        ≡⟨ trans-symˡ (q a) ⟩

             refl _                                                         ≡⟨ sym lemma₃ ⟩∎

             trans (ext⁻¹ (refl P.id) a) (ext⁻¹ (refl P.id) a)              ∎)
                                                                         (⟨ext⟩ left-inverse-of)
                                                                         (set-get l) ⟩
         trans (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a))
           (ext⁻¹ (⟨ext⟩ left-inverse-of) a)                        ≡⟨ sym $ lemma₂ _ ⟩

         trans (left-inverse-of (f a))
           (left-inverse-of a)                                      ≡⟨⟩

         trans (left-inverse-of (get (l⁻¹ ∘ l) a))
           (left-inverse-of a)                                      ∎)
    , (λ a a₁ a₂ →
         let q = set-set l a (get l a₁) (get l a₂)

             lemma =
               cong from
                 (trans (sym (right-inverse-of _))
                    (trans (sym (cong (get l) q))
                       (right-inverse-of _)))                    ≡⟨ cong-trans _ _ (trans (sym (cong (get l) q)) (right-inverse-of _)) ⟩

               trans (cong from (sym (right-inverse-of _)))
                 (cong from (trans (sym (cong (get l) q))
                               (right-inverse-of _)))            ≡⟨ cong₂ trans
                                                                      (cong-sym _ (right-inverse-of _))
                                                                      (cong-trans _ _ (right-inverse-of _)) ⟩
               trans (sym (cong from (right-inverse-of _)))
                 (trans (cong from (sym (cong (get l) q)))
                    (cong from (right-inverse-of _)))            ≡⟨ cong₂ (λ p r → trans (sym p) (trans (cong from (sym (cong (get l) q))) r))
                                                                      (right-left-lemma _)
                                                                      (right-left-lemma _) ⟩
               trans (sym (left-inverse-of _))
                 (trans (cong from (sym (cong (get l) q)))
                    (left-inverse-of _))                         ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                   (trans eq (left-inverse-of _))) $
                                                                    cong-sym _ (cong (get l) q) ⟩
               trans (sym (left-inverse-of _))
                 (trans (sym (cong from (cong (get l) q)))
                    (left-inverse-of _))                         ≡⟨ cong (λ eq → trans (sym (left-inverse-of _))
                                                                                   (trans (sym eq) (left-inverse-of _))) $
                                                                    cong-∘ _ _ q ⟩
               trans (sym (left-inverse-of _))
                 (trans (sym (cong (from ⊚ get l) q))
                    (left-inverse-of _))                         ≡⟨ cong (λ g → trans (sym (g _))
                                                                                  (trans (sym (cong (from ⊚ get l) q)) (g _))) $ sym $
                                                                    _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext)
                                                                      left-inverse-of ⟩∎
               trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) _))
                 (trans (sym (cong (from ⊚ get l) q))
                    (ext⁻¹ (⟨ext⟩ left-inverse-of) _))           ∎

             f = from ⊚ get l
         in
         set-set (l⁻¹ ∘ l) a a₁ a₂                                     ≡⟨⟩

         trans (set-set l a (get l a₁) (get l a₂))
           (cong from
              (trans (cong (λ _ → get l a₂)
                        (right-inverse-of (get l a₁)))
                 (set-set l⁻¹ (get l a) a₁ a₂)))                       ≡⟨ cong (λ eq → trans (set-set l a (get l a₁) _)
                                                                                         (cong from (trans eq (set-set l⁻¹ (get l a) a₁ _)))) $
                                                                          cong-const (right-inverse-of (get l a₁)) ⟩
         trans (set-set l a (get l a₁) (get l a₂))
           (cong from (trans (refl _) (set-set l⁻¹ (get l a) a₁ a₂)))  ≡⟨ cong (λ eq → trans (set-set l a (get l a₁) _) (cong from eq)) $
                                                                          trans-reflˡ (set-set l⁻¹ (get l a) a₁ _) ⟩
         trans (set-set l a (get l a₁) (get l a₂))
           (cong from (set-set l⁻¹ (get l a) a₁ a₂))                   ≡⟨⟩

         trans (set-set l a (get l a₁) (get l a₂))
           (cong from
              (trans (sym (right-inverse-of _))
                 (trans (sym (cong (get l)
                                (set-set l (from (get l a))
                                   (get l a₁) (get l a₂))))
                    (right-inverse-of _))))                            ≡⟨ cong (λ a′ → trans q
                                                                                         (cong from
                                                                                            (trans (sym (right-inverse-of _))
                                                                                               (trans (sym (cong (get l)
                                                                                                              (set-set l a′ (get l a₁) (get l a₂))))
                                                                                                  (right-inverse-of _))))) $
                                                                          left-inverse-of _ ⟩
         trans q
           (cong from
              (trans (sym (right-inverse-of _))
                 (trans (sym (cong (get l) q))
                    (right-inverse-of _))))                            ≡⟨ cong (trans q) lemma ⟩

         trans q
           (trans (sym (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂)))
              (trans (sym (cong f q))
                 (ext⁻¹ (⟨ext⟩ left-inverse-of) (f a₂))))              ≡⟨ elim₁
                                                                            (λ {f} (p : f ≡ P.id) →
                                                                               (q : f a₂ ≡ f a₂) →
                                                                               trans q
                                                                                 (trans (sym (ext⁻¹ p (f a₂)))
                                                                                    (trans (sym (cong f q))
                                                                                       (ext⁻¹ p (f a₂)))) ≡
                                                                               refl _)
                                                                          (λ q →
             trans q
               (trans (sym (ext⁻¹ (refl P.id) a₂))
                  (trans (sym (cong P.id q))
                     (ext⁻¹ (refl P.id) a₂)))                                ≡⟨ cong (λ eq → trans q (trans (sym eq)
                                                                                                        (trans (sym (cong P.id q)) eq))) $
                                                                                ext⁻¹-refl _ ⟩
             trans q (trans (sym (refl _))
                        (trans (sym (cong P.id q)) (refl _)))                ≡⟨ cong₂ (λ p r → trans q (trans p r))
                                                                                  sym-refl
                                                                                  (trans-reflʳ _) ⟩

             trans q (trans (refl _) (sym (cong P.id q)))                    ≡⟨ cong (trans q) $ trans-reflˡ (sym (cong P.id q)) ⟩

             trans q (sym (cong P.id q))                                     ≡⟨ cong (λ eq → trans q (sym eq)) $ sym $ cong-id q ⟩

             trans q (sym q)                                                 ≡⟨ trans-symʳ q ⟩∎

             refl _                                                          ∎)
                                                                          (⟨ext⟩ left-inverse-of)
                                                                          q ⟩

         refl _                                                        ∎)
    )

-- There is an equivalence between "l is bi-invertible" and "the
-- getter of l is an equivalence".

Is-bi-invertible≃Is-equivalence-get :
  (l : Lens A B) →
  Is-bi-invertible l ≃ Is-equivalence (Lens.get l)
Is-bi-invertible≃Is-equivalence-get l = Eq.⇔→≃
  (BM.Is-bi-invertible-propositional l)
  (Eq.propositional ext _)
  (Is-bi-invertible→Is-equivalence-get l)
  (Is-equivalence-get→Is-bi-invertible l)

------------------------------------------------------------------------
-- A category

-- Lenses between sets with the same universe level form a
-- precategory.

precategory : Precategory (lsuc a) a
precategory {a = a} = record
  { precategory =
      SET a
    , (λ (A , A-set) (B , _) →
           Lens A B
         , lens-preserves-h-level-of-domain 1 A-set)
    , id
    , _∘_
    , left-identity _
    , right-identity _
    , (λ {_ _ _ _ l₁ l₂ l₃} → associativity l₃ l₂ l₁)
  }
  where
  open Lens-combinators

-- Lenses between sets with the same universe level form a
-- category (assuming univalence).

category :
  Univalence a →
  Category (lsuc a) a
category {a = a} univ =
  C.precategory-with-SET-to-category
    ext
    (λ _ _ → univ)
    (proj₂ Pre.precategory)
    (λ (_ , A-set) _ → ≃≃≅ A-set)
    (λ (_ , A-set) → ≃≃≅-id≡id A-set)
  where
  module Pre = C.Precategory precategory

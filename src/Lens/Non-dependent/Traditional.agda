------------------------------------------------------------------------
-- Traditional non-dependent lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Traditional
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bij using (_↔_)
open import Circle eq as Circle using (𝕊¹)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣)
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)

private
  variable
    a b c p         : Level
    A B             : Type a
    u v x₁ x₂ y₁ y₂ : A

------------------------------------------------------------------------
-- Traditional lenses

-- Lenses.

record Lens (A : Type a) (B : Type b) : Type (a ⊔ b) where
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

-- Lens A B is isomorphic to a nested Σ-type.

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

private
  variable
    l₁ l₂ : Lens A B

------------------------------------------------------------------------
-- Somewhat coherent lenses

-- Traditional lenses that satisfy some extra coherence properties.

record Coherent-lens (A : Type a) (B : Type b) : Type (a ⊔ b) where
  field
    lens : Lens A B

  open Lens lens public

  field
    get-set-get : ∀ a → cong get (set-get a) ≡ get-set a (get a)
    get-set-set :
      ∀ a b₁ b₂ →
      cong get (set-set a b₁ b₂) ≡
      trans (get-set (set a b₁) b₂) (sym (get-set a b₂))

instance

  -- Somewhat coherent lenses have getters and setters.

  coherent-has-getter-and-setter :
    Has-getter-and-setter (Coherent-lens {a = a} {b = b})
  coherent-has-getter-and-setter = record
    { get = Coherent-lens.get
    ; set = Coherent-lens.set
    }

-- Coherent-lens A B is equivalent to a nested Σ-type.

Coherent-lens-as-Σ :
  Coherent-lens A B ≃
  ∃ λ (l : Lens A B) →
    let open Lens l in
    (∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
    (∀ a b₁ b₂ →
     cong get (set-set a b₁ b₂) ≡
     trans (get-set (set a b₁) b₂) (sym (get-set a b₂)))
Coherent-lens-as-Σ = Eq.↔→≃
  (λ l → lens l , get-set-get l , get-set-set l)
  (λ (l , get-set-get , get-set-set) → record
     { lens        = l
     ; get-set-get = get-set-get
     ; get-set-set = get-set-set
     })
  refl
  refl
  where
  open Coherent-lens

------------------------------------------------------------------------
-- Some lemmas

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
  Lens A B                                                               ↝⟨ Lens-as-Σ ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a b → get (set a b) ≡ b) ×
     (∀ a → set a (get a) ≡ a) ×
     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                             drop-⊤-left-× λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                             Π-closure ext 0 λ _ →
                                                                             Π-closure ext 0 λ _ →
                                                                             +⇒≡ B-prop) ⟩
  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a → set a (get a) ≡ a) ×
     (∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂))                         ↝⟨ (∃-cong λ get → ∃-cong λ set → ∃-cong λ _ →
                                                                             ∀-cong ext λ a → ∀-cong ext λ b₁ → ∀-cong ext λ b₂ →
                                                                               ≡⇒↝ _ (
       (set (set a b₁)                         b₂ ≡ set a b₂)                    ≡⟨ cong (λ b → set (set a b) b₂ ≡ _) (B-prop _ _) ⟩
       (set (set a (get a))                    b₂ ≡ set a b₂)                    ≡⟨ cong (λ b → set (set a (get a)) b ≡ _) (B-prop _ _) ⟩
       (set (set a (get a)) (get (set a (get a))) ≡ set a b₂)                    ≡⟨ cong (λ b → _ ≡ set a b) (B-prop _ _) ⟩∎
       (set (set a (get a)) (get (set a (get a))) ≡ set a (get a))               ∎)) ⟩

  (∃ λ (get : A → B) →
   ∃ λ (set : A → B → A) →
     (∀ a → set a (get a) ≡ a) ×
     (∀ a → B → B →
        set (set a (get a)) (get (set a (get a))) ≡
        set a (get a)))                                                  ↝⟨ (∃-cong λ get → Σ-cong (A→B→A↔A→A get) λ _ → F.id) ⟩

  ((A → B) ×
   ∃ λ (f : A → A) →
     (∀ a → f a ≡ a) ×
     (∀ a → B → B → f (f a) ≡ f a))                                      ↝⟨ (∃-cong λ get → ∃-cong λ _ → ∃-cong λ _ →
                                                                             ∀-cong ext λ a →
                                                                             drop-⊤-left-Π ext (B↔⊤ (get a)) F.∘
                                                                             drop-⊤-left-Π ext (B↔⊤ (get a))) ⟩

  ((A → B) × ∃ λ (f : A → A) → (∀ a → f a ≡ a) × (∀ a → f (f a) ≡ f a))  ↝⟨ (∃-cong λ _ → ∃-cong λ f → ∃-cong λ f≡id →
                                                                             ∀-cong ext λ a →
                                                                             ≡⇒↝ _ (cong₂ _≡_ (trans (f≡id (f a)) (f≡id a)) (f≡id a))) ⟩

  ((A → B) × ∃ λ (f : A → A) → (∀ a → f a ≡ a) × (∀ a → a ≡ a))          ↝⟨ (∃-cong λ _ →
                                                                             Σ-assoc F.∘
                                                                             (∃-cong λ _ →
                                                                              Σ-cong (Eq.extensionality-isomorphism ext) λ _ → F.id)) ⟩

  (A → B) × (∃ λ (f : A → A) → f ≡ id) × (∀ a → a ≡ a)                   ↝⟨ (∃-cong λ _ → drop-⊤-left-× λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                             singleton-contractible _) ⟩□
  (A → B) × (∀ a → a ≡ a)                                                □
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

-- See also lens-from-⊥≃⊤ and lens-from-⊤≃codomain-contractible below.

------------------------------------------------------------------------
-- Some lens results related to h-levels

-- If the domain of a lens is inhabited and has h-level n,
-- then the codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited {A = A} {B = B} n l a =
  H-level n A  ↝⟨ H-level.respects-surjection surj n ⟩□
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

-- Lens 𝕊¹ ⊤ is not propositional (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-type-of-refl-propositional.)

¬-lens-to-⊤-propositional :
  Univalence (# 0) →
  ¬ Is-proposition (Lens 𝕊¹ ⊤)
¬-lens-to-⊤-propositional _ =
  Is-proposition (Lens 𝕊¹ ⊤)                 ↝⟨ H-level.respects-surjection (_↔_.surjection lens-to-⊤↔) 1 ⟩
  Is-proposition ((x : 𝕊¹) → x ≡ x)          ↝⟨ H-level-cong _ 1 (Π-cong ext (inverse Bij.↑↔) λ _ → Eq.≃-≡ $ Eq.↔⇒≃ Bij.↑↔) ⟩
  Is-proposition ((x : ↑ lzero 𝕊¹) → x ≡ x)  ↝⟨ proj₂ $ Circle.¬-type-of-refl-propositional ⟩□
  ⊥                                          □

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
        ∀ (C : A → B → Type c) (eq : u ≡ v) {f g} →
        (subst (λ x → ∀ y → C x y) eq f ≡ g)
          ↔
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)
      lemma₁ C eq {f} {g} =
        subst (λ x → ∀ y → C x y) eq f ≡ g              ↔⟨ inverse $ Eq.extensionality-isomorphism ext ⟩
        (∀ y → subst (λ x → ∀ y → C x y) eq f y ≡ g y)  ↝⟨ (∀-cong ext λ y → ≡⇒↝ _ $
                                                            cong (λ x → x ≡ _) (sym $ push-subst-application eq _)) ⟩□
        (∀ y → subst (λ x → C x y) eq (f y) ≡ g y)      □

    lemma₂ :
      (P : A × B → Type p) (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : y₁ ≡ y₂) →
      ∀ {p p′} →
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

    lemma₁ :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a b →
      subst (λ get → get (set l₂ a b) ≡ b) g
        (subst (λ set → get l₁ (set a b) ≡ b) s
           (get-set l₁ a b)) ≡
      trans (sym (cong₂ (λ set get → get (set a b)) s g))
        (get-set l₁ a b)
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

    lemma₂ :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a →
      subst (λ get → set l₂ a (get a) ≡ a) g
        (subst (λ set → set a (get l₁ a) ≡ a) s
           (set-get l₁ a)) ≡
      trans (sym (cong₂ (λ set get → set a (get a)) s g))
        (set-get l₁ a)
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

    lemma :
      (g : get l₁ ≡ get l₂) (s : set l₁ ≡ set l₂) →
      ∀ a b₁ b₂ →
      (subst (λ set → set (set a b₁) b₂ ≡ set a b₂) s
         (set-set l₁ a b₁ b₂) ≡
       set-set l₂ a b₁ b₂) ≡
      (trans (set-set l₁ a b₁ b₂) (cong (λ set → set a b₂) s) ≡
       trans (cong (λ set → set (set a b₁) b₂) s)
         (set-set l₂ a b₁ b₂))
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
         trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ∘ s)))
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
        trans (cong (get l₁ ∘ (_$ b)) (ext⁻¹ s a))
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
        ⟨ext⟩ (⟨ext⟩ ∘ ext⁻¹ ∘ ext⁻¹ s)                                        ∎)) ⟩□

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
          trans (cong (λ set → set (set a b₁) b₂) (⟨ext⟩ (⟨ext⟩ ∘ s)))
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
-- More isomorphisms/equivalences related to lenses

-- Lens ⊤ B is equivalent to Contractible B.

lens-from-⊤≃codomain-contractible :
  Lens ⊤ B ≃ Contractible B
lens-from-⊤≃codomain-contractible = Eq.⇔→≃
  (lens-preserves-h-level-of-domain 0 (mono₁ 0 ⊤-contractible))
  (H-level-propositional ext 0)
  (λ l → contractible-to-contractible l ⊤-contractible)
  (λ (b , irrB) → record
     { get     = λ _ → b
     ; get-set = λ _ → irrB
     ; set-get = refl
     ; set-set = λ _ _ _ → refl _
     })

-- Lens ⊥ B is equivalent to the unit type.

lens-from-⊥≃⊤ : Lens (⊥ {ℓ = a}) B ≃ ⊤
lens-from-⊥≃⊤ = Eq.⇔→≃
  (lens-preserves-h-level-of-domain 0 ⊥-propositional)
  (mono₁ 0 ⊤-contractible)
  _
  (λ _ → record
     { get = ⊥-elim
     ; set = ⊥-elim
     ; get-set = λ a → ⊥-elim a
     ; set-get = λ a → ⊥-elim a
     ; set-set = λ a → ⊥-elim a
     })

-- If A is a set and there is a lens from A to B, then A is equivalent
-- to the cartesian product of some type (that can be expressed using
-- the setter of l) and B.
--
-- This result is based on Theorem 2.3.9 from "Lenses and View Update
-- Translation" by Pierce and Schmitt.

≃Σ∥set⁻¹∥× :
  Is-set A →
  (l : Lens A B) →
  A ≃ ((∃ λ (f : B → A) → ∥ Lens.set l ⁻¹ f ∥) × B)
≃Σ∥set⁻¹∥× {A = A} {B = B} A-set l = Eq.↔→≃
  (λ a → (set a , ∣ a , refl _ ∣) , get a)
  (λ ((f , _) , b) → f b)
  (λ ((f , p) , b) →
     flip (Trunc.rec (×-closure 2
                        (Σ-closure 2
                           (Π-closure ext 2 λ _ → A-set) λ _ →
                           mono₁ 1 Trunc.truncation-is-proposition)
                        (B-set (f b))))
       p λ (a , q) →
     let
       lemma₁ =
         set (f b)      ≡⟨ cong (λ f → set (f b)) $ sym q ⟩
         set (set a b)  ≡⟨ ⟨ext⟩ $ set-set a b ⟩
         set a          ≡⟨ q ⟩∎
         f              ∎

       lemma₂ =
         get (f b)      ≡⟨ cong (λ f → get (f b)) $ sym q ⟩
         get (set a b)  ≡⟨ get-set _ _ ⟩∎
         b              ∎
     in
     (set (f b) , ∣ f b , refl _ ∣) , get (f b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma₁ (Trunc.truncation-is-proposition _ _)) lemma₂ ⟩∎
     (f         , p               ) , b          ∎)
  (λ a →
     set a (get a)  ≡⟨ set-get a ⟩∎
     a              ∎)
  where
  open Lens l

  B-set : A → Is-set B
  B-set a =
    h-level-respects-lens-from-inhabited 2 l a A-set

-- If B is an inhabited set and there is a lens from A to B, then A is
-- equivalent to the cartesian product of some type (that can be
-- expressed using the getter of l) and B.
--
-- This result is based on Corollary 13 from "Algebras and Update
-- Strategies" by Johnson, Rosebrugh and Wood.

≃get⁻¹× :
  Is-set B →
  (b : B)
  (l : Lens A B) →
  A ≃ (Lens.get l ⁻¹ b × B)
≃get⁻¹× {B = B} {A = A} B-set b₀ l = Eq.↔→≃
  (λ a → (set a b₀ , get-set a b₀) , get a)
  (λ ((a , _) , b) → set a b)
  (λ ((a , h) , b) →
     let
       lemma =
         set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
         set a b₀          ≡⟨ cong (set a) (sym h) ⟩
         set a (get a)     ≡⟨ set-get a ⟩∎
         a                 ∎
     in
     (set (set a b) b₀ , get-set (set a b) b₀) , get (set a b)  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma (B-set _ _)) (get-set a b) ⟩∎
     (a                , h                   ) , b              ∎)
  (λ a →
     set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
     set a (get a)           ≡⟨ set-get a ⟩∎
     a                       ∎)
  where
  open Lens l

-- For somewhat coherent lenses the previous result can be proved
-- without the assumption that the codomain is a set.

≃get⁻¹×-coherent :
  (b : B)
  (l : Coherent-lens A B) →
  A ≃ (Coherent-lens.get l ⁻¹ b × B)
≃get⁻¹×-coherent {B = B} {A = A} b₀ l = Eq.↔→≃
  (λ a → (set a b₀ , get-set a b₀) , get a)
  (λ ((a , _) , b) → set a b)
  (λ ((a , h) , b) →
     let
       lemma₁ =
         set (set a b) b₀  ≡⟨ set-set a b b₀ ⟩
         set a b₀          ≡⟨ cong (set a) (sym h) ⟩
         set a (get a)     ≡⟨ set-get a ⟩∎
         a                 ∎

       lemma₂₁ =
         cong get (trans (set-set a b b₀)
                     (trans (cong (set a) (sym h))
                        (set-get a)))               ≡⟨ trans (cong-trans _ _ _) $
                                                       cong (trans _) $
                                                       trans (cong-trans _ _ _) $
                                                       cong (flip trans _) $
                                                       cong-∘ _ _ _ ⟩
         trans (cong get (set-set a b b₀))
           (trans (cong (get ∘ set a) (sym h))
              (cong get (set-get a)))               ≡⟨ cong₂ (λ p q → trans p (trans (cong (get ∘ set a) (sym h)) q))
                                                         (get-set-set _ _ _)
                                                         (get-set-get _) ⟩∎
         trans (trans (get-set (set a b) b₀)
                  (sym (get-set a b₀)))
           (trans (cong (get ∘ set a) (sym h))
              (get-set a (get a)))                  ∎

       lemma₂₂ =
         sym (trans (trans (get-set (set a b) b₀)
                       (sym (get-set a b₀)))
                (trans (cong (get ∘ set a) (sym h))
                   (get-set a (get a))))               ≡⟨ trans (sym-trans _ _) $
                                                          cong₂ trans
                                                            (sym-trans _ _)
                                                            (sym-trans _ _) ⟩
         trans (trans (sym (get-set a (get a)))
                  (sym (cong (get ∘ set a) (sym h))))
           (trans (sym (sym (get-set a b₀)))
              (sym (get-set (set a b) b₀)))            ≡⟨ cong₂ (λ p q → trans (trans (sym (get-set a (get a))) p)
                                                                           (trans q (sym (get-set (set a b) b₀))))
                                                            (trans (cong sym $ cong-sym _ _) $
                                                             sym-sym _)
                                                            (sym-sym _) ⟩
         trans (trans (sym (get-set a (get a)))
                  (cong (get ∘ set a) h))
           (trans (get-set a b₀)
              (sym (get-set (set a b) b₀)))            ≡⟨ trans (sym $ trans-assoc _ _ _) $
                                                          cong (flip trans _) $ trans-assoc _ _ _ ⟩∎
         trans (trans (sym (get-set a (get a)))
                  (trans (cong (get ∘ set a) h)
                     (get-set a b₀)))
           (sym (get-set (set a b) b₀))                ∎

       lemma₂ =
         subst (λ a → get a ≡ b₀)
           (trans (set-set a b b₀)
              (trans (cong (set a) (sym h)) (set-get a)))
           (get-set (set a b) b₀)                            ≡⟨ subst-∘ _ _ _ ⟩

         subst (_≡ b₀)
           (cong get (trans (set-set a b b₀)
                        (trans (cong (set a) (sym h))
                           (set-get a))))
           (get-set (set a b) b₀)                            ≡⟨ subst-trans-sym ⟩

         trans
           (sym (cong get (trans (set-set a b b₀)
                             (trans (cong (set a) (sym h))
                                (set-get a)))))
           (get-set (set a b) b₀)                            ≡⟨ cong (flip (trans ∘ sym) _) lemma₂₁ ⟩

         trans
           (sym (trans (trans (get-set (set a b) b₀)
                          (sym (get-set a b₀)))
                   (trans (cong (get ∘ set a) (sym h))
                      (get-set a (get a)))))
           (get-set (set a b) b₀)                            ≡⟨ cong (flip trans _) lemma₂₂ ⟩

         trans
           (trans (trans (sym (get-set a (get a)))
                     (trans (cong (get ∘ set a) h)
                        (get-set a b₀)))
              (sym (get-set (set a b) b₀)))
           (get-set (set a b) b₀)                            ≡⟨ trans-[trans-sym]- _ _ ⟩

         trans (sym (get-set a (get a)))
           (trans (cong (get ∘ set a) h)
              (get-set a b₀))                                ≡⟨ cong (λ f → trans (sym (f (get a))) (trans (cong (get ∘ set a) h) (f b₀))) $ sym $
                                                                _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) (get-set a) ⟩
         trans (sym (ext⁻¹ (⟨ext⟩ (get-set a)) (get a)))
           (trans (cong (get ∘ set a) h)
              (ext⁻¹ (⟨ext⟩ (get-set a)) b₀))                ≡⟨ elim₁
                                                                  (λ {f} eq →
                                                                     trans (sym (ext⁻¹ eq (get a)))
                                                                       (trans (cong f h) (ext⁻¹ eq b₀)) ≡
                                                                       h)
                                                                  (
             trans (sym (ext⁻¹ (refl id) (get a)))
               (trans (cong id h) (ext⁻¹ (refl id) b₀))            ≡⟨ cong₂ (λ p q → trans p (trans (cong id h) q))
                                                                        (trans (cong sym (ext⁻¹-refl _)) sym-refl)
                                                                        (ext⁻¹-refl _) ⟩

             trans (refl _) (trans (cong id h) (refl _))           ≡⟨ trans-reflˡ _ ⟩

             trans (cong id h) (refl _)                            ≡⟨ trans-reflʳ _ ⟩

             cong id h                                             ≡⟨ sym $ cong-id _ ⟩∎

             h                                                     ∎)
                                                                  _ ⟩∎
         h                                                   ∎
     in
     ((set (set a b) b₀ , get-set (set a b) b₀) , get (set a b))  ≡⟨ cong₂ _,_ (Σ-≡,≡→≡ lemma₁ lemma₂) (get-set a b) ⟩∎
     ((a                , h                   ) , b            )  ∎)
  (λ a →
     set (set a b₀) (get a)  ≡⟨ set-set a b₀ (get a) ⟩
     set a (get a)           ≡⟨ set-get a ⟩∎
     a                       ∎)
  where
  open Coherent-lens l

------------------------------------------------------------------------
-- A conversion function

-- If A is a set, then Lens A B is equivalent to Coherent-lens A B.

≃coherent : Is-set A → Lens A B ≃ Coherent-lens A B
≃coherent {A = A} {B = B} A-set = Eq.↔→≃
  to
  Coherent-lens.lens
  (λ l → let l′ = Coherent-lens.lens l in
                          $⟨ ×-closure 1
                               (Π-closure ext 1 λ a →
                                mono₁ 2 (B-set l′ a))
                               (Π-closure ext 1 λ a →
                                Π-closure ext 1 λ _ →
                                Π-closure ext 1 λ _ →
                                mono₁ 2 (B-set l′ a)) ⟩
     Is-proposition _     ↝⟨ (λ p → cong (l′ ,_) (p _ _)) ⦂ (_ → _) ⟩
     (l′ , _) ≡ (l′ , _)  ↔⟨ Eq.≃-≡ Coherent-lens-as-Σ ⟩□
     to l′ ≡ l            □)
  refl
  where
  B-set : Lens A B → A → Is-set B
  B-set l a =
    h-level-respects-lens-from-inhabited 2 l a A-set

  to : Lens A B → Coherent-lens A B
  to l = record
    { lens        = l
    ; get-set-get = λ a → B-set l a _ _
    ; get-set-set = λ a _ _ → B-set l a _ _
    }

-- The conversion preserves getters and setters.

≃coherent-preserves-getters-and-setters :
  {A : Type a}
  (s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_≃_.logical-equivalence (≃coherent s))
≃coherent-preserves-getters-and-setters _ =
    (λ _ → refl _ , refl _)
  , (λ _ → refl _ , refl _)

------------------------------------------------------------------------
-- Some existence results

-- There is, in general, no lens for the first projection from a
-- Σ-type.

no-first-projection-lens :
  ¬ Lens (∃ λ (b : Bool) → b ≡ true) Bool
no-first-projection-lens =
  Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

-- There are two lenses with equal setters that are not equal
-- (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.not-refl≢refl.)

equal-setters-but-not-equal :
  Univalence lzero →
  ∃ λ (A : Type) →
  ∃ λ (B : Type) →
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
  l₁′ = _≃_.from lemma Circle.not-refl

  l₂′ : Lens 𝕊¹ ⊤
  l₂′ = _≃_.from lemma refl

  set-l₁′≡set-l₂′ : set l₁′ ≡ set l₂′
  set-l₁′≡set-l₂′ = refl _

  l₁′≢l₂′ : l₁′ ≢ l₂′
  l₁′≢l₂′ =
    l₁′ ≡ l₂′               ↔⟨ Eq.≃-≡ (inverse lemma) {x = Circle.not-refl} {y = refl} ⟩
    Circle.not-refl ≡ refl  ↝⟨ Circle.not-refl≢refl ⟩□
    ⊥                       □

-- A lens which is used in some counterexamples below.

bad : Lens 𝕊¹ 𝕊¹
bad = record
  { get     = id
  ; set     = const id
  ; get-set = λ _ → Circle.not-refl
  ; set-get = refl
  ; set-set = λ _ _ → Circle.not-refl
  }

-- The lens bad has a getter which is an equivalence, but it does not
-- satisfy either of the coherence laws that Coherent-lens lenses must
-- satisfy (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.not-refl≢refl.)

getter-equivalence-but-not-coherent :
  Univalence lzero →
  let open Lens bad in
  Is-equivalence get ×
  ¬ (∀ a → cong get (set-get a) ≡ get-set a (get a)) ×
  ¬ (∀ a₁ a₂ a₃ →
     cong get (set-set a₁ a₂ a₃) ≡
     trans (get-set (set a₁ a₂) a₃) (sym (get-set a₁ a₃)))
getter-equivalence-but-not-coherent _ =
    _≃_.is-equivalence F.id
  , (((x : 𝕊¹) → cong get (set-get x) ≡ get-set x (get x))  ↔⟨⟩
     ((x : 𝕊¹) → cong id (refl _) ≡ Circle.not-refl x)      ↝⟨ trans (cong-id _) ∘_ ⟩
     ((x : 𝕊¹) → refl x ≡ Circle.not-refl x)                ↔⟨ Eq.extensionality-isomorphism ext ⟩
     refl ≡ Circle.not-refl                                 ↝⟨ Circle.not-refl≢refl ∘ sym ⟩□
     ⊥                                                      □)
  , (((x y z : 𝕊¹) →
      cong get (set-set x y z) ≡
      trans (get-set (set x y) z) (sym (get-set x z)))      ↔⟨⟩

     ((x y z : 𝕊¹) →
      cong id (Circle.not-refl z) ≡
      trans (Circle.not-refl z) (sym (Circle.not-refl z)))  ↝⟨ (λ hyp → hyp Circle.base Circle.base) ⟩

     ((x : 𝕊¹) →
      cong id (Circle.not-refl x) ≡
      trans (Circle.not-refl x) (sym (Circle.not-refl x)))  ↝⟨ (∀-cong _ λ _ → ≡⇒↝ _ $ cong₂ _≡_
                                                                  (sym $ cong-id _)
                                                                  (trans-symʳ _)) ⟩

     ((x : 𝕊¹) → Circle.not-refl x ≡ refl x)                ↔⟨ Eq.extensionality-isomorphism ext ⟩

     Circle.not-refl ≡ refl                                 ↝⟨ Circle.not-refl≢refl ⟩□

     ⊥                                                      □)
  where
  open Lens bad

------------------------------------------------------------------------
-- Higher lenses
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Lens.Non-dependent.Higher
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bij using (_↔_)
import Bool equality-with-J as Bool
open import Circle eq as Circle using (𝕊¹)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
import Equivalence.Half-adjoint equality-with-J as HA
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
import Nat equality-with-J as Nat
open import Preimage equality-with-J as Preimage using (_⁻¹_)
open import Quotient eq
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Lens.Non-dependent eq as Non-dependent
  hiding (no-first-projection-lens)
import Lens.Non-dependent.Traditional eq as Traditional

private
  variable
    a b c r         : Level
    A A₁ A₂ B B₁ B₂ : Type a

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

record Lens (A : Type a) (B : Type b) : Type (lsuc (a ⊔ b)) where
  constructor ⟨_,_,_⟩
  pattern
  no-eta-equality
  field
    -- Remainder type.
    R : Type (a ⊔ b)

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

  -- The setter leaves the remainder unchanged.

  remainder-set : ∀ a b → remainder (set a b) ≡ remainder a
  remainder-set a b =
    proj₁ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₁ (_≃_.right-inverse-of equiv (remainder a , b)) ⟩∎
    remainder a                                              ∎

  -- Lens laws.

  get-set : ∀ a b → get (set a b) ≡ b
  get-set a b =
    proj₂ (_≃_.to equiv (_≃_.from equiv (remainder a , b)))  ≡⟨ cong proj₂ (_≃_.right-inverse-of equiv (remainder a , b)) ⟩∎
    proj₂ (remainder a , b)                                  ∎

  set-get : ∀ a → set a (get a) ≡ a
  set-get a =
    _≃_.from equiv (_≃_.to equiv a)  ≡⟨ _≃_.left-inverse-of equiv a ⟩∎
    a                                ∎

  set-set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂
  set-set a b₁ b₂ =
    _≃_.from equiv (remainder (set a b₁) , b₂)  ≡⟨ cong (λ r → _≃_.from equiv (r , b₂)) (remainder-set a b₁) ⟩∎
    _≃_.from equiv (remainder a          , b₂)  ∎

  -- The remainder function is surjective.

  remainder-surjective : Surjective remainder
  remainder-surjective r =
    ∥∥-map (λ b → _≃_.from equiv (r , b)
                , (remainder (_≃_.from equiv (r , b))             ≡⟨⟩
                   proj₁ (_≃_.to equiv (_≃_.from equiv (r , b)))  ≡⟨ cong proj₁ (_≃_.right-inverse-of equiv (r , b)) ⟩∎
                   r                                              ∎))
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

  -- The following two coherence laws, which do not necessarily hold
  -- for traditional lenses (see
  -- Traditional.getter-equivalence-but-not-coherent), hold
  -- unconditionally for higher lenses.

  get-set-get : ∀ a → cong get (set-get a) ≡ get-set a (get a)
  get-set-get a =
    cong get (set-get a)                                            ≡⟨⟩
    cong (proj₂ ∘ _≃_.to equiv) (_≃_.left-inverse-of equiv a)       ≡⟨ sym $ cong-∘ _ _ (_≃_.left-inverse-of equiv _) ⟩
    cong proj₂ (cong (_≃_.to equiv) (_≃_.left-inverse-of equiv a))  ≡⟨ cong (cong proj₂) $ _≃_.left-right-lemma equiv _ ⟩
    cong proj₂ (_≃_.right-inverse-of equiv (_≃_.to equiv a))        ≡⟨⟩
    get-set a (get a)                                               ∎

  get-set-set :
    ∀ a b₁ b₂ →
    cong get (set-set a b₁ b₂) ≡
    trans (get-set (set a b₁) b₂) (sym (get-set a b₂))
  get-set-set a b₁ b₂ =
    cong get (set-set a b₁ b₂)                                            ≡⟨⟩

    cong get (cong (λ r → _≃_.from equiv (r , b₂)) (remainder-set a b₁))  ≡⟨ elim₁
                                                                               (λ {r} eq →
                                                                                  cong get (cong (λ r → _≃_.from equiv (r , b₂)) eq) ≡
                                                                                  trans (cong proj₂ (_≃_.right-inverse-of equiv (r , b₂)))
                                                                                    (sym (get-set a b₂)))
                                                                               (
        cong get (cong (λ r → _≃_.from equiv (r , b₂))
                    (refl (remainder a)))                                       ≡⟨ trans (cong (cong get) $ cong-refl _) $
                                                                                   cong-refl _ ⟩

        refl (get (set a b₂))                                                   ≡⟨ sym $ trans-symʳ _ ⟩

        trans (get-set a b₂) (sym (get-set a b₂))                               ≡⟨⟩

        trans (cong proj₂
                 (_≃_.right-inverse-of equiv (remainder a , b₂)))
          (sym (get-set a b₂))                                                  ∎)
                                                                               (remainder-set a b₁) ⟩
    trans (cong proj₂
             (_≃_.right-inverse-of equiv (remainder (set a b₁) , b₂)))
      (sym (get-set a b₂))                                                ≡⟨⟩

    trans (get-set (set a b₁) b₂) (sym (get-set a b₂))                    ∎

  -- A somewhat coherent lens.

  coherent-lens : Traditional.Coherent-lens A B
  coherent-lens = record
    { lens        = traditional-lens
    ; get-set-get = get-set-get
    ; get-set-set = get-set-set
    }

instance

  -- Higher lenses have getters and setters.

  has-getter-and-setter :
    Has-getter-and-setter (Lens {a = a} {b = b})
  has-getter-and-setter = record
    { get = Lens.get
    ; set = Lens.set
    }

------------------------------------------------------------------------
-- Simple definitions related to lenses

-- An η-law for lenses.

η :
  (l : Lens A B) →
  ⟨ Lens.R l , Lens.equiv l , Lens.inhabited l ⟩ ≡ l
η ⟨ _ , _ , _ ⟩ = refl _

-- Lens can be expressed as a nested Σ-type.

Lens-as-Σ :
  {A : Type a} {B : Type b} →
  Lens A B ≃
  ∃ λ (R : Type (a ⊔ b)) →
    (A ≃ (R × B)) ×
    (R → ∥ B ∥)
Lens-as-Σ = Eq.↔→≃
  (λ l → R l , equiv l , inhabited l)
  (λ (R , equiv , inhabited) → record
     { R         = R
     ; equiv     = equiv
     ; inhabited = inhabited
     })
  refl
  η
  where
  open Lens

-- An equality rearrangement lemma.

left-inverse-of-Lens-as-Σ :
  (l : Lens A B) →
  _≃_.left-inverse-of Lens-as-Σ l ≡ η l
left-inverse-of-Lens-as-Σ l@(⟨ _ , _ , _ ⟩) =
  _≃_.left-inverse-of Lens-as-Σ l                          ≡⟨⟩

  _≃_.left-inverse-of Lens-as-Σ
    (_≃_.from Lens-as-Σ (_≃_.to Lens-as-Σ l))              ≡⟨ sym $ _≃_.right-left-lemma Lens-as-Σ _ ⟩

  cong (_≃_.from Lens-as-Σ)
    (_≃_.right-inverse-of Lens-as-Σ (_≃_.to Lens-as-Σ l))  ≡⟨⟩

  cong (_≃_.from Lens-as-Σ) (refl _)                       ≡⟨ cong-refl _ ⟩∎

  refl _                                                   ∎

-- Isomorphisms can be converted into lenses.

isomorphism-to-lens :
  {A : Type a} {B : Type b} {R : Type (a ⊔ b)} →
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
  {A : Type a} {B : Type b} →
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
  {A B : Type a} →
  A ≃ B → Lens A B
≃→lens′ {a = a} {A = A} {B = B} A≃B = record
  { R         = ∥ B ∥
  ; equiv     = A          ↝⟨ A≃B ⟩
                B          ↝⟨ inverse ∥∥×≃ ⟩□
                ∥ B ∥ × B  □
  ; inhabited = id
  }

------------------------------------------------------------------------
-- Some results related to the remainder type

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
           trans (cong (get ∘ set a) (sym get-a≡b))
             (cong proj₂ (cong (_≃_.to equiv)
                            (_≃_.left-inverse-of equiv _)))              ≡⟨ cong₂ (λ p q → trans p (cong proj₂ q))
                                                                              (cong-sym _ get-a≡b)
                                                                              (_≃_.left-right-lemma equiv _) ⟩
           trans (sym (cong (get ∘ set a) get-a≡b))
             (cong proj₂ (_≃_.right-inverse-of equiv _))                 ≡⟨ sym $ sym-sym _ ⟩

           sym (sym (trans (sym (cong (get ∘ set a) get-a≡b))
                       (cong proj₂ (_≃_.right-inverse-of equiv _))))     ≡⟨ cong sym $
                                                                            sym-trans _ (cong proj₂ (_≃_.right-inverse-of equiv _)) ⟩
           sym (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                  (sym (sym (cong (get ∘ set a) get-a≡b))))              ≡⟨ cong (λ eq → sym (trans (sym (cong proj₂
                                                                                                            (_≃_.right-inverse-of equiv _)))
                                                                                                eq)) $
                                                                            sym-sym (cong (get ∘ set a) get-a≡b) ⟩∎
           sym (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                  (cong (get ∘ set a) get-a≡b))                          ∎
     in
     Σ-≡,≡→≡
       (_≃_.from equiv (remainder a , b)  ≡⟨⟩
        set a b                           ≡⟨ cong (set a) (sym get-a≡b) ⟩
        set a (get a)                     ≡⟨ set-get a ⟩∎
        a                                 ∎)
       (subst (λ a → get a ≡ b)
          (trans (cong (set a) (sym get-a≡b)) (set-get a))
          (cong proj₂ $ _≃_.right-inverse-of equiv (remainder a , b))    ≡⟨⟩

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
                  (cong (get ∘ set a) get-a≡b)))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ subst-trans (trans _ (cong (get ∘ set a) get-a≡b)) ⟩

        trans
          (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
             (cong (get ∘ set a) get-a≡b))
          (cong proj₂ $ _≃_.right-inverse-of equiv _)                    ≡⟨ elim¹
                                                                              (λ eq → trans
                                                                                        (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                                                                                           (cong (get ∘ set a) eq))
                                                                                        (cong proj₂ $ _≃_.right-inverse-of equiv _) ≡
                                                                                      eq)
                                                                              (
            trans
              (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                 (cong (get ∘ set a) (refl _)))
              (cong proj₂ $ _≃_.right-inverse-of equiv _)                      ≡⟨ cong (λ eq → trans (trans (sym (cong proj₂
                                                                                                                    (_≃_.right-inverse-of equiv _)))
                                                                                                        eq)
                                                                                                 (cong proj₂ $ _≃_.right-inverse-of equiv _)) $
                                                                                  cong-refl _ ⟩
            trans
              (trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
                 (refl _))
              (cong proj₂ $ _≃_.right-inverse-of equiv _)                      ≡⟨ cong (flip trans _) $ trans-reflʳ _ ⟩

            trans (sym (cong proj₂ (_≃_.right-inverse-of equiv _)))
              (cong proj₂ $ _≃_.right-inverse-of equiv _)                      ≡⟨ trans-symˡ (cong proj₂ (_≃_.right-inverse-of equiv _)) ⟩∎

            refl _                                                             ∎)
                                                                              get-a≡b ⟩∎
        get-a≡b                                                          ∎))
  (λ r →
     remainder (_≃_.from equiv (r , b))             ≡⟨⟩
     proj₁ (_≃_.to equiv (_≃_.from equiv (r , b)))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of equiv _ ⟩∎
     r                                              ∎)
  where
  open Lens l

-- A corollary: Lens.get l ⁻¹_ is constant (up to equivalence).
--
-- Paolo Capriotti discusses this kind of property
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

get⁻¹-constant :
  (l : Lens A B) (b₁ b₂ : B) → Lens.get l ⁻¹ b₁ ≃ Lens.get l ⁻¹ b₂
get⁻¹-constant l b₁ b₂ =
  Lens.get l ⁻¹ b₁  ↝⟨ inverse $ remainder≃get⁻¹ l b₁ ⟩
  Lens.R l          ↝⟨ remainder≃get⁻¹ l b₂ ⟩□
  Lens.get l ⁻¹ b₂  □

-- The two directions of get⁻¹-constant.

get⁻¹-const :
  (l : Lens A B) (b₁ b₂ : B) →
  Lens.get l ⁻¹ b₁ → Lens.get l ⁻¹ b₂
get⁻¹-const l b₁ b₂ = _≃_.to (get⁻¹-constant l b₁ b₂)

get⁻¹-const⁻¹ :
  (l : Lens A B) (b₁ b₂ : B) →
  Lens.get l ⁻¹ b₂ → Lens.get l ⁻¹ b₁
get⁻¹-const⁻¹ l b₁ b₂ = _≃_.from (get⁻¹-constant l b₁ b₂)

-- The set function can be expressed using get⁻¹-const and get.
--
-- Paolo Capriotti defines set in a similar way
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

set-in-terms-of-get⁻¹-const :
  (l : Lens A B) →
  Lens.set l ≡
  λ a b → proj₁ (get⁻¹-const l (Lens.get l a) b (a , refl _))
set-in-terms-of-get⁻¹-const l = refl _

-- The remainder function can be expressed using remainder≃get⁻¹ and
-- get.

remainder-in-terms-of-remainder≃get⁻¹ :
  (l : Lens A B) →
  Lens.remainder l ≡
  λ a → _≃_.from (remainder≃get⁻¹ l (Lens.get l a)) (a , refl _)
remainder-in-terms-of-remainder≃get⁻¹ l = refl _

-- The functions get⁻¹-const and get⁻¹-const⁻¹ satisfy some coherence
-- properties.
--
-- The first and third properties are discussed by Paolo Capriotti
-- (http://homotopytypetheory.org/2014/04/29/higher-lenses/).

get⁻¹-const-∘ :
  (l : Lens A B) (b₁ b₂ b₃ : B) (p : Lens.get l ⁻¹ b₁) →
  get⁻¹-const l b₂ b₃ (get⁻¹-const l b₁ b₂ p) ≡
  get⁻¹-const l b₁ b₃ p
get⁻¹-const-∘ l _ b₂ b₃ p =
  from (r₂ , b₃) , cong proj₂ (right-inverse-of (r₂ , b₃))  ≡⟨ cong (λ r → from (r , b₃) , cong proj₂ (right-inverse-of (r , b₃))) $
                                                               cong proj₁ $ right-inverse-of _ ⟩∎
  from (r₁ , b₃) , cong proj₂ (right-inverse-of (r₁ , b₃))  ∎
  where
  open Lens l
  open _≃_ equiv

  r₁ r₂ : R
  r₁ = proj₁ (to (proj₁ p))
  r₂ = proj₁ (to (from (r₁ , b₂)))

get⁻¹-const-inverse :
  (l : Lens A B) (b₁ b₂ : B) (p : Lens.get l ⁻¹ b₁) →
  get⁻¹-const l b₁ b₂ p ≡ get⁻¹-const⁻¹ l b₂ b₁ p
get⁻¹-const-inverse _ _ _ _ = refl _

get⁻¹-const-id :
  (l : Lens A B) (b : B) (p : Lens.get l ⁻¹ b) →
  get⁻¹-const l b b p ≡ p
get⁻¹-const-id l b p =
  get⁻¹-const l b b p                        ≡⟨ sym $ get⁻¹-const-∘ l b _ _ p ⟩
  get⁻¹-const l b b (get⁻¹-const l b b p)    ≡⟨⟩
  get⁻¹-const⁻¹ l b b (get⁻¹-const l b b p)  ≡⟨ _≃_.left-inverse-of (get⁻¹-constant l b b) _ ⟩∎
  p                                          ∎

-- Another kind of coherence property does not hold for get⁻¹-const.
--
-- This kind of property came up in a discussion with Andrea Vezzosi.

get⁻¹-const-not-coherent :
  ¬ ({A B : Type} (l : Lens A B) (b₁ b₂ : B)
     (f : ∀ b → Lens.get l ⁻¹ b) →
     get⁻¹-const l b₁ b₂ (f b₁) ≡ f b₂)
get⁻¹-const-not-coherent =
  ({A B : Type} (l : Lens A B) (b₁ b₂ : B) (f : ∀ b → Lens.get l ⁻¹ b) →
   get⁻¹-const l b₁ b₂ (f b₁) ≡ f b₂)                                     ↝⟨ (λ hyp → hyp l true false f) ⟩

  get⁻¹-const l true false (f true) ≡ f false                             ↝⟨ cong (proj₁ ∘ proj₁) ⟩

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
  f b = (b , b) , refl _

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

------------------------------------------------------------------------
-- Equality characterisations for lenses

-- An equality characterisation lemma.

equality-characterisation₀ :
  let open Lens in
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≡ R l₂) →
    subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂
equality-characterisation₀ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                     ↔⟨ inverse $ Eq.≃-≡ Lens-as-Σ ⟩

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
     equiv l₂)                                                ↔⟨ (∃-cong λ _ → ≡⇒≃ $ cong (λ (eq , _) → eq ≡ _) $
                                                                  push-subst-, _ _) ⟩□
  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)       □
  where
  open Lens

  l₁′ = _≃_.to Lens-as-Σ l₁
  l₂′ = _≃_.to Lens-as-Σ l₂

-- A "computation" rule.

from-equality-characterisation₀ :
  let open Lens in
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
  (b : Block "equality-characterisation") →
  {p : R l₁ ≡ R l₂}
  {q : subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂} →
  _↔_.from (equality-characterisation₀ {l₁ = l₁} {l₂ = l₂} b) (p , q) ≡
  trans (sym (η l₁))
    (trans (cong (_≃_.from Lens-as-Σ)
              (Σ-≡,≡→≡ p
                 (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                  (sym (push-subst-, _ _)))
                             q)
                    (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                                 truncation-is-proposition))))))
       (η l₂))
from-equality-characterisation₀ ⊠ {p = p} {q = q} =
  trans (sym (_≃_.left-inverse-of Lens-as-Σ _))
    (trans (cong (_≃_.from Lens-as-Σ)
              (Σ-≡,≡→≡ p
                 (_↔_.to (ignore-propositional-component
                            (Π-closure ext 1 λ _ →
                             truncation-is-proposition))
                    (_≃_.from (≡⇒≃ (cong (λ (eq , _) → eq ≡ _)
                                      (push-subst-, _ _)))
                       q))))
       (_≃_.left-inverse-of Lens-as-Σ _))                         ≡⟨ cong (λ eq →
                                                                             trans (sym (_≃_.left-inverse-of Lens-as-Σ _))
                                                                               (trans (cong (_≃_.from Lens-as-Σ)
                                                                                         (Σ-≡,≡→≡ p
                                                                                            (_↔_.to (ignore-propositional-component
                                                                                                       (Π-closure ext 1 λ _ →
                                                                                                        truncation-is-proposition))
                                                                                               (_≃_.to eq q))))
                                                                                  (_≃_.left-inverse-of Lens-as-Σ _))) $
                                                                     trans (sym $ ≡⇒≃-sym ext _) $
                                                                     cong ≡⇒≃ $ sym $ cong-sym _ _ ⟩
  trans (sym (_≃_.left-inverse-of Lens-as-Σ _))
    (trans (cong (_≃_.from Lens-as-Σ)
              (Σ-≡,≡→≡ p
                 (_↔_.to (ignore-propositional-component
                            (Π-closure ext 1 λ _ →
                             truncation-is-proposition))
                    (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                            (sym (push-subst-, _ _)))
                       q))))
       (_≃_.left-inverse-of Lens-as-Σ _))                         ≡⟨⟩

  trans (sym (_≃_.left-inverse-of Lens-as-Σ _))
    (trans (cong (_≃_.from Lens-as-Σ)
              (Σ-≡,≡→≡ p
                 (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                  (sym (push-subst-, _ _)))
                             q)
                    (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                                 truncation-is-proposition))))))
       (_≃_.left-inverse-of Lens-as-Σ _))                         ≡⟨ cong₂ (λ eq₁ eq₂ →
                                                                              trans (sym eq₁)
                                                                                (trans (cong (_≃_.from Lens-as-Σ)
                                                                                          (Σ-≡,≡→≡ p
                                                                                             (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                                                                                              (sym (push-subst-, _ _)))
                                                                                                         q)
                                                                                                (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                                                                                                             truncation-is-proposition))))))
                                                                                   eq₂))
                                                                       (left-inverse-of-Lens-as-Σ _)
                                                                       (left-inverse-of-Lens-as-Σ _) ⟩
  trans (sym (η _))
    (trans (cong (_≃_.from Lens-as-Σ)
              (Σ-≡,≡→≡ p
                 (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                  (sym (push-subst-, _ _)))
                             q)
                    (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                                 truncation-is-proposition))))))
       (η _))                                                     ∎

-- A variant of the computation rule above.

cong-set-from-equality-characterisation₀ :
  let open Lens in
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
  (b : Block "equality-characterisation") →
  {p : R l₁ ≡ R l₂}
  {q : subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂} →
  cong set (_↔_.from (equality-characterisation₀ {l₁ = l₁} {l₂ = l₂} b)
              (p , q)) ≡
  cong (λ (_ , equiv) a b → _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
    (Σ-≡,≡→≡ p q)
cong-set-from-equality-characterisation₀
  {B = B} {l₁ = l₁@(⟨ _ , _ , _ ⟩)} {l₂ = l₂@(⟨ _ , _ , _ ⟩)}
  b {p = p} {q = q} =
  elim₁
    (λ {R₁} p → ∀ equiv₁ inhabited₁ q →
       cong set
         (_↔_.from (equality-characterisation₀
                     {l₁ = ⟨ R₁ , equiv₁ , inhabited₁ ⟩}
                     {l₂ = l₂} b)
            (p , q)) ≡
       cong (λ (_ , equiv) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (Σ-≡,≡→≡ p q))
    (λ equiv₁ inhabited₁ q →
       cong set
         (_↔_.from (equality-characterisation₀ b) (refl _ , q))           ≡⟨ cong (cong set) $
                                                                             from-equality-characterisation₀ b ⟩
       cong set
         (trans (sym (refl _))
            (trans (cong (_≃_.from Lens-as-Σ)
                      (Σ-≡,≡→≡ (refl _)
                         (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                          (sym (push-subst-, _ _)))
                                     q)
                            (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                                         truncation-is-proposition))))))
               (refl _)))                                                 ≡⟨ trans
                                                                               (cong₂ (λ eq₁ eq₂ → cong set (trans eq₁ eq₂))
                                                                                  sym-refl
                                                                                  (trans-reflʳ _)) $
                                                                             cong (cong set) $ trans-reflˡ _ ⟩
       cong set
         (cong (_≃_.from Lens-as-Σ)
            (Σ-≡,≡→≡ (refl _)
               (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                (sym (push-subst-, _ _)))
                           q)
                  (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                               truncation-is-proposition))))))            ≡⟨ cong-∘ _ _ _ ⟩

       cong (λ (_ , equiv , _) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (Σ-≡,≡→≡ (refl _)
            (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                             (sym (push-subst-, _ _)))
                        q)
               (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                            truncation-is-proposition)))))                ≡⟨ cong (cong _) $
                                                                             Σ-≡,≡→≡-reflˡ _ ⟩
       cong (λ (_ , equiv , _) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (cong (_ ,_)
            (trans (sym $ subst-refl _ _)
               (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                (sym (push-subst-, _ _)))
                           q)
                  (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                               truncation-is-proposition))))))            ≡⟨ cong-∘ _ _ _ ⟩

       cong (λ (equiv , _) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (trans (sym $ subst-refl _ _)
            (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                             (sym (push-subst-, _ _)))
                        q)
               (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                            truncation-is-proposition)))))                ≡⟨ trans (sym $ cong-∘ _ _ _) $
                                                                             cong (cong _) $ cong-trans _ _ _  ⟩
       cong (λ equiv a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (trans (cong proj₁ (sym $ subst-refl _ _))
            (cong proj₁
               (Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                (sym (push-subst-, _ _)))
                           q)
                  (proj₁ (+⇒≡ (Π-closure ext 1 λ _ →
                               truncation-is-proposition))))))            ≡⟨ cong (λ eq → cong _ (trans (cong proj₁ (sym $ subst-refl _ _)) eq)) $
                                                                             proj₁-Σ-≡,≡→≡ (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                                                                                   (sym (push-subst-, _ (λ R → R → ∥ B ∥))))
                                                                                              q) _ ⟩
       cong (λ equiv a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (trans (cong proj₁ (sym $ subst-refl _ _))
            (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                    (sym (push-subst-, _ _)))
               q))                                                        ≡⟨ cong (cong _) $
                                                                             elim¹
                                                                               (λ q →
                                                                                  trans (cong proj₁ (sym $ subst-refl _ _))
                                                                                    (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                                                                                            (sym (push-subst-, _ _)))
                                                                                       q) ≡
                                                                                  trans (sym $ subst-refl _ _) q)
                                                                               (
           trans (cong proj₁ $ sym $ subst-refl _ _)
             (≡⇒→ (cong (λ (eq , _) → eq ≡ _)
                     (sym (push-subst-, _ _)))
                (refl _))                                                       ≡⟨ cong (trans _) $ sym $
                                                                                   subst-in-terms-of-≡⇒↝ equivalence _ _ _ ⟩
           trans (cong proj₁ $ sym $ subst-refl _ _)
             (subst (λ (eq , _) → eq ≡ _)
                (sym (push-subst-, _ _))
                (refl _))                                                       ≡⟨ cong (trans _) $
                                                                                   subst-∘ _ _ _ ⟩
           trans (cong proj₁ $ sym $ subst-refl _ _)
             (subst (_≡ _)
                (cong proj₁ $ sym $ push-subst-, _ _)
                (refl _))                                                       ≡⟨ cong (trans _) $
                                                                                   trans subst-trans-sym $
                                                                                   trans (trans-reflʳ _) $
                                                                                   trans (sym (cong-sym _ _)) $
                                                                                   cong (cong _) $ sym-sym _ ⟩
           trans (cong proj₁ $ sym $ subst-refl _ _)
             (cong proj₁ $ push-subst-, {y≡z = refl _} _ _)                     ≡⟨ cong₂ trans
                                                                                     (cong-sym _ _)
                                                                                     (proj₁-push-subst-,-refl _ _) ⟩
           trans (sym $ cong proj₁ $ subst-refl _ _)
             (trans (cong proj₁ (subst-refl _ _))
                (sym $ subst-refl _ _))                                         ≡⟨ trans-sym-[trans] _ _ ⟩

           sym (subst-refl _ _)                                                 ≡⟨ sym $ trans-reflʳ _ ⟩∎

           trans (sym $ subst-refl _ _) (refl _)                                ∎)
                                                                               q ⟩
       cong (λ equiv a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (trans (sym $ subst-refl _ _) q)                                 ≡⟨ sym $ cong-∘ _ _ _ ⟩

       cong (λ (_ , equiv) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (cong (_ ,_) (trans (sym $ subst-refl _ _) q))                   ≡⟨ cong (cong _) $ sym $
                                                                             Σ-≡,≡→≡-reflˡ _ ⟩∎
       cong (λ (_ , equiv) a b →
               _≃_.from equiv (proj₁ (_≃_.to equiv a) , b))
         (Σ-≡,≡→≡ (refl _) q)                                             ∎)
    _ _ _ _
  where
  open Lens

-- An equality characterisation lemma.

equality-characterisation₀₁ :
  let open Lens in
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  (l₁ ≡ l₂)
    ≃
  ∃ λ (p : R l₁ ≡ R l₂) →
    ∀ a → (subst id p (remainder l₁ a) , get l₁ a) ≡
          _≃_.to (equiv l₂) a
equality-characterisation₀₁ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                       ↔⟨ equality-characterisation₀ ⊠ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)         ↝⟨ (∃-cong λ _ → inverse $ ≃-to-≡≃≡ ext ext) ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     ∀ a → _≃_.to (subst (λ R → A ≃ (R × B)) p (equiv l₁)) a ≡
           _≃_.to (equiv l₂) a)                                 ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ →
                                                                    ≡⇒≃ $ cong (_≡ _) $
                                                                    trans (cong (_$ _) $ Eq.to-subst) $
                                                                    trans (sym $ push-subst-application _ _) $
                                                                    trans (push-subst-, _ _) $
                                                                    cong (subst id _ _ ,_) $ subst-const _) ⟩□
  (∃ λ (p : R l₁ ≡ R l₂) →
     ∀ a → (subst id p (remainder l₁ a) , get l₁ a) ≡
           _≃_.to (equiv l₂) a)                                 □
  where
  open Lens

private

  -- An equality characterisation lemma with a "computation" rule.

  equality-characterisation₁′ :
    let open Lens in
    {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
    (bl : Block "equality-characterisation₀") →
    Block "equality-characterisation₁" →
    (univ : Univalence (a ⊔ b)) →
    ∃ λ (eq : l₁ ≡ l₂
                ↔
              ∃ λ (p : R l₁ ≃ R l₂) →
                ∀ a → (_≃_.to p (remainder l₁ a) , get l₁ a) ≡
                      _≃_.to (equiv l₂) a) →
      (p : R l₁ ≃ R l₂)
      (q : ∀ a → (_≃_.to p (remainder l₁ a) , get l₁ a) ≡
                      _≃_.to (equiv l₂) a) →
      _↔_.from eq (p , q) ≡
      _↔_.from (equality-characterisation₀ bl)
        ( ≃⇒≡ univ p
        , Eq.lift-equality ext
            (trans
               (≃-elim¹ univ
                  (λ {R} p →
                     _≃_.to (subst (λ R → A ≃ (R × B))
                               (≃⇒≡ univ p) (equiv l₁)) ≡
                     (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
                  (trans
                     (cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B))
                                             eq (equiv l₁)))
                        (≃⇒≡-id univ))
                     (cong _≃_.to $ subst-refl _ _))
                  p)
               (⟨ext⟩ q))
        )
  equality-characterisation₁′ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂}
                              b ⊠ univ =
      (l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₀ b ⟩

       (∃ λ (p : R l₁ ≡ R l₂) →
          subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)              ↝⟨ inverse $ Σ-cong (inverse $ ≡≃≃ univ) (λ _ → F.id) ⟩

       (∃ λ (p : R l₁ ≃ R l₂) →
          subst (λ R → A ≃ (R × B)) (≃⇒≡ univ p) (equiv l₁) ≡ equiv l₂)   ↔⟨ (∃-cong λ _ → inverse $ ≃-to-≡≃≡ ext bad-ext) ⟩

       (∃ λ (p : R l₁ ≃ R l₂) →
          ∀ a →
          _≃_.to (subst (λ R → A ≃ (R × B)) (≃⇒≡ univ p) (equiv l₁)) a ≡
          _≃_.to (equiv l₂) a)                                            ↔⟨ (∃-cong λ p → ∀-cong ext λ a → inverse $ ≡⇒≃ $
                                                                              cong (_≡ _) $ sym $ cong (_$ a) $
                                                                              ≃-elim¹ univ
                                                                                (λ {R} p →
                                                                                   _≃_.to (subst (λ R → A ≃ (R × B)) (≃⇒≡ univ p) (equiv l₁)) ≡
                                                                                   (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
                                                                                (
           _≃_.to (subst (λ R → A ≃ (R × B))
                     (≃⇒≡ univ Eq.id) (equiv l₁))                                ≡⟨ cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B)) eq (equiv l₁))) $
                                                                                    ≃⇒≡-id univ ⟩

           _≃_.to (subst (λ R → A ≃ (R × B)) (refl _) (equiv l₁))                ≡⟨ cong _≃_.to $ subst-refl _ _ ⟩∎

           _≃_.to (equiv l₁)                                                     ∎)
                                                                                p) ⟩□
       (∃ λ (p : R l₁ ≃ R l₂) →
          ∀ a → (_≃_.to p (remainder l₁ a) , get l₁ a) ≡
                _≃_.to (equiv l₂) a)                                      □)
    , λ p q →
        _↔_.from (equality-characterisation₀ b)
          ( ≃⇒≡ univ p
          , Eq.lift-equality ext
              (⟨ext⟩ λ a →
               ≡⇒→ (cong (_≡ _) $ sym $ cong (_$ a) $
                    ≃-elim¹ univ
                      (λ {R} p →
                         _≃_.to (subst (λ R → A ≃ (R × B))
                                   (≃⇒≡ univ p) (equiv l₁)) ≡
                         (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
                      (trans
                         (cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B))
                                                 eq (equiv l₁)))
                            (≃⇒≡-id univ))
                         (cong _≃_.to $ subst-refl _ _))
                      p)
                 (q a))
          )                                                               ≡⟨ (cong (λ eq → _↔_.from (equality-characterisation₀ b)
                                                                                             (≃⇒≡ univ p , Eq.lift-equality ext (⟨ext⟩ eq))) $
                                                                              ⟨ext⟩ λ a →
                                                                              trans (sym $ subst-in-terms-of-≡⇒↝ equivalence _ _ _) $
                                                                              subst-trans _) ⟩
        _↔_.from (equality-characterisation₀ b)
          ( ≃⇒≡ univ p
          , Eq.lift-equality ext
              (⟨ext⟩ λ a →
               trans
                 (cong (_$ a) $
                  ≃-elim¹ univ
                    (λ {R} p →
                       _≃_.to (subst (λ R → A ≃ (R × B))
                                 (≃⇒≡ univ p) (equiv l₁)) ≡
                       (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
                    (trans
                       (cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B))
                                               eq (equiv l₁)))
                          (≃⇒≡-id univ))
                       (cong _≃_.to $ subst-refl _ _))
                    p)
                 (q a))
          )                                                               ≡⟨ cong (λ eq → _↔_.from (equality-characterisation₀ b)
                                                                                            (≃⇒≡ univ p , Eq.lift-equality ext eq)) $
                                                                             trans (ext-trans _ _) $
                                                                             cong (flip trans _) $
                                                                             _≃_.right-inverse-of (Eq.extensionality-isomorphism bad-ext) _ ⟩
        _↔_.from (equality-characterisation₀ b)
          ( ≃⇒≡ univ p
          , Eq.lift-equality ext
              (trans
                 (≃-elim¹ univ
                    (λ {R} p →
                       _≃_.to (subst (λ R → A ≃ (R × B))
                                 (≃⇒≡ univ p) (equiv l₁)) ≡
                       (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
                    (trans
                       (cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B))
                                               eq (equiv l₁)))
                          (≃⇒≡-id univ))
                       (cong _≃_.to $ subst-refl _ _))
                    p)
                 (⟨ext⟩ q))
          )                                                               ∎
    where
    open Lens

-- An equality characterisation lemma.

equality-characterisation₁ :
  let open Lens in
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (p : R l₁ ≃ R l₂) →
    ∀ a → (_≃_.to p (remainder l₁ a) , get l₁ a) ≡
          _≃_.to (equiv l₂) a
equality-characterisation₁ b univ =
  proj₁ (equality-characterisation₁′ b b univ)

-- A "computation" rule.

from-equality-characterisation₁ :
  let open Lens in
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
  (bl : Block "equality-characterisation") →
  (univ : Univalence (a ⊔ b))
  (p : R l₁ ≃ R l₂)
  (q : ∀ a → (_≃_.to p (remainder l₁ a) , get l₁ a) ≡
             _≃_.to (equiv l₂) a) →
  _↔_.from (equality-characterisation₁ {l₁ = l₁} {l₂ = l₂} bl univ)
    (p , q) ≡
  _↔_.from (equality-characterisation₀ bl)
    ( ≃⇒≡ univ p
    , Eq.lift-equality ext
        (trans
           (≃-elim¹ univ
              (λ {R} p →
                 _≃_.to (subst (λ R → A ≃ (R × B))
                           (≃⇒≡ univ p) (equiv l₁)) ≡
                 (λ a → _≃_.to p (remainder l₁ a) , get l₁ a))
              (trans
                 (cong (λ eq → _≃_.to (subst (λ R → A ≃ (R × B))
                                         eq (equiv l₁)))
                    (≃⇒≡-id univ))
                 (cong _≃_.to $ subst-refl _ _))
              p)
           (⟨ext⟩ q))
    )
from-equality-characterisation₁ b univ _ _ =
  proj₂ (equality-characterisation₁′ b b univ) _ _

-- An equality characterisation lemma.

equality-characterisation₀₂ :
  let open Lens in
  {l₁ l₂ : Lens A B} →
  Block "equality-characterisation" →
  (l₁ ≡ l₂)
    ≃
  ∃ λ (p : R l₁ ≡ R l₂) →
    (∀ a → subst id p (remainder l₁ a) ≡ remainder l₂ a) ×
    (∀ a → get l₁ a ≡ get l₂ a)
equality-characterisation₀₂ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} ⊠ =
  l₁ ≡ l₂                                                      ↝⟨ equality-characterisation₀₁ ⊠ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     ∀ a → (subst id p (remainder l₁ a) , get l₁ a) ≡
           _≃_.to (equiv l₂) a)                                ↔⟨⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     ∀ a → (subst id p (remainder l₁ a) , get l₁ a) ≡
           (remainder l₂ a , get l₂ a))                        ↔⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse ≡×≡↔≡) ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     ∀ a → subst id p (remainder l₁ a) ≡ remainder l₂ a ×
           get l₁ a ≡ get l₂ a)                                ↔⟨ (∃-cong λ _ → ΠΣ-comm) ⟩□

  (∃ λ (p : R l₁ ≡ R l₂) →
     (∀ a → subst id p (remainder l₁ a) ≡ remainder l₂ a) ×
     (∀ a → get l₁ a ≡ get l₂ a))                              □
  where
  open Lens

private

  -- An equality characterisation lemma with a "computation" rule.

  equality-characterisation₂′ :
    {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
    let open Lens in
    (bl : Block "equality-characterisation₁") →
    Block "equality-characterisation₂" →
    (univ : Univalence (a ⊔ b)) →
    ∃ λ (eq : l₁ ≡ l₂
                ↔
              ∃ λ (r : R l₁ ≃ R l₂) →
                (∀ x → _≃_.to r (remainder l₁ x) ≡ remainder l₂ x)
                  ×
                (∀ x → get l₁ x ≡ get l₂ x)) →
      (r₁ : R l₁ ≃ R l₂)
      (r₂ : ∀ x → _≃_.to r₁ (remainder l₁ x) ≡ remainder l₂ x)
      (g : ∀ x → get l₁ x ≡ get l₂ x) →
      _↔_.from eq (r₁ , r₂ , g) ≡
      _↔_.from (equality-characterisation₁ bl univ)
        (r₁ , λ a → cong₂ _,_ (r₂ a) (g a))
  equality-characterisation₂′ {l₁ = l₁} {l₂ = l₂} bl ⊠ univ =
      (l₁ ≡ l₂                                                 ↝⟨ equality-characterisation₁ bl univ ⟩

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
          (∀ x → get l₁ x ≡ get l₂ x))                         □)
    , λ _ _ _ → refl _
    where
    open Lens

-- An equality characterisation lemma.

equality-characterisation₂ :
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Block "equality-characterisation" →
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    (∀ x → _≃_.to eq (remainder l₁ x) ≡ remainder l₂ x)
      ×
    (∀ x → get l₁ x ≡ get l₂ x)
equality-characterisation₂ bl univ =
  proj₁ (equality-characterisation₂′ bl bl univ)

-- A "computation" rule.

from-equality-characterisation₂ :
  let open Lens in
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B}
  (bl : Block "equality-characterisation") →
  (univ : Univalence (a ⊔ b))
  (r₁ : R l₁ ≃ R l₂)
  (r₂ : ∀ x → _≃_.to r₁ (remainder l₁ x) ≡ remainder l₂ x)
  (g : ∀ x → get l₁ x ≡ get l₂ x) →
  _↔_.from (equality-characterisation₂ {l₁ = l₁} {l₂ = l₂} bl univ)
    (r₁ , r₂ , g) ≡
  _↔_.from (equality-characterisation₁ bl univ)
    (r₁ , λ a → cong₂ _,_ (r₂ a) (g a))
from-equality-characterisation₂ bl univ =
  proj₂ (equality-characterisation₂′ bl bl univ)

-- An equality characterisation lemma.

equality-characterisation₃ :
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Univalence (a ⊔ b) →
  l₁ ≡ l₂
    ↔
  ∃ λ (eq : R l₁ ≃ R l₂) →
    ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
          _≃_.from (equiv l₂) p
equality-characterisation₃ {A = A} {B = B} {l₁ = l₁} {l₂ = l₂} univ =
  l₁ ≡ l₂                                                            ↝⟨ equality-characterisation₀ ⊠ ⟩

  (∃ λ (p : R l₁ ≡ R l₂) →
     subst (λ R → A ≃ (R × B)) p (equiv l₁) ≡ equiv l₂)              ↝⟨ inverse $ Σ-cong (inverse $ ≡≃≃ univ) (λ _ → F.id) ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     subst (λ R → A ≃ (R × B)) (≃⇒≡ univ eq) (equiv l₁) ≡ equiv l₂)  ↔⟨ (∃-cong λ _ → inverse $ ≡⇒≃ $ cong (_≡ _) $
                                                                         transport-theorem
                                                                           (λ R → A ≃ (R × B))
                                                                           (λ X≃Y → (X≃Y ×-cong F.id) F.∘_)
                                                                           (λ _ → Eq.lift-equality ext (refl _))
                                                                           univ _ _) ⟩
  (∃ λ (eq : R l₁ ≃ R l₂) →
     (eq ×-cong F.id) F.∘ equiv l₁ ≡ equiv l₂)                       ↝⟨ (∃-cong λ _ → inverse $ ≃-from-≡↔≡ ext) ⟩□

  (∃ λ (eq : R l₁ ≃ R l₂) →
     ∀ p → _≃_.from (equiv l₁) (_≃_.from eq (proj₁ p) , proj₂ p) ≡
           _≃_.from (equiv l₂) p)                                    □
  where
  open Lens

-- An equality characterisation lemma for lenses for which the view
-- type is inhabited.

equality-characterisation₄ :
  {A : Type a} {B : Type b} {l₁ l₂ : Lens A B} →
  let open Lens in
  Block "equality-characterisation" →
  Univalence (a ⊔ b) →
  (b : B) →
  (l₁ ≡ l₂)
    ≃
  (∃ λ (eq : get l₁ ⁻¹ b ≃ get l₂ ⁻¹ b) →
     (∀ a → _≃_.to eq (set l₁ a b , get-set l₁ a b) ≡
            (set l₂ a b , get-set l₂ a b))
       ×
     (∀ a → get l₁ a ≡ get l₂ a))
equality-characterisation₄ {l₁ = l₁} {l₂ = l₂} bl univ b =
  l₁ ≡ l₂                                                          ↔⟨ equality-characterisation₂ bl univ ⟩

  (∃ λ (eq : R l₁ ≃ R l₂) →
     (∀ a → _≃_.to eq (remainder l₁ a) ≡ remainder l₂ a)
       ×
     (∀ a → get l₁ a ≡ get l₂ a))                                  ↝⟨ inverse $
                                                                      Σ-cong
                                                                        (inverse $
                                                                         Eq.≃-preserves ext (remainder≃get⁻¹ l₁ b) (remainder≃get⁻¹ l₂ b))
                                                                        (λ _ → F.id) ⟩
  (∃ λ (eq : get l₁ ⁻¹ b ≃ get l₂ ⁻¹ b) →
     (∀ a → remainder l₂
              (proj₁ (_≃_.to eq (set l₁ a b , get-set l₁ a b))) ≡
            remainder l₂ a)
       ×
     (∀ a → get l₁ a ≡ get l₂ a))                                  ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → ∀-cong ext λ a →
                                                                       ≡⇒≃ $ cong (remainder l₂ _ ≡_) $ sym $
                                                                       remainder-set l₂ _ _) ⟩
  (∃ λ (eq : get l₁ ⁻¹ b ≃ get l₂ ⁻¹ b) →
     (∀ a → remainder l₂
              (proj₁ (_≃_.to eq (set l₁ a b , get-set l₁ a b))) ≡
            remainder l₂ (set l₂ a b))
       ×
     (∀ a → get l₁ a ≡ get l₂ a))                                  ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → ∀-cong ext λ a →
                                                                       Eq.≃-≡ (inverse $ remainder≃get⁻¹ l₂ b)) ⟩□
  (∃ λ (eq : get l₁ ⁻¹ b ≃ get l₂ ⁻¹ b) →
     (∀ a → _≃_.to eq (set l₁ a b , get-set l₁ a b) ≡
            (set l₂ a b , get-set l₂ a b))
       ×
     (∀ a → get l₁ a ≡ get l₂ a))                                  □
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

-- Two lenses of type Lens A B are equal if B is inhabited and the
-- lenses' setters are equal (assuming univalence).
--
-- Some results below are more general than this one, but this proof,
-- which uses remainder≃get⁻¹, is rather easy.

lenses-with-inhabited-codomains-equal-if-setters-equal :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  B →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-with-inhabited-codomains-equal-if-setters-equal
  {B = B} univ l₁ l₂ b setters-equal =
  _↔_.from (equality-characterisation₂ ⊠ univ)
    ( R≃R
    , (λ a →
         remainder l₂ (set l₁ a b)  ≡⟨ cong (λ f → remainder l₂ (f a b)) setters-equal ⟩
         remainder l₂ (set l₂ a b)  ≡⟨ remainder-set l₂ _ _ ⟩∎
         remainder l₂ a             ∎)
    , getters-equal
    )
  where
  open Lens

  getters-equal =
    ext⁻¹ $ getters-equal-if-setters-equal l₁ l₂ setters-equal

  R≃R : R l₁ ≃ R l₂
  R≃R =
    R l₁         ↝⟨ remainder≃get⁻¹ l₁ b ⟩
    get l₁ ⁻¹ b  ↔⟨ Preimage.respects-extensional-equality getters-equal ⟩
    get l₂ ⁻¹ b  ↝⟨ inverse $ remainder≃get⁻¹ l₂ b ⟩□
    R l₂         □

-- A generalisation of lenses-equal-if-setters-equal (which is defined
-- below).

lenses-equal-if-setters-equal′ :
  let open Lens in
  {A : Type a} {B : Type b}
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

  _↔_.from (equality-characterisation₂ ⊠ univ)
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

  id-f≃ : Eq.Is-equivalence (Σ-map id f)
  id-f≃ = Eq.respects-extensional-equality
    (λ (b , r) →
       let b′ , ≡fr = ∃≡f b r in
       to BR≃BR (b , r)                             ≡⟨ to-BR≃BR _ _ _ ⟩
       b , remainder l₂ (from (equiv l₁) (r , b′))  ≡⟨ cong (b ,_) ≡fr ⟩
       b , f r                                      ≡⟨⟩
       Σ-map id f (b , r)                           ∎)
    (is-equivalence BR≃BR)

  f≃ : Eq.Is-equivalence f
  f≃ =
    HA.[inhabited→Is-equivalence]→Is-equivalence λ r →
    Trunc.rec
      (Eq.propositional ext _)
      (Eq.drop-Σ-map-id _ id-f≃)
      (inhabited l₂ r)

  R≃R : R l₁ ≃ R l₂
  R≃R = Eq.⟨ f , f≃ ⟩

-- If the codomain of a lens is inhabited when it is merely inhabited
-- and the remainder type is inhabited, then this lens is equal to
-- another lens if their setters are equal (assuming univalence).

lenses-equal-if-setters-equal :
  {A : Type a} {B : Type b} →
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
  {A : Type a} {B : Type b} →
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
       f (remainder l₁ a)  ≡⟨ R₂-prop _ _ ⟩∎
       remainder l₂ a      ∎)
  where
  open Lens

  f : R l₁ → R l₂
  f r =
    Trunc.rec R₂-prop
      (λ b → remainder l₂ (_≃_.from (equiv l₁) (r , b)))
      (inhabited l₁ r)

-- A generalisation of the previous result: If a lens has a remainder
-- type that is a set, then this lens is equal to another lens if
-- their setters are equal (assuming univalence).
--
-- This result is due to Andrea Vezzosi.

lenses-equal-if-setters-equal-and-remainder-set :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  (l₁ l₂ : Lens A B) →
  Is-set (Lens.R l₂) →
  Lens.set l₁ ≡ Lens.set l₂ →
  l₁ ≡ l₂
lenses-equal-if-setters-equal-and-remainder-set
  {B = B} univ l₁ l₂ R₂-set setters-equal =

  lenses-equal-if-setters-equal′
    univ l₁ l₂ f
    (λ b r →
         b
       , (remainder l₂ (_≃_.from (equiv l₁) (r , b))  ≡⟨ cong (f₂ r) $ truncation-is-proposition ∣ _ ∣ (inhabited l₁ r) ⟩∎
          f r                                         ∎))
    (λ a →
       f (remainder l₁ a)                                   ≡⟨⟩
       f₂ (remainder l₁ a) (inhabited l₁ (remainder l₁ a))  ≡⟨ cong (f₂ (remainder l₁ a)) $
                                                               truncation-is-proposition (inhabited l₁ (remainder l₁ a)) ∣ _ ∣ ⟩
       f₁ (remainder l₁ a) (get l₁ a)                       ≡⟨ sym $ f₁-remainder _ _ ⟩∎
       remainder l₂ a                                       ∎)
    setters-equal
  where
  open Lens

  f₁ : R l₁ → B → R l₂
  f₁ r b = remainder l₂ (_≃_.from (equiv l₁) (r , b))

  f₁-remainder : ∀ a b → remainder l₂ a ≡ f₁ (remainder l₁ a) b
  f₁-remainder a b =
    remainder l₂ a             ≡⟨ sym $ remainder-set l₂ a b ⟩
    remainder l₂ (set l₂ a b)  ≡⟨ cong (λ f → remainder l₂ (f a b)) $ sym setters-equal ⟩∎
    remainder l₂ (set l₁ a b)  ∎

  f₂ : R l₁ → ∥ B ∥ → R l₂
  f₂ r =
    _↔_.to (constant-function↔∥inhabited∥⇒inhabited R₂-set)
      ( f₁ r
      , λ b₁ b₂ →
          let a = _≃_.from (equiv l₁) (r , b₁) in
          remainder l₂ a                                            ≡⟨ f₁-remainder _ _ ⟩
          f₁ (remainder l₁ a) b₂                                    ≡⟨⟩
          remainder l₂ (_≃_.from (equiv l₁) (remainder l₁ a , b₂))  ≡⟨ cong (λ p → f₁ (proj₁ p) b₂) $ _≃_.right-inverse-of (equiv l₁) _ ⟩∎
          remainder l₂ (_≃_.from (equiv l₁) (r , b₂))               ∎
      )

  f : R l₁ → R l₂
  f r = f₂ r (inhabited l₁ r)

-- If lenses from A × C to C (where the universe of A is at least as
-- large as the universe of C) with equal setters are equal, then
-- weakly constant functions from C to equivalences between A and B
-- (where B lives in the same universe as A) are coherently constant.
--
-- This result is due to Andrea Vezzosi.

lenses-equal-if-setters-equal→constant→coherently-constant :
  ∀ ℓ {A B : Type (c ⊔ ℓ)} {C : Type c} →
  ((l₁ l₂ : Lens (A × C) C) → Lens.set l₁ ≡ Lens.set l₂ → l₁ ≡ l₂) →
  (A≃B : C → A ≃ B) →
  Constant A≃B →
  ∃ λ (A≃B′ : ∥ C ∥ → A ≃ B) → A≃B ≡ A≃B′ ∘ ∣_∣
lenses-equal-if-setters-equal→constant→coherently-constant
  _ {A = A} {B = B} {C = C} lenses-equal-if-setters-equal A≃B c =
  A≃B′ , A≃B≡
  where
  open Lens

  module _ (∥c∥ : ∥ C ∥) where

    l₁ l₂ : Lens (A × C) C
    l₁ = record
      { R         = A
      ; equiv     = F.id
      ; inhabited = λ _ → ∥c∥
      }

    l₂ = record
      { R         = B
      ; equiv     = A × C  ↔⟨ ×-comm ⟩
                    C × A  ↝⟨ ∃-cong A≃B ⟩
                    C × B  ↔⟨ ×-comm ⟩□
                    B × C  □
      ; inhabited = λ _ → ∥c∥
      }

    setters-equal : ∀ p c → set l₁ p c ≡ set l₂ p c
    setters-equal (a , c₁) c₂ =
      cong (_, c₂) $ sym $
        (_≃_.from (A≃B c₂) (_≃_.to (A≃B c₁) a)  ≡⟨ cong (λ eq → _≃_.from (A≃B c₂) (_≃_.to eq a)) $ c c₁ c₂ ⟩
         _≃_.from (A≃B c₂) (_≃_.to (A≃B c₂) a)  ≡⟨ _≃_.left-inverse-of (A≃B c₂) a ⟩∎
         a                                      ∎)

    l₁≡l₂ : l₁ ≡ l₂
    l₁≡l₂ =
      lenses-equal-if-setters-equal l₁ l₂
        (⟨ext⟩ λ p → ⟨ext⟩ λ c → setters-equal p c)

    l₁≡l₂′ = _≃_.to (equality-characterisation₀₂ ⊠) l₁≡l₂

    A≃B′ : A ≃ B
    A≃B′ = ≡⇒≃ $ proj₁ l₁≡l₂′

  A≃B≡ : A≃B ≡ A≃B′ ∘ ∣_∣
  A≃B≡ = ⟨ext⟩ λ c → Eq.lift-equality ext $ ⟨ext⟩ λ a →
    _≃_.to (A≃B c) a                                                ≡⟨⟩
    remainder (l₂ ∣ c ∣) (a , c)                                    ≡⟨ sym $ proj₁ (proj₂ (l₁≡l₂′ ∣ c ∣)) _ ⟩
    subst id (proj₁ (l₁≡l₂′ ∣ c ∣)) (remainder (l₁ ∣ c ∣) (a , c))  ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    ≡⇒→ (proj₁ (l₁≡l₂′ ∣ c ∣)) (remainder (l₁ ∣ c ∣) (a , c))       ≡⟨⟩
    _≃_.to (A≃B′ ∣ c ∣) a                                           ∎

-- The functions ≃→lens and ≃→lens′ are pointwise equal (when
-- applicable, assuming univalence).

≃→lens≡≃→lens′ :
  {A B : Type a} →
  Univalence a →
  (A≃B : A ≃ B) → ≃→lens A≃B ≡ ≃→lens′ A≃B
≃→lens≡≃→lens′ {B = B} univ A≃B =
  _↔_.from (equality-characterisation₂ ⊠ univ)
    ( (∥ ↑ _ B ∥  ↔⟨ ∥∥-cong Bij.↑↔ ⟩□
       ∥ B ∥      □)
    , (λ _ → refl _)
    , (λ _ → refl _)
    )

-- If the getter of a lens is an equivalence, then the lens formed
-- using the equivalence (using ≃→lens) is equal to the lens (assuming
-- univalence).

get-equivalence→≡≃→lens :
  {A : Type a} {B : Type b} →
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
  {A B : Type a} →
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
-- Some equivalences

-- "The getter is an equivalence" is equivalent to "the remainder type
-- is equivalent to the propositional truncation of the codomain".

get-equivalence≃inhabited-equivalence :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) ≃ Is-equivalence (Lens.inhabited l)
get-equivalence≃inhabited-equivalence {A = A} {B = B} l =
  Is-equivalence (get l)                  ↝⟨ Eq.⇔→≃
                                               (Eq.propositional ext _)
                                               (Eq.propositional ext _)
                                               (flip (Eq.Two-out-of-three.g∘f-f (Eq.two-out-of-three _ _))
                                                  (_≃_.is-equivalence (equiv l)))
                                               (Eq.Two-out-of-three.f-g (Eq.two-out-of-three _ _)
                                                  (_≃_.is-equivalence (equiv l))) ⟩
  Is-equivalence (proj₂ ⦂ (R l × B → B))  ↝⟨ inverse $ equivalence-to-∥∥≃proj₂-equivalence _ ⟩□
  Is-equivalence (inhabited l)            □
  where
  open Lens

-- "The getter is an equivalence" is equivalent to "the remainder type
-- is equivalent to the propositional truncation of the codomain".

get-equivalence≃remainder≃∥codomain∥ :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) ≃ (Lens.R l ≃ ∥ B ∥)
get-equivalence≃remainder≃∥codomain∥ {A = A} {B = B} l =
  Is-equivalence (get l)                          ↝⟨ get-equivalence≃inhabited-equivalence l ⟩
  Is-equivalence (inhabited l)                    ↔⟨ inverse $
                                                     drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                     propositional⇒inhabited⇒contractible
                                                       (Π-closure ext 1 λ _ →
                                                        truncation-is-proposition)
                                                       (inhabited l) ⟩
  (∃ λ (inh : R l → ∥ B ∥) → Is-equivalence inh)  ↔⟨ inverse Eq.≃-as-Σ ⟩□
  R l ≃ ∥ B ∥                                     □
  where
  open Lens

------------------------------------------------------------------------
-- Some lens isomorphisms

-- A generalised variant of Lens preserves bijections.

Lens-cong′ :
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  (∃ λ (R : Type r) → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥)) ↔
  (∃ λ (R : Type r) → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))
Lens-cong′ A₁↔A₂ B₁↔B₂ =
  ∃-cong λ _ →
  Eq.≃-preserves-bijections ext A₁↔A₂ (F.id ×-cong B₁↔B₂)
    ×-cong
  →-cong ext F.id (∥∥-cong B₁↔B₂)

-- Lens preserves level-preserving bijections.

Lens-cong :
  {A₁ A₂ : Type a} {B₁ B₂ : Type b} →
  A₁ ↔ A₂ → B₁ ↔ B₂ →
  Lens A₁ B₁ ↔ Lens A₂ B₂
Lens-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁↔A₂ B₁↔B₂ =
  Lens A₁ B₁                              ↔⟨ Lens-as-Σ ⟩
  (∃ λ R → A₁ ≃ (R × B₁) × (R → ∥ B₁ ∥))  ↝⟨ Lens-cong′ A₁↔A₂ B₁↔B₂ ⟩
  (∃ λ R → A₂ ≃ (R × B₂) × (R → ∥ B₂ ∥))  ↔⟨ inverse Lens-as-Σ ⟩□
  Lens A₂ B₂                              □

-- If B is a proposition, then Lens A B is isomorphic to A → B
-- (assuming univalence).

lens-to-proposition↔get :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Lens A B ↔ (A → B)
lens-to-proposition↔get {b = b} {A = A} {B = B} univ B-prop =
  Lens A B                             ↔⟨ Lens-as-Σ ⟩
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
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b))
  (prop : Is-proposition B)
  (l : Lens A B) →
  _↔_.to (lens-to-proposition↔get univ prop) l ≡
  Trunc.rec prop id ∘ Lens.inhabited l ∘ Lens.remainder l
_ = λ _ _ _ → refl _

-- A variant of the previous result.

lens-to-proposition≃get :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  Is-proposition B →
  Lens A B ≃ (A → B)
lens-to-proposition≃get {b = b} {A = A} {B = B} univ prop = Eq.↔→≃
  get
  from
  refl
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
     _↔_.from (equality-characterisation₁ ⊠ univ)
        (lemma , λ _ → refl _))
  where
  open Lens

  from = λ get → record
    { R         = ↑ b A
    ; equiv     = A          ↔⟨ inverse Bij.↑↔ ⟩
                  ↑ b A      ↔⟨ (inverse $ drop-⊤-right {k = bijection} λ (lift a) →
                                 _⇔_.to contractible⇔↔⊤ $
                                 propositional⇒inhabited⇒contractible prop (get a)) ⟩□
                  ↑ b A × B  □
    ; inhabited = ∣_∣ ∘ get ∘ lower
    }

_ :
  {A : Type a} {B : Type b}
  (univ : Univalence (a ⊔ b))
  (prop : Is-proposition B)
  (l : Lens A B) →
  _≃_.to (lens-to-proposition≃get univ prop) l ≡ Lens.get l
_ = λ _ _ _ → refl _

-- If B is contractible, then Lens A B is isomorphic to ⊤ (assuming
-- univalence).

lens-to-contractible↔⊤ :
  {A : Type a} {B : Type b} →
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
  {A : Type a} →
  Univalence (a ⊔ b) →
  Lens A (⊥ {ℓ = b}) ↔ ¬ A
lens-to-⊥↔¬ {A = A} univ =
  Lens A ⊥  ↝⟨ lens-to-proposition↔get univ ⊥-propositional ⟩
  (A → ⊥)   ↝⟨ inverse $ ¬↔→⊥ ext ⟩□
  ¬ A       □

-- If A is contractible, then Lens A B is isomorphic to Contractible B
-- (assuming univalence).

lens-from-contractible↔codomain-contractible :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  Contractible A →
  Lens A B ↔ Contractible B
lens-from-contractible↔codomain-contractible {A = A} {B} univ cA =
  Lens A B                                                   ↔⟨ Lens-as-Σ ⟩
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
  {B : Type b} →
  Univalence (a ⊔ b) →
  Lens (⊥ {ℓ = a}) B ↔ ⊤
lens-from-⊥↔⊤ {B = B} univ =
  _⇔_.to contractible⇔↔⊤ $
    isomorphism-to-lens
      (⊥      ↝⟨ inverse ×-left-zero ⟩□
       ⊥ × B  □) ,
    λ l → _↔_.from (equality-characterisation₁ ⊠ univ)
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
    whatever : ∀ {ℓ} {Whatever : R l → Type ℓ} → (r : R l) → Whatever r
    whatever r = ⊥-elim {ℓ = lzero} $ Trunc.rec
      ⊥-propositional
      (λ b → ⊥-elim (_≃_.from (equiv l) (r , b)))
      (inhabited l r)

-- There is an equivalence between A ≃ B and
-- ∃ λ (l : Lens A B) → Is-equivalence (Lens.get l) (assuming
-- univalence).
--
-- See also ≃≃≊ below.

≃-≃-Σ-Lens-Is-equivalence-get :
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  (A ≃ B) ≃ (∃ λ (l : Lens A B) → Is-equivalence (Lens.get l))
≃-≃-Σ-Lens-Is-equivalence-get {a = a} {A = A} {B = B} univ =
  A ≃ B                                                ↝⟨ Eq.≃-preserves ext F.id (inverse ∥∥×≃) ⟩
  A ≃ (∥ B ∥ × B)                                      ↝⟨ inverse $
                                                          Eq.↔⇒≃ Σ-left-identity F.∘
                                                          Σ-cong (singleton-with-≃-↔-⊤ {a = a} ext univ)
                                                            (λ (C , C≃∥B∥) → Eq.≃-preserves ext F.id (×-cong₁ λ _ → C≃∥B∥)) ⟩
  (∃ λ ((R , _) : ∃ λ R → R ≃ ∥ B ∥) → A ≃ (R × B))    ↔⟨ inverse $
                                                          (Σ-cong (∃-cong λ _ → inverse Eq.≃-as-Σ) λ _ → F.id) F.∘
                                                          Σ-assoc F.∘
                                                          (∃-cong λ _ → inverse (Σ-assoc F.∘ ×-comm)) F.∘
                                                          inverse Σ-assoc F.∘
                                                          Σ-cong Lens-as-Σ (λ _ → F.id) ⟩
  (∃ λ (l : Lens A B) → Is-equivalence (inhabited l))  ↝⟨ inverse $ ∃-cong get-equivalence≃inhabited-equivalence ⟩□
  (∃ λ (l : Lens A B) → Is-equivalence (get l))        □
  where
  open Lens

-- The right-to-left direction of ≃-≃-Σ-Lens-Is-equivalence-get
-- returns the lens's getter (and some proof).

to-from-≃-≃-Σ-Lens-Is-equivalence-get≡get :
  {A : Type a} {B : Type b} →
  (univ : Univalence (a ⊔ b))
  (p@(l , _) : ∃ λ (l : Lens A B) → Is-equivalence (Lens.get l)) →
  _≃_.to (_≃_.from (≃-≃-Σ-Lens-Is-equivalence-get univ) p) ≡
  Lens.get l
to-from-≃-≃-Σ-Lens-Is-equivalence-get≡get _ _ = refl _

------------------------------------------------------------------------
-- Results relating different kinds of lenses

-- In general there is no split surjection from Lens A B to
-- Traditional.Lens A B (assuming univalence).

¬Lens↠Traditional-lens :
  Univalence lzero →
  ¬ (Lens 𝕊¹ ⊤ ↠ Traditional.Lens 𝕊¹ ⊤)
¬Lens↠Traditional-lens univ =
  Lens 𝕊¹ ⊤ ↠ Traditional.Lens 𝕊¹ ⊤                                      ↝⟨ flip H-level.respects-surjection 1 ⟩
  (Is-proposition (Lens 𝕊¹ ⊤) → Is-proposition (Traditional.Lens 𝕊¹ ⊤))  ↝⟨ _$ mono₁ 0 (_⇔_.from contractible⇔↔⊤ $
                                                                                        lens-to-contractible↔⊤ univ ⊤-contractible) ⟩
  Is-proposition (Traditional.Lens 𝕊¹ ⊤)                                 ↝⟨ Traditional.¬-lens-to-⊤-propositional univ ⟩□
  ⊥                                                                      □

-- Some lemmas used in Lens↠Traditional-lens and Lens↔Traditional-lens
-- below.

private

  module Lens↔Traditional-lens
    {A : Type a} {B : Type b}
    (A-set : Is-set A)
    where

    from : Block "conversion" → Traditional.Lens A B → Lens A B
    from ⊠ l = isomorphism-to-lens
      (A                                     ↔⟨ Traditional.≃Σ∥set⁻¹∥× A-set l ⟩□
       (∃ λ (f : B → A) → ∥ set ⁻¹ f ∥) × B  □)
      where
      open Traditional.Lens l

    to∘from : ∀ bc l → Lens.traditional-lens (from bc l) ≡ l
    to∘from ⊠ l = Traditional.equal-laws→≡
      (λ a _ → B-set a _ _)
      (λ _ → A-set _ _)
      (λ _ _ _ → A-set _ _)
      where
      open Traditional.Lens l

      B-set : A → Is-set B
      B-set a =
        Traditional.h-level-respects-lens-from-inhabited 2 l a A-set

    from∘to :
      Univalence (a ⊔ b) →
      ∀ bc l → from bc (Lens.traditional-lens l) ≡ l
    from∘to univ ⊠ l′ =
      _↔_.from (equality-characterisation₁ ⊠ univ)
        ( ((∃ λ (f : B → A) → ∥ set ⁻¹ f ∥) × ∥ B ∥  ↝⟨ (×-cong₁ lemma₃) ⟩
           (∥ B ∥ → R) × ∥ B ∥                       ↝⟨ lemma₂ ⟩□
           R                                         □)
        , λ p →
            ( proj₁ (_≃_.to l (_≃_.from l (_≃_.to l p)))
            , proj₂ (_≃_.to l p)
            )                                             ≡⟨ cong (_, proj₂ (_≃_.to l p)) $ cong proj₁ $
                                                             _≃_.right-inverse-of l _ ⟩∎
            _≃_.to l p                                    ∎
        )
      where
      open Lens l′ renaming (equiv to l)

      B-set : A → Is-set B
      B-set a =
        Traditional.h-level-respects-lens-from-inhabited
          2
          (Lens.traditional-lens l′)
          a
          A-set

      R-set : Is-set R
      R-set =
        [inhabited⇒+]⇒+ 1 λ r →
        Trunc.rec
          (H-level-propositional ext 2)
          (λ b → proj₁-closure (const b) 2 $
                 H-level.respects-surjection
                   (_≃_.surjection l) 2 A-set)
          (inhabited r)

      lemma₁ :
        ∥ B ∥ →
        (f : B → A) →
        ∥ set ⁻¹ f ∥ ≃ (∀ b b′ → set (f b) b′ ≡ f b′)
      lemma₁ ∥b∥ f = Eq.⇔→≃
        truncation-is-proposition
        prop
        (Trunc.rec prop λ (a , set-a≡f) b b′ →
         set (f b) b′      ≡⟨ cong (λ f → set (f b) b′) $ sym set-a≡f ⟩
         set (set a b) b′  ≡⟨ set-set _ _ _ ⟩
         set a b′          ≡⟨ cong (_$ b′) set-a≡f ⟩∎
         f b′              ∎)
        (λ hyp →
           flip ∥∥-map ∥b∥ λ b →
           f b , ⟨ext⟩ (hyp b))
        where
        prop =
          Π-closure ext 1 λ _ →
          Π-closure ext 1 λ _ →
          A-set

      lemma₂ : ((∥ B ∥ → R) × ∥ B ∥) ≃ R
      lemma₂ = Eq.↔→≃
        (λ (f , ∥b∥) → f ∥b∥)
        (λ r → (λ _ → r) , inhabited r)
        refl
        (λ (f , ∥b∥) → cong₂ _,_
           (⟨ext⟩ λ ∥b∥′ →
              f ∥b∥   ≡⟨ cong f (truncation-is-proposition _ _) ⟩∎
              f ∥b∥′  ∎)
           (truncation-is-proposition _ _))

      lemma₃ = λ ∥b∥ →
        (∃ λ (f : B → A) → ∥ set ⁻¹ f ∥)                                ↝⟨ ∃-cong (lemma₁ ∥b∥) ⟩

        (∃ λ (f : B → A) → ∀ b b′ → set (f b) b′ ≡ f b′)                ↝⟨ (Σ-cong (→-cong ext F.id l) λ f →
                                                                            ∀-cong ext λ b → ∀-cong ext λ b′ →
                                                                            ≡⇒↝ _ $ cong (_≃_.from l (proj₁ (_≃_.to l (f b)) , b′) ≡_) $ sym $
                                                                            _≃_.left-inverse-of l _) ⟩
        (∃ λ (f : B → R × B) →
           ∀ b b′ → _≃_.from l (proj₁ (f b) , b′) ≡ _≃_.from l (f b′))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                            Eq.≃-≡ (inverse l)) ⟩

        (∃ λ (f : B → R × B) → ∀ b b′ → (proj₁ (f b) , b′) ≡ f b′)      ↔⟨ (Σ-cong ΠΣ-comm λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                            inverse $ ≡×≡↔≡) ⟩
        (∃ λ ((f , g) : (B → R) × (B → B)) →
           ∀ b b′ → f b ≡ f b′ × b′ ≡ g b′)                             ↔⟨ (Σ-assoc F.∘
                                                                            (∃-cong λ _ →
                                                                             ∃-comm F.∘
                                                                             ∃-cong λ _ →
                                                                             ΠΣ-comm F.∘
                                                                             ∀-cong ext λ _ →
                                                                             ΠΣ-comm) F.∘
                                                                            inverse Σ-assoc) ⟩
        ((∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → B → ∀ b → b ≡ g b))                         ↔⟨ (∃-cong $ uncurry λ f _ → ∃-cong λ _ → inverse $
                                                                            →-intro ext (λ b → B-set (_≃_.from l (f b , b)))) ⟩
        ((∃ λ (f : B → R) → Constant f) ×
         (∃ λ (g : B → B) → ∀ b → b ≡ g b))                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                            Eq.extensionality-isomorphism ext) ⟩

        ((∃ λ (f : B → R) → Constant f) × (∃ λ (g : B → B) → id ≡ g))   ↔⟨ (drop-⊤-right λ _ →
                                                                            _⇔_.to contractible⇔↔⊤ $
                                                                            other-singleton-contractible _) ⟩

        (∃ λ (f : B → R) → Constant f)                                  ↝⟨ constant-function≃∥inhabited∥⇒inhabited R-set ⟩□

        (∥ B ∥ → R)                                                     □

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

-- The split surjection above preserves getters and setters.

Lens↠Traditional-lens-preserves-getters-and-setters :
  {A : Type a}
  (b : Block "conversion")
  (s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_↠_.logical-equivalence (Lens↠Traditional-lens b s))
Lens↠Traditional-lens-preserves-getters-and-setters ⊠ _ =
  (λ _ → refl _ , refl _) , (λ _ → refl _ , refl _)

-- If the domain A is a set, then Traditional.Lens A B and Lens A B
-- are isomorphic (assuming univalence).

Lens↔Traditional-lens :
  {A : Type a} {B : Type b} →
  Block "conversion" →
  Univalence (a ⊔ b) →
  Is-set A →
  Lens A B ↔ Traditional.Lens A B
Lens↔Traditional-lens bc univ A-set =
  Lens↔Traditional-lens.iso A-set bc univ

-- The isomorphism preserves getters and setters.

Lens↔Traditional-lens-preserves-getters-and-setters :
  {A : Type a} {B : Type b}
  (bc : Block "conversion")
  (univ : Univalence (a ⊔ b))
  (s : Is-set A) →
  Preserves-getters-and-setters-⇔ A B
    (_↔_.logical-equivalence (Lens↔Traditional-lens bc univ s))
Lens↔Traditional-lens-preserves-getters-and-setters bc _ =
  Lens↠Traditional-lens-preserves-getters-and-setters bc

-- If the codomain B is an inhabited set, then Lens A B and
-- Traditional.Lens A B are logically equivalent.
--
-- This definition is inspired by the statement of Corollary 13 from
-- "Algebras and Update Strategies" by Johnson, Rosebrugh and Wood.
--
-- See also Lens.Non-dependent.Equivalent-preimages.coherent↠higher.

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
    (A                               ↔⟨ Traditional.≃get⁻¹× B-set b₀ l ⟩□
     (∃ λ (a : A) → get a ≡ b₀) × B  □)
    where
    open Traditional.Lens l

-- The logical equivalence preserves getters and setters.

Lens⇔Traditional-lens-preserves-getters-and-setters :
  {B : Type b}
  (s : Is-set B)
  (b₀ : B) →
  Preserves-getters-and-setters-⇔ A B (Lens⇔Traditional-lens s b₀)
Lens⇔Traditional-lens-preserves-getters-and-setters _ b₀ =
    (λ _ → refl _ , refl _)
  , (λ l → refl _
         , ⟨ext⟩ λ a → ⟨ext⟩ λ b →
           set l (set l a b₀) b  ≡⟨ set-set l _ _ _ ⟩∎
           set l a b             ∎)
  where
  open Traditional.Lens

------------------------------------------------------------------------
-- Some results related to h-levels

-- If the domain of a lens is inhabited and has h-level n, then the
-- codomain also has h-level n.

h-level-respects-lens-from-inhabited :
  ∀ n → Lens A B → A → H-level n A → H-level n B
h-level-respects-lens-from-inhabited n =
  Traditional.h-level-respects-lens-from-inhabited n ∘
  Lens.traditional-lens

-- This is not necessarily true for arbitrary domains (assuming
-- univalence).

¬-h-level-respects-lens :
  Univalence lzero →
  ¬ (∀ n → Lens ⊥₀ Bool → H-level n ⊥₀ → H-level n Bool)
¬-h-level-respects-lens univ resp =
                       $⟨ ⊥-propositional ⟩
  Is-proposition ⊥     ↝⟨ resp 1 (_↔_.from (lens-from-⊥↔⊤ univ) _) ⟩
  Is-proposition Bool  ↝⟨ ¬-Bool-propositional ⟩□
  ⊥                    □

-- In fact, there is a lens with a proposition as its domain and a
-- non-set as its codomain (assuming univalence).
--
-- (The lemma does not actually use the univalence argument, but
-- univalence is used by Circle.¬-𝕊¹-set.)

lens-from-proposition-to-non-set :
  Univalence (# 0) →
  ∃ λ (A : Type a) → ∃ λ (B : Type b) →
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
  , Circle.¬-𝕊¹-set ∘
    H-level.respects-surjection (_↔_.surjection Bij.↑↔) 2

-- Lenses with contractible domains have contractible codomains.

contractible-to-contractible :
  Lens A B → Contractible A → Contractible B
contractible-to-contractible l c =
  h-level-respects-lens-from-inhabited _ l (proj₁ c) c

-- If the domain type of a lens has h-level n, then the remainder type
-- also has h-level n.

remainder-has-same-h-level-as-domain :
  (l : Lens A B) → ∀ n → H-level n A → H-level n (Lens.R l)
remainder-has-same-h-level-as-domain {A = A} {B = B} l n =
  H-level n A        ↝⟨ H-level.respects-surjection (_≃_.surjection equiv) n ⟩
  H-level n (R × B)  ↝⟨ H-level-×₁ inhabited n ⟩□
  H-level n R        □
  where
  open Lens l

-- If the getter function is an equivalence, then the remainder type
-- is propositional.

get-equivalence→remainder-propositional :
  (l : Lens A B) →
  Is-equivalence (Lens.get l) →
  Is-proposition (Lens.R l)
get-equivalence→remainder-propositional {B = B} l =
  Is-equivalence (get l)  ↔⟨ get-equivalence≃remainder≃∥codomain∥ l ⟩
  R l ≃ ∥ B ∥             ↝⟨ ≃∥∥→Is-proposition ⟩□
  Is-proposition (R l)    □
  where
  open Lens

-- If the getter function is pointwise equal to the identity
-- function, then the remainder type is propositional.

get≡id→remainder-propositional :
  (l : Lens A A) →
  (∀ a → Lens.get l a ≡ a) →
  Is-proposition (Lens.R l)
get≡id→remainder-propositional l =
  (∀ a → Lens.get l a ≡ a)     ↝⟨ (λ hyp → Eq.respects-extensional-equality (sym ∘ hyp) (_≃_.is-equivalence F.id)) ⟩
  Is-equivalence (Lens.get l)  ↝⟨ get-equivalence→remainder-propositional l ⟩□
  Is-proposition (Lens.R l)    □

-- It is not necessarily the case that contractibility of A implies
-- contractibility of Lens A B (assuming univalence).

¬-Contractible-closed-domain :
  ∀ {a b} →
  Univalence (a ⊔ b) →
  ¬ ({A : Type a} {B : Type b} →
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
  {A : Type a} {B : Type b} →
  Univalence (a ⊔ b) →
  Contractible B → Contractible (Lens A B)
Contractible-closed-codomain {A = A} {B} univ cB =
                           $⟨ lens-to-contractible↔⊤ univ cB ⟩
  Lens A B ↔ ⊤             ↝⟨ _⇔_.from contractible⇔↔⊤ ⟩□
  Contractible (Lens A B)  □

-- If B is a proposition, then Lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-codomain :
  {A : Type a} {B : Type b} →
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
    {A : Type a} {B : Type b} →
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
                                                                     (_↔_.surjection $ inverse $ equality-characterisation₃ univ)
                                                                     n ⟩□
    H-level n (l₁ ≡ l₂)                                         □
    where
    open Lens

-- If A is a proposition, then Lens A B is also a proposition
-- (assuming univalence).

Is-proposition-closed-domain :
  {A : Type a} {B : Type b} →
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
  remainder⁻¹ l r = Trunc.rec
    A-prop
    (λ b → _≃_.from (equiv l) (r , b))
    (inhabited l r)

  R-to-R : (l₁ l₂ : Lens A B) → R l₁ → R l₂
  R-to-R l₁ l₂ = remainder l₂ ∘ remainder⁻¹ l₁

  involutive : (l : Lens A B) {f : R l → R l} → ∀ r → f r ≡ r
  involutive l _ = R-prop l _ _

  R₁≃R₂ : (l₁ l₂ : Lens A B) → R l₁ ≃ R l₂
  R₁≃R₂ l₁ l₂ = Eq.↔⇒≃ $
    Bij.bijection-from-involutive-family
      R-to-R (λ l _ → involutive l) l₁ l₂

-- An alternative proof.

Is-proposition-closed-domain′ :
  {A : Type a} {B : Type b} →
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
  {A : Type a} {B : Type b} →
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
-- See also
-- Lens.Non-dependent.Higher.Coinductive.Small.lens-preserves-h-level-of-domain.

domain-0+⇒lens-1+ :
  {A : Type a} {B : Type b} →
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
  {A : Type a} {B : Type b} →
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
  ¬ Lens (∃ λ (b : Bool) → b ≡ true) Bool
no-first-projection-lens =
  Non-dependent.no-first-projection-lens
    Lens contractible-to-contractible

------------------------------------------------------------------------
-- Equal lenses can be "observably different"

-- An example based on one presented in "Shattered lens" by Oleg
-- Grenrus.
--
-- Grenrus states that there are two lenses with equal getters and
-- setters that are "observably different".

-- A lemma used to construct the two lenses of the example.

grenrus-example : (Bool → Bool ↔ Bool) → Lens (Bool × Bool) Bool
grenrus-example eq = record
  { R         = Bool
  ; inhabited = ∣_∣
  ; equiv     = Bool × Bool  ↔⟨ ×-cong₁ eq ⟩□
                Bool × Bool  □
  }

-- The two lenses.

grenrus-example₁ = grenrus-example (if_then F.id else Bool.swap)
grenrus-example₂ = grenrus-example (if_then Bool.swap else F.id)

-- The two lenses have equal setters.

set-grenrus-example₁≡set-grenrus-example₂ :
  Lens.set grenrus-example₁ ≡ Lens.set grenrus-example₂
set-grenrus-example₁≡set-grenrus-example₂ = ⟨ext⟩ (⟨ext⟩ ∘ lemma)
  where
  lemma : ∀ _ _ → _
  lemma (true  , true)  true  = refl _
  lemma (true  , true)  false = refl _
  lemma (true  , false) true  = refl _
  lemma (true  , false) false = refl _
  lemma (false , true)  true  = refl _
  lemma (false , true)  false = refl _
  lemma (false , false) true  = refl _
  lemma (false , false) false = refl _

-- Thus the lenses are equal (assuming univalence).

grenrus-example₁≡grenrus-example₂ :
  Univalence lzero →
  grenrus-example₁ ≡ grenrus-example₂
grenrus-example₁≡grenrus-example₂ univ =
  lenses-with-inhabited-codomains-equal-if-setters-equal
    univ _ _ true
    set-grenrus-example₁≡set-grenrus-example₂

-- However, in a certain sense the lenses are "observably different".

grenrus-example₁-true :
  Lens.remainder grenrus-example₁ (true , true) ≡ true
grenrus-example₁-true = refl _

grenrus-example₂-false :
  Lens.remainder grenrus-example₂ (true , true) ≡ false
grenrus-example₂-false = refl _

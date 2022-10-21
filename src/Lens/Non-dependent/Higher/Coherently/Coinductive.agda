------------------------------------------------------------------------
-- The coinductive type family Coherently
------------------------------------------------------------------------

-- This type family is used to define the lenses in
-- Lens.Non-dependent.Higher.Coinductive and
-- Lens.Non-dependent.Higher.Coinductive.Small.

{-# OPTIONS --cubical --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coherently.Coinductive
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Equality.Path.Univalence as EPU
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
import Bijection P.equality-with-J as PB
open import Container.Indexed equality-with-J
open import Container.Indexed.Coalgebra equality-with-J
open import Container.Indexed.M.Codata eq
import Container.Indexed.M.Function equality-with-J as F
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
  using () renaming (abstract-univ to univ)
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
import Extensionality P.equality-with-J as PExt
open import Function-universe equality-with-J hiding (id; _∘_)
import Function-universe P.equality-with-J as PF
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹; ∣_∣)
open import Univalence-axiom equality-with-J
import Univalence-axiom P.equality-with-J as PU

import Lens.Non-dependent.Higher.Coherently.Not-coinductive eq as NC

private
  variable
    a b ℓ p p₁ p₂ : Level
    A A₁ A₂ B C   : Type a
    f q x y       : A
    n             : ℕ

------------------------------------------------------------------------
-- The type family

-- Coherently P step f means that f and all variants of f built using
-- step (in a certain way) satisfy the property P.
--
-- Paolo Capriotti came up with a coinductive definition of lenses.
-- Andrea Vezzosi suggested that one could use a kind of indexed
-- M-type to make it easier to prove that two variants of coinductive
-- lenses are equivalent: the lemma Coherently-cong-≡ below is based
-- on his idea, and Coherently is a less general variant of the M-type
-- that he suggested. See also Coherently-with-restriction′ below,
-- which is defined as an indexed M-type.

record Coherently
         {A : Type a} {B : Type b}
         (P : {A : Type a} → (A → B) → Type p)
         (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B)
         (f : A → B) : Type p where
  coinductive
  field
    property : P f
    coherent : Coherently P step (step f property)

open Coherently public

------------------------------------------------------------------------
-- An equivalence

-- Coherently is pointwise equivalent to NC.Coherently.

Coherently≃Not-coinductive-coherently :
  {B : Type b}
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B}
  {f : A → B} →
  Coherently P step f ≃ NC.Coherently P step f
Coherently≃Not-coinductive-coherently
  {a = a} {B = B} {P = P} {step = step} {f = f} =
  block λ b →

  Coherently P step f     ↝⟨ Eq.↔→≃ to from
                               (_↔_.from ≡↔≡ ∘ to-from)
                               (_↔_.from ≡↔≡ ∘ from-to) ⟩
  M (CC step) (_ , f)     ↝⟨ carriers-of-final-coalgebras-equivalent
                               (M-coalgebra (CC step) , M-final univ univ)
                               (F.M-coalgebra b ext (CC step) , F.M-final b ext ext)
                               _ ⟩
  F.M (CC step) (_ , f)   ↔⟨⟩
  NC.Coherently P step f  □
  where
  CC = NC.Coherently-container P

  to :
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} {f : A → B} →
    Coherently P step f → M (CC step) (_ , f)
  to c .out-M .proj₁   = c .property
  to c .out-M .proj₂ _ = to (c .coherent)

  from :
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} {f : A → B} →
    M (CC step) (_ , f) → Coherently P step f
  from c .property = c .out-M .proj₁
  from c .coherent = from (c .out-M .proj₂ _)

  to-from :
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} {f : A → B} →
    (c : M (CC step) (_ , f)) →
    to (from c) P.≡ c
  to-from c i .out-M .proj₁   = c .out-M .proj₁
  to-from c i .out-M .proj₂ _ = to-from (c .out-M .proj₂ _) i

  from-to :
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} {f : A → B} →
    (c : Coherently P step f) →
    from (to c) P.≡ c
  from-to c i .property = c .property
  from-to c i .coherent = from-to (c .coherent) i

------------------------------------------------------------------------
-- Preservation lemmas

private

  -- A preservation lemma for Coherently.

  Coherently-cong-≡ :
    Block "Coherently-cong-≡" →
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
    ({A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherently P₁ step₁ f P.≡ Coherently P₂ step₂ f
  Coherently-cong-≡
    {a = a} {B = B} {p = p} {f = f} ⊠ {P₁ = P₁} {P₂ = P₂}
    {step₁ = step₁} {step₂ = step₂} P₁≃P₂′ step₁≡step₂ =

    P.cong (λ ((P , step) :
              ∃ λ (P : (A : Type a) → (A → B) → Type p) →
                  {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ → B) →
             Coherently (P _) step f) $

    P.Σ-≡,≡→≡′

      (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
       EPU.≃⇒≡ (P₁≃P₂ f))

      (PExt.implicit-extensionality P.ext λ A → P.⟨ext⟩ λ f →
         P.subst (λ P → {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            EPU.≃⇒≡ (P₁≃P₂ f))
           step₁ f                                                      P.≡⟨ P.trans (P.cong (_$ f) $ P.sym $
                                                                                      P.push-subst-implicit-application
                                                                                        (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → EPU.≃⇒≡ (P₁≃P₂ f))
                                                                                        (λ P A → (f : A → B) → P A f → ∥ A ∥¹ → B)
                                                                                        {f = const _} {g = step₁}) $
                                                                             P.sym $ P.push-subst-application
                                                                                       (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → EPU.≃⇒≡ (P₁≃P₂ f))
                                                                                       (λ P f → P A f → ∥ A ∥¹ → B)
                                                                                       {f = const f} {g = step₁} ⟩
         P.subst (λ P → P A f → ∥ A ∥¹ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            EPU.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                    P.≡⟨⟩

         P.subst (λ P → P → ∥ A ∥¹ → B)
           (EPU.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                    P.≡⟨ P.sym $
                                                                             PU.transport-theorem
                                                                               (λ P → P → ∥ A ∥¹ → B)
                                                                               (PF.→-cong₁ _)
                                                                               (λ _ → P.refl)
                                                                               EPU.univ
                                                                               (P₁≃P₂ f)
                                                                               (step₁ f) ⟩
         PF.→-cong₁ _ (P₁≃P₂ f) (step₁ f)                               P.≡⟨⟩

         step₁ f ∘ PEq._≃_.from (P₁≃P₂ f)                               P.≡⟨ P.⟨ext⟩ (_↔_.to ≡↔≡ ∘ step₁≡step₂ f) ⟩∎

         step₂ f                                                        ∎)
    where
    P₁≃P₂ : (f : A → B) → P₁ f PEq.≃ P₂ f
    P₁≃P₂ f = _↔_.to ≃↔≃ (P₁≃P₂′ f)

  -- A "computation rule".

  to-Coherently-cong-≡-property :
    (bl : Block "Coherently-cong-≡")
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherently P₁ step₁ f) →
    PU.≡⇒→ (Coherently-cong-≡ bl P₁≃P₂ step₁≡step₂) c .property P.≡
    _≃_.to (P₁≃P₂ f) (c .property)
  to-Coherently-cong-≡-property
    {f = f} ⊠ {P₁ = P₁} {P₂ = P₂} P₁≃P₂ step₁≡step₂ c =

    P.transport (λ _ → P₂ f) P.0̲
      (_≃_.to (P₁≃P₂ f) (P.transport (λ _ → P₁ f) P.0̲ (c .property)))  P.≡⟨ P.cong (_$ _≃_.to (P₁≃P₂ f)
                                                                                             (P.transport (λ _ → P₁ f) P.0̲ (c .property))) $
                                                                                P.transport-refl P.0̲ ⟩

    _≃_.to (P₁≃P₂ f) (P.transport (λ _ → P₁ f) P.0̲ (c .property))      P.≡⟨ P.cong (λ g → _≃_.to (P₁≃P₂ f) (g (c .property))) $
                                                                                P.transport-refl P.0̲ ⟩∎
    _≃_.to (P₁≃P₂ f) (c .property)                                     ∎

  -- Another "computation rule".

  from-Coherently-cong-≡-property :
    (bl : Block "Coherently-cong-≡")
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherently P₂ step₂ f) →
    PEq._≃_.from
      (PU.≡⇒≃ (Coherently-cong-≡ bl {step₁ = step₁} P₁≃P₂ step₁≡step₂))
      c .property P.≡
    _≃_.from (P₁≃P₂ f) (c .property)
  from-Coherently-cong-≡-property
    {f = f} ⊠ {P₁ = P₁} {P₂ = P₂} P₁≃P₂ step₁≡step₂ c =

    P.transport (λ _ → P₁ f) P.0̲
      (_≃_.from (P₁≃P₂ f) (P.transport (λ _ → P₂ f) P.0̲ (c .property)))  P.≡⟨ P.cong (_$ _≃_.from (P₁≃P₂ f)
                                                                                           (P.transport (λ _ → P₂ f) P.0̲ (c .property))) $
                                                                              P.transport-refl P.0̲ ⟩

    _≃_.from (P₁≃P₂ f) (P.transport (λ _ → P₂ f) P.0̲ (c .property))      P.≡⟨ P.cong (λ g → _≃_.from (P₁≃P₂ f) (g (c .property))) $
                                                                              P.transport-refl P.0̲ ⟩∎
    _≃_.from (P₁≃P₂ f) (c .property)                                     ∎

  -- A preservation lemma for Coherently.
  --
  -- The two directions of this equivalence compute the property
  -- fields in certain ways, see the "unit tests" below.
  --
  -- Note that P₁ and P₂ have to target the same universe. A more
  -- general result is given below (Coherently-cong).

  Coherently-cong-≃ :
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
    ({A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherently P₁ step₁ f ≃ Coherently P₂ step₂ f
  Coherently-cong-≃
    {f = f} {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂}
    P₁≃P₂ step₁≡step₂ =

    block λ bl →
    Eq.with-other-inverse
      (Eq.with-other-function
         (equiv bl)
         (to bl)
         (_↔_.from ≡↔≡ ∘ ≡to bl))
      (from bl)
      (_↔_.from ≡↔≡ ∘ ≡from bl)

    where

    equiv :
      Block "Coherently-cong-≡" →
      Coherently P₁ step₁ f ≃ Coherently P₂ step₂ f
    equiv bl =
      _↔_.from ≃↔≃ $ PU.≡⇒≃ $
      Coherently-cong-≡ bl P₁≃P₂ step₁≡step₂

    to :
      Block "Coherently-cong-≡" →
      Coherently P₁ step₁ f → Coherently P₂ step₂ f
    to _  c .property = _≃_.to (P₁≃P₂ f) (c .property)
    to bl c .coherent =
      P.subst
        (Coherently P₂ step₂)
        (P.cong (step₂ f) $
         to-Coherently-cong-≡-property bl P₁≃P₂ step₁≡step₂ c) $
      _≃_.to (equiv bl) c .coherent

    ≡to : ∀ bl c → _≃_.to (equiv bl) c P.≡ to bl c
    ≡to bl c i .property = to-Coherently-cong-≡-property
                             bl P₁≃P₂ step₁≡step₂ c i
    ≡to bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherently P₂ step₂
                     (step₂ f
                        (to-Coherently-cong-≡-property
                           bl P₁≃P₂ step₁≡step₂ c i))) ]
          _≃_.to (equiv bl) c .coherent ≡
          P.subst
            (Coherently P₂ step₂)
            (P.cong (step₂ f) $
             to-Coherently-cong-≡-property bl P₁≃P₂ step₁≡step₂ c)
            (_≃_.to (equiv bl) c .coherent)
      lemma =
        PB._↔_.from (P.heterogeneous↔homogeneous _) P.refl

    from :
      Block "Coherently-cong-≡" →
      Coherently P₂ step₂ f → Coherently P₁ step₁ f
    from _  c .property = _≃_.from (P₁≃P₂ f) (c .property)
    from bl c .coherent =
      P.subst
        (Coherently P₁ step₁)
        (P.cong (step₁ f) $
         from-Coherently-cong-≡-property bl P₁≃P₂ step₁≡step₂ c) $
      _≃_.from (equiv bl) c .coherent

    ≡from : ∀ bl c → _≃_.from (equiv bl) c P.≡ from bl c
    ≡from bl c i .property = from-Coherently-cong-≡-property
                               bl P₁≃P₂ step₁≡step₂ c i
    ≡from bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherently P₁ step₁
                     (step₁ f
                        (from-Coherently-cong-≡-property
                           bl P₁≃P₂ step₁≡step₂ c i))) ]
          _≃_.from (equiv bl) c .coherent ≡
          P.subst
            (Coherently P₁ step₁)
            (P.cong (step₁ f) $
             from-Coherently-cong-≡-property bl P₁≃P₂ step₁≡step₂ c)
            (_≃_.from (equiv bl) c .coherent)
      lemma =
        PB._↔_.from (P.heterogeneous↔homogeneous _) P.refl

  -- Unit tests that ensure that Coherently-cong-≃ computes the
  -- property fields in certain ways.

  module _
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f}
    {step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x}
    where

    _ :
      {c : Coherently P₁ step₁ f} →
      _≃_.to (Coherently-cong-≃ P₁≃P₂ step₁≡step₂) c .property ≡
      _≃_.to (P₁≃P₂ f) (c .property)
    _ = refl _

    _ :
      {c : Coherently P₂ step₂ f} →
      _≃_.from (Coherently-cong-≃ {step₁ = step₁} P₁≃P₂ step₁≡step₂)
        c .property ≡
      _≃_.from (P₁≃P₂ f) (c .property)
    _ = refl _

  -- A lemma involving Coherently and ↑.

  Coherently-↑ :
    {P : {A : Type a} → (A → B) → Type p}
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} →
    Coherently (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f ≃
    Coherently P step f
  Coherently-↑ {ℓ = ℓ} {P = P} {step = step} =
    Eq.↔→≃
      to
      from
      (_↔_.from ≡↔≡ ∘ to-from)
      (_↔_.from ≡↔≡ ∘ from-to)
    where
    to :
      Coherently (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f →
      Coherently P step f
    to c .property = lower (c .property)
    to c .coherent = to (c .coherent)

    from :
      Coherently P step f →
      Coherently (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f
    from c .property = lift (c .property)
    from c .coherent = from (c .coherent)

    to-from :
      (c : Coherently P step f) →
      to (from c) P.≡ c
    to-from c i .property = c .property
    to-from c i .coherent = to-from (c .coherent) i

    from-to :
      (c : Coherently (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f) →
      from (to c) P.≡ c
    from-to c i .property = c .property
    from-to c i .coherent = from-to (c .coherent) i

-- A preservation lemma for Coherently.
--
-- The two directions of this equivalence compute the property
-- fields in certain ways, see the "unit tests" below.

Coherently-cong :
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
  {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
  (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
  ({A : Type a} (f : A → B) (x : P₂ f) →
   step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
  Coherently P₁ step₁ f ≃ Coherently P₂ step₂ f
Coherently-cong
  {p₁ = p₁} {p₂ = p₂} {f = f}
  {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂}
  P₁≃P₂ step₁≡step₂ =

  Coherently P₁ step₁ f                          ↝⟨ inverse Coherently-↑ ⟩

  Coherently (↑ p₂ ∘ P₁) ((_∘ lower) ∘ step₁) f  ↝⟨ Coherently-cong-≃
                                                      (λ f →
    ↑ p₂ (P₁ f)                                          ↔⟨ B.↑↔ ⟩
    P₁ f                                                 ↝⟨ P₁≃P₂ f ⟩
    P₂ f                                                 ↔⟨ inverse B.↑↔ ⟩□
    ↑ p₁ (P₂ f)                                          □)
                                                      ((_∘ lower) ∘ step₁≡step₂) ⟩

  Coherently (↑ p₁ ∘ P₂) ((_∘ lower) ∘ step₂) f  ↝⟨ Coherently-↑ ⟩□

  Coherently P₂ step₂ f                          □

-- Unit tests that ensure that Coherently-cong computes the
-- property fields in certain ways.

module _
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
  {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
  {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f}
  {step₁≡step₂ :
     {A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x}
  where

  _ :
    {c : Coherently P₁ step₁ f} →
    _≃_.to (Coherently-cong P₁≃P₂ step₁≡step₂) c .property ≡
    _≃_.to (P₁≃P₂ f) (c .property)
  _ = refl _

  _ :
    {c : Coherently P₂ step₂ f} →
    _≃_.from (Coherently-cong {step₁ = step₁} P₁≃P₂ step₁≡step₂)
      c .property ≡
    _≃_.from (P₁≃P₂ f) (c .property)
  _ = refl _

-- Another preservation lemma for Coherently.

Coherently-cong′ :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} →
  (A₁≃A₂ : A₁ ≃ A₂) →
  Coherently P step (f ∘ _≃_.to A₁≃A₂) ≃ Coherently P step f
Coherently-cong′ {f = f} {P = P} {step = step} A₁≃A₂ =
  ≃-elim₁ univ
    (λ A₁≃A₂ →
       Coherently P step (f ∘ _≃_.to A₁≃A₂) ≃
       Coherently P step f)
    Eq.id
    A₁≃A₂

------------------------------------------------------------------------
-- Another lemma

-- A "computation rule".

subst-Coherently-property :
  ∀ {A : C → Type a} {B : Type b}
    {P : C → {A : Type a} → (A → B) → Type p}
    {step : (c : C) {A : Type a} (f : A → B) → P c f → ∥ A ∥¹ → B}
    {f : (c : C) → A c → B} {eq : x ≡ y} {c} →
  subst (λ x → Coherently (P x) (step x) (f x)) eq c .property ≡
  subst (λ x → P x (f x)) eq (c .property)
subst-Coherently-property
  {P = P} {step = step} {f = f} {eq = eq} {c = c} =
  elim¹
    (λ eq →
       subst (λ x → Coherently (P x) (step x) (f x)) eq c .property ≡
       subst (λ x → P x (f x)) eq (c .property))
    (subst (λ x → Coherently (P x) (step x) (f x)) (refl _) c .property  ≡⟨ cong property $ subst-refl _ _ ⟩
     c .property                                                         ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → P x (f x)) (refl _) (c .property)                      ∎)
    eq

------------------------------------------------------------------------
-- Coherently-with-restriction

-- A variant of Coherently. An extra predicate Q is included, so that
-- one can restrict the "f" functions (and their domains).

record Coherently-with-restriction
         {A : Type a} {B : Type b}
         (P : {A : Type a} → (A → B) → Type p)
         (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B)
         (f : A → B)
         (Q : {A : Type a} → (A → B) → Type q)
         (pres : {A : Type a} {f : A → B} {p : P f} →
                 Q f → Q (step f p))
         (q : Q f) : Type p where
  coinductive
  field
    property : P f
    coherent :
      Coherently-with-restriction
        P step (step f property)
        Q pres (pres q)

open Coherently-with-restriction public

-- Coherently P step f is equivalent to
-- Coherently-with-restriction P step f Q pres q.

Coherently≃Coherently-with-restriction :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B}
  {Q : {A : Type a} → (A → B) → Type q}
  {pres : {A : Type a} {f : A → B} {p : P f} → Q f → Q (step f p)}
  {q : Q f} →
  Coherently P step f ≃ Coherently-with-restriction P step f Q pres q
Coherently≃Coherently-with-restriction
  {P = P} {step = step} {Q = Q} {pres = pres} =
  Eq.↔→≃ to (from _)
    (λ c → _↔_.from ≡↔≡ (to-from c))
    (λ c → _↔_.from ≡↔≡ (from-to _ c))
  where
  to :
    Coherently P step f →
    Coherently-with-restriction P step f Q pres q
  to c .property = c .property
  to c .coherent = to (c .coherent)

  from :
    ∀ q →
    Coherently-with-restriction P step f Q pres q →
    Coherently P step f
  from _ c .property = c .property
  from _ c .coherent = from _ (c .coherent)

  to-from :
    (c : Coherently-with-restriction P step f Q pres q) →
    to (from q c) P.≡ c
  to-from c i .property = c .property
  to-from c i .coherent = to-from (c .coherent) i

  from-to : ∀ q (c : Coherently P step f) → from q (to c) P.≡ c
  from-to _ c i .property = c .property
  from-to q c i .coherent = from-to (pres q) (c .coherent) i

-- A container that is used to define Coherently-with-restriction′.

Coherently-with-restriction-container :
  {B : Type b}
  (P : {A : Type a} → (A → B) → Type p)
  (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B) →
  (Q : {A : Type a} → (A → B) → Type q) →
  ({A : Type a} {f : A → B} {p : P f} → Q f → Q (step f p)) →
  Container (∃ λ (A : Type a) → ∃ λ (f : A → B) → Q f) p lzero
Coherently-with-restriction-container P step _ pres = λ where
  .Shape (_ , f , _)               → P f
  .Position _                      → ⊤
  .index {o = A , f , q} {s = p} _ → ∥ A ∥¹ , step f p , pres q

-- A variant of Coherently-with-restriction, defined using an indexed
-- container.

Coherently-with-restriction′ :
  {A : Type a} {B : Type b}
  (P : {A : Type a} → (A → B) → Type p)
  (step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B) →
  (f : A → B) →
  (Q : {A : Type a} → (A → B) → Type q) →
  ({A : Type a} {f : A → B} {p : P f} → Q f → Q (step f p)) →
  Q f →
  Type (lsuc a ⊔ b ⊔ p ⊔ q)
Coherently-with-restriction′ P step f Q pres q =
  M (Coherently-with-restriction-container P step Q pres) (_ , f , q)

-- Coherently-with-restriction P step f Q pres q is equivalent to
-- Coherently-with-restriction′ P step f Q pres q.

Coherently-with-restriction≃Coherently-with-restriction′ :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B}
  {Q : {A : Type a} → (A → B) → Type q}
  {pres : {A : Type a} {f : A → B} {p : P f} → Q f → Q (step f p)}
  {q : Q f} →
  Coherently-with-restriction P step f Q pres q ≃
  Coherently-with-restriction′ P step f Q pres q
Coherently-with-restriction≃Coherently-with-restriction′
  {P = P} {step = step} {Q = Q} {pres = pres} =
  Eq.↔→≃ to (from _)
    (λ c → _↔_.from ≡↔≡ (to-from _ c))
    (λ c → _↔_.from ≡↔≡ (from-to c))
  where
  to :
    Coherently-with-restriction P step f Q pres q →
    Coherently-with-restriction′ P step f Q pres q
  to c .out-M .proj₁   = c .property
  to c .out-M .proj₂ _ = to (c .coherent)

  from :
    ∀ q →
    Coherently-with-restriction′ P step f Q pres q →
    Coherently-with-restriction P step f Q pres q
  from _ c .property = c .out-M .proj₁
  from _ c .coherent = from _ (c .out-M .proj₂ _)

  to-from :
    ∀ q (c : Coherently-with-restriction′ P step f Q pres q) →
    to (from q c) P.≡ c
  to-from _ c i .out-M .proj₁   = c .out-M .proj₁
  to-from q c i .out-M .proj₂ _ = to-from (pres q) (c .out-M .proj₂ _) i

  from-to :
    (c : Coherently-with-restriction P step f Q pres q) →
    from q (to c) P.≡ c
  from-to c i .property = c .property
  from-to c i .coherent = from-to (c .coherent) i

------------------------------------------------------------------------
-- H-levels

-- I think that Paolo Capriotti suggested that one could prove that
-- certain instances of Coherently have certain h-levels by using the
-- result (due to Ahrens, Capriotti and Spadotti, see "Non-wellfounded
-- trees in Homotopy Type Theory") that M-types for indexed containers
-- have h-level n if all shapes have h-level n. The use of containers
-- with "restrictions" is my idea.

-- If P f has h-level n for every function f for which Q holds, then
-- Coherently-with-restriction P step f Q pres q has h-level n.

H-level-Coherently-with-restriction :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B}
  {Q : {A : Type a} → (A → B) → Type q}
  {pres : {A : Type a} {f : A → B} {p : P f} → Q f → Q (step f p)}
  {q : Q f} →
  ({A : Type a} {f : A → B} → Q f → H-level n (P f)) →
  H-level n (Coherently-with-restriction P step f Q pres q)
H-level-Coherently-with-restriction
  {B = B} {f = f} {n = n} {P = P} {step = step} {Q = Q}
  {pres = pres} {q = q} =

  (∀ {A} {f : A → B} → Q f → H-level n (P f))                        ↝⟨ (λ h (_ , _ , q) → h q) ⟩
  (((_ , f , _) : ∃ λ A → ∃ λ (f : A → B) → Q f) → H-level n (P f))  ↝⟨ (λ h → H-level-M univ univ h) ⟩
  H-level n (Coherently-with-restriction′ P step f Q pres q)         ↝⟨ H-level-cong _ n
                                                                          (inverse Coherently-with-restriction≃Coherently-with-restriction′) ⟩□
  H-level n (Coherently-with-restriction P step f Q pres q)          □

-- If P f has h-level n, and (for any f and p) P (step f p) has
-- h-level n when P f has h-level n, then Coherently P step f has
-- h-level n.

H-level-Coherently :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} →
  H-level n (P f) →
  ({A : Type a} {f : A → B} {p : P f} →
   H-level n (P f) → H-level n (P (step f p))) →
  H-level n (Coherently P step f)
H-level-Coherently {n = n} {f = f} {P = P} {step = step} h₁ h₂ =
                                            $⟨ H-level-Coherently-with-restriction id ⟩
  H-level n
    (Coherently-with-restriction P step f
       (λ f → H-level n (P f)) h₂ h₁)       ↝⟨ H-level-cong _ n (inverse Coherently≃Coherently-with-restriction) ⦂ (_ → _) ⟩□

  H-level n (Coherently P step f)           □

-- A variant of H-level-Coherently for type-valued functions.

H-level-Coherently-→Type :
  {P : {A : Type a} → (A → Type f) → Type p}
  {step : {A : Type a} (F : A → Type f) → P F → ∥ A ∥¹ → Type f}
  {F : A → Type f} →
  ((a : A) → H-level n (F a)) →
  ({A : Type a} {F : A → Type f} →
   ((a : A) → H-level n (F a)) → H-level n (P F)) →
  ({A : Type a} {F : A → Type f} {p : P F} →
   ((a : A) → H-level n (F a)) →
   (a : A) → H-level n (step F p ∣ a ∣)) →
  H-level n (Coherently P step F)
H-level-Coherently-→Type
  {a = a} {f = f} {n = n} {P = P} {step = step} {F = F} h₁ h₂ h₃ =
                                              $⟨ H-level-Coherently-with-restriction h₂ ⟩
  H-level n
    (Coherently-with-restriction P step F
       (λ F → ∀ a → H-level n (F a)) h₃′ h₁)  ↝⟨ H-level-cong _ n (inverse Coherently≃Coherently-with-restriction) ⦂ (_ → _) ⟩□

  H-level n (Coherently P step F)             □
  where
  h₃′ :
    {F : A → Type f} {p : P F} →
    ((a : A) → H-level n (F a)) →
    (a : ∥ A ∥¹) → H-level n (step F p a)
  h₃′ h = O.elim λ where
    .O.∣∣ʳ              → h₃ h
    .O.∣∣-constantʳ _ _ → H-level-propositional ext n _ _

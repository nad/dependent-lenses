------------------------------------------------------------------------
-- The coinductive type family Coherently
------------------------------------------------------------------------

-- This type family is used to define the lenses in
-- Lens.Non-dependent.Higher.Coinductive and
-- Lens.Non-dependent.Higher.Coinductive.Small.

{-# OPTIONS --cubical --safe --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coinductive.Coherently
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J as B using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
open import Function-universe equality-with-J hiding (_∘_)
import Function-universe P.equality-with-J as PF
open import H-level.Truncation.Propositional.One-step eq using (∥_∥¹)
import Univalence-axiom P.equality-with-J as PU

private
  variable
    a b ℓ p p₁ p₂ : Level
    A B C         : Type a
    x y           : A
    f             : A → B

-- Coherently P step f means that f and all variants of f built using
-- step (in a certain way) satisfy the property P.
--
-- Paolo Capriotti came up with a coinductive definition of lenses.
-- Andrea Vezzosi suggested that one could use a kind of indexed
-- M-type to make it easier to prove that two variants of coinductive
-- lenses are equivalent: the lemma Coherently-cong-≡ below is based
-- on his idea, and Coherently is a less general variant of the M-type
-- that he suggested.

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

private

  -- A preservation lemma for Coherently.
  --
  -- The lemma does not use the univalence argument, instead it uses
  -- P.univ directly.

  Coherently-cong-≡ :
    Block "Coherently-cong-≡" →
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {f : A → B} →
    PU.Univalence p →
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
    ({A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherently P₁ step₁ f P.≡ Coherently P₂ step₂ f
  Coherently-cong-≡
    {a = a} {B = B} {p = p} ⊠ {P₁ = P₁} {P₂ = P₂}
    {step₁ = step₁} {step₂ = step₂} {f = f} _ P₁≃P₂′ step₁≡step₂ =

    P.cong (λ ((P , step) :
              ∃ λ (P : (A : Type a) → (A → B) → Type p) →
                  {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ → B) →
             Coherently (P _) step f) $

    Σ-≡,≡→≡′

      (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
       P.≃⇒≡ (P₁≃P₂ f))

      (P.implicit-extensionality P.ext λ A → P.⟨ext⟩ λ f →
         P.subst (λ P → {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            P.≃⇒≡ (P₁≃P₂ f))
           step₁ f                                                      P.≡⟨ P.trans (P.cong (_$ f) $ P.sym $
                                                                                      P.push-subst-implicit-application
                                                                                        (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → P.≃⇒≡ (P₁≃P₂ f))
                                                                                        (λ P A → (f : A → B) → P A f → ∥ A ∥¹ → B)
                                                                                        {f = const _} {g = step₁}) $
                                                                             P.sym $ P.push-subst-application
                                                                                       (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → P.≃⇒≡ (P₁≃P₂ f))
                                                                                       (λ P f → P A f → ∥ A ∥¹ → B)
                                                                                       {f = const f} {g = step₁} ⟩
         P.subst (λ P → P A f → ∥ A ∥¹ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            P.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                    P.≡⟨⟩

         P.subst (λ P → P → ∥ A ∥¹ → B)
           (P.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                    P.≡⟨ P.sym $
                                                                             PU.transport-theorem
                                                                               (λ P → P → ∥ A ∥¹ → B)
                                                                               (PF.→-cong₁ _)
                                                                               (λ _ → P.refl)
                                                                               P.univ
                                                                               (P₁≃P₂ f)
                                                                               (step₁ f) ⟩
         PF.→-cong₁ _ (P₁≃P₂ f) (step₁ f)                               P.≡⟨⟩

         step₁ f ∘ PEq._≃_.from (P₁≃P₂ f)                               P.≡⟨ P.⟨ext⟩ (_↔_.to ≡↔≡ ∘ step₁≡step₂ f) ⟩∎

         step₂ f                                                        ∎)
    where
    P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f PEq.≃ P₂ f
    P₁≃P₂ f = _↔_.to ≃↔≃ (P₁≃P₂′ f)

    Σ-≡,≡→≡′ :
      {P : A → Type b} {p₁ p₂ : Σ A P} →
      (p : proj₁ p₁ P.≡ proj₁ p₂) →
      P.subst P p (proj₂ p₁) P.≡ proj₂ p₂ →
      p₁ P.≡ p₂
    Σ-≡,≡→≡′ {P = P} {p₁ = _ , y₁} {p₂ = _ , y₂} p q i =
      p i , lemma i
      where
      lemma : P.[ (λ i → P (p i)) ] y₁ ≡ y₂
      lemma = PB._↔_.from (P.heterogeneous↔homogeneous _) q

  -- A "computation rule".

  to-Coherently-cong-≡-property :
    (bl : Block "Coherently-cong-≡")
    {A : Type a} {B : Type b}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {f : A → B}
    (univ : PU.Univalence p)
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherently P₁ step₁ f) →
    PU.≡⇒→ (Coherently-cong-≡ bl univ P₁≃P₂ step₁≡step₂) c .property P.≡
    _≃_.to (P₁≃P₂ f) (c .property)
  to-Coherently-cong-≡-property
    ⊠ {P₁ = P₁} {P₂ = P₂} {f = f} _ P₁≃P₂ step₁≡step₂ c =

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
    {A : Type a} {B : Type b}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {f : A → B}
    (univ : PU.Univalence p)
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherently P₂ step₂ f) →
    PEq._≃_.from
      (PU.≡⇒≃ (Coherently-cong-≡ bl {step₁ = step₁} univ
                 P₁≃P₂ step₁≡step₂))
      c .property P.≡
    _≃_.from (P₁≃P₂ f) (c .property)
  from-Coherently-cong-≡-property
    ⊠ {P₁ = P₁} {P₂ = P₂} {f = f} _ P₁≃P₂ step₁≡step₂ c =

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
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {f : A → B} →
    PU.Univalence p →
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
    ({A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherently P₁ step₁ f ≃ Coherently P₂ step₂ f
  Coherently-cong-≃
    {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂} {f = f}
    univ P₁≃P₂ step₁≡step₂ =

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
      Coherently-cong-≡ bl univ P₁≃P₂ step₁≡step₂

    to :
      Block "Coherently-cong-≡" →
      Coherently P₁ step₁ f → Coherently P₂ step₂ f
    to _  c .property = _≃_.to (P₁≃P₂ f) (c .property)
    to bl c .coherent =
      P.subst
        (Coherently P₂ step₂)
        (P.cong (step₂ f) $
         to-Coherently-cong-≡-property bl univ P₁≃P₂ step₁≡step₂ c) $
      _≃_.to (equiv bl) c .coherent

    ≡to : ∀ bl c → _≃_.to (equiv bl) c P.≡ to bl c
    ≡to bl c i .property = to-Coherently-cong-≡-property
                             bl univ P₁≃P₂ step₁≡step₂ c i
    ≡to bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherently P₂ step₂
                     (step₂ f
                        (to-Coherently-cong-≡-property
                           bl univ P₁≃P₂ step₁≡step₂ c i))) ]
          _≃_.to (equiv bl) c .coherent ≡
          P.subst
            (Coherently P₂ step₂)
            (P.cong (step₂ f) $
             to-Coherently-cong-≡-property bl univ P₁≃P₂ step₁≡step₂ c)
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
         from-Coherently-cong-≡-property bl univ P₁≃P₂ step₁≡step₂ c) $
      _≃_.from (equiv bl) c .coherent

    ≡from : ∀ bl c → _≃_.from (equiv bl) c P.≡ from bl c
    ≡from bl c i .property = from-Coherently-cong-≡-property
                               bl univ P₁≃P₂ step₁≡step₂ c i
    ≡from bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherently P₁ step₁
                     (step₁ f
                        (from-Coherently-cong-≡-property
                           bl univ P₁≃P₂ step₁≡step₂ c i))) ]
          _≃_.from (equiv bl) c .coherent ≡
          P.subst
            (Coherently P₁ step₁)
            (P.cong (step₁ f) $
             from-Coherently-cong-≡-property
               bl univ P₁≃P₂ step₁≡step₂ c)
            (_≃_.from (equiv bl) c .coherent)
      lemma =
        PB._↔_.from (P.heterogeneous↔homogeneous _) P.refl

  -- Unit tests that ensure that Coherently-cong-≃ computes the
  -- property fields in certain ways.

  module _
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
    {f : A → B}
    {univ : PU.Univalence p}
    {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f}
    {step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x}
    where

    _ :
      {c : Coherently P₁ step₁ f} →
      _≃_.to (Coherently-cong-≃ univ P₁≃P₂ step₁≡step₂) c .property ≡
      _≃_.to (P₁≃P₂ f) (c .property)
    _ = refl _

    _ :
      {c : Coherently P₂ step₂ f} →
      _≃_.from (Coherently-cong-≃ {step₁ = step₁} univ
                  P₁≃P₂ step₁≡step₂)
        c .property ≡
      _≃_.from (P₁≃P₂ f) (c .property)
    _ = refl _

  -- A lemma involving Coherently and ↑.

  Coherently-↑ :
    {A : Type a}
    {P : {A : Type a} → (A → B) → Type p}
    {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B}
    {f : A → B} →
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
  {A : Type a}
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
  {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
  {f : A → B} →
  PU.Univalence (p₁ ⊔ p₂) →
  (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
  ({A : Type a} (f : A → B) (x : P₂ f) →
   step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
  Coherently P₁ step₁ f ≃ Coherently P₂ step₂ f
Coherently-cong
  {p₁ = p₁} {p₂ = p₂}
  {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂} {f = f}
  univ P₁≃P₂ step₁≡step₂ =

  Coherently P₁ step₁ f                          ↝⟨ inverse Coherently-↑ ⟩

  Coherently (↑ p₂ ∘ P₁) ((_∘ lower) ∘ step₁) f  ↝⟨ Coherently-cong-≃
                                                      univ
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
  {A : Type a}
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ → B}
  {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ → B}
  {f : A → B}
  {univ : PU.Univalence (p₁ ⊔ p₂)}
  {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f}
  {step₁≡step₂ :
     {A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x}
  where

  _ :
    {c : Coherently P₁ step₁ f} →
    _≃_.to (Coherently-cong univ P₁≃P₂ step₁≡step₂) c .property ≡
    _≃_.to (P₁≃P₂ f) (c .property)
  _ = refl _

  _ :
    {c : Coherently P₂ step₂ f} →
    _≃_.from (Coherently-cong {step₁ = step₁} univ P₁≃P₂ step₁≡step₂)
      c .property ≡
    _≃_.from (P₁≃P₂ f) (c .property)
  _ = refl _

-- A "computation rule".

subst-Coherently-property :
  ∀ {B : Type b} {P : C → {A : Type a} → (A → B) → Type p}
    {step : (c : C) {A : Type a} (f : A → B) → P c f → ∥ A ∥¹ → B}
    {f : C → A → B} {eq : x ≡ y} {c} →
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

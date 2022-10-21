------------------------------------------------------------------------
-- A variant of Coherently with an erased field
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

import Equality.Path as P

module Lens.Non-dependent.Higher.Coherently.Coinductive.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Equality.Path.Univalence as EPU
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
  using () renaming (abstract-univ to univ)
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
open import Equivalence.Erased equality-with-J as EEq using (_≃ᴱ_)
import Extensionality P.equality-with-J as PExt
open import Function-universe equality-with-J hiding (_∘_)
import Function-universe P.equality-with-J as PF
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹; ∥∥¹ᴱ→∥∥¹)
open import H-level.Truncation.Propositional.One-step.Erased eq as OE
  using (∥_∥¹ᴱ)
open import Univalence-axiom equality-with-J
import Univalence-axiom P.equality-with-J as PU

open import Lens.Non-dependent.Higher.Coherently.Coinductive eq as C
  using (Coherently)

private
  variable
    a b ℓ p p₁ p₂ : Level
    A A₁ A₂ B C   : Type a
    x y           : A
    f             : A → B

-- A variant of
-- Lens.Non-dependent.Higher.Coherently.Coinductive.Coherently with an
-- erased "coherent" field.

record Coherentlyᴱ
         {A : Type a} {B : Type b}
         (P : {A : Type a} → (A → B) → Type p)
         (@0 step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ᴱ → B)
         (f : A → B) : Type p where
  coinductive
  field
    property    : P f
    @0 coherent : Coherentlyᴱ P step (step f property)

open Coherentlyᴱ public

-- A preservation lemma for Coherentlyᴱ. (See also Coherentlyᴱ-cong
-- below.)

@0 Coherentlyᴱ-cong′ :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ᴱ → B} →
  (A₁≃A₂ : A₁ ≃ A₂) →
  Coherentlyᴱ P step (f ∘ _≃_.to A₁≃A₂) ≃ Coherentlyᴱ P step f
Coherentlyᴱ-cong′ {f = f} {P = P} {step = step} A₁≃A₂ =
  ≃-elim₁ univ
    (λ A₁≃A₂ →
       Coherentlyᴱ P step (f ∘ _≃_.to A₁≃A₂) ≃
       Coherentlyᴱ P step f)
    Eq.id
    A₁≃A₂

-- In erased contexts Coherently and Coherentlyᴱ are, in a certain
-- sense, logically equivalent.

@0 Coherentlyᴱ⇔Coherently :
  {P : {A : Type a} → (A → B) → Type p}
  {step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ → B} →
  Coherentlyᴱ P (λ f p → step f p ∘ ∥∥¹ᴱ→∥∥¹) f ⇔ Coherently P step f
Coherentlyᴱ⇔Coherently ._⇔_.from c .property = c .C.property
Coherentlyᴱ⇔Coherently ._⇔_.from c .coherent =
  Coherentlyᴱ⇔Coherently ._⇔_.from
    (_≃_.from (C.Coherently-cong′ O.∥∥¹ᴱ≃∥∥¹) (c .C.coherent))

Coherentlyᴱ⇔Coherently ._⇔_.to c .C.property = c .property
Coherentlyᴱ⇔Coherently ._⇔_.to c .C.coherent =
  Coherentlyᴱ⇔Coherently ._⇔_.to
    (_≃_.to (Coherentlyᴱ-cong′ O.∥∥¹ᴱ≃∥∥¹)
       (c .coherent))

private

  -- A preservation lemma for Coherentlyᴱ.

  @0 Coherentlyᴱ-cong-≡ :
    Block "Coherentlyᴱ-cong-≡" →
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
    {f : A → B} →
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f) →
    ({A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherentlyᴱ P₁ step₁ f P.≡ Coherentlyᴱ P₂ step₂ f
  Coherentlyᴱ-cong-≡
    {a = a} {B = B} {p = p} ⊠ {P₁ = P₁} {P₂ = P₂}
    {step₁ = step₁} {step₂ = step₂} {f = f} P₁≃P₂′ step₁≡step₂ =

    P.cong (λ ((P , step) :
              ∃ λ (P : (A : Type a) → (A → B) → Type p) →
                  {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ᴱ → B) →
             Coherentlyᴱ (P _) step f) $

    Σ-≡,≡→≡′

      (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
       EPU.≃⇒≡ (P₁≃P₂ f))

      (PExt.implicit-extensionality P.ext λ A → P.⟨ext⟩ λ f →
         P.subst (λ P → {A : Type a} (f : A → B) → P A f → ∥ A ∥¹ᴱ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            EPU.≃⇒≡ (P₁≃P₂ f))
           step₁ f                                                       P.≡⟨ P.trans (P.cong (_$ f) $ P.sym $
                                                                                       P.push-subst-implicit-application
                                                                                         (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → EPU.≃⇒≡ (P₁≃P₂ f))
                                                                                         (λ P A → (f : A → B) → P A f → ∥ A ∥¹ᴱ → B)
                                                                                         {f = const _} {g = step₁}) $
                                                                              P.sym $ P.push-subst-application
                                                                                        (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) → EPU.≃⇒≡ (P₁≃P₂ f))
                                                                                        (λ P f → P A f → ∥ A ∥¹ᴱ → B)
                                                                                        {f = const f} {g = step₁} ⟩
         P.subst (λ P → P A f → ∥ A ∥¹ᴱ → B)
           (P.⟨ext⟩ λ A → P.⟨ext⟩ λ (f : A → B) →
            EPU.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                     P.≡⟨⟩

         P.subst (λ P → P → ∥ A ∥¹ᴱ → B)
           (EPU.≃⇒≡ (P₁≃P₂ f))
           (step₁ f)                                                     P.≡⟨ P.sym $
                                                                              PU.transport-theorem
                                                                                (λ P → P → ∥ A ∥¹ᴱ → B)
                                                                                (PF.→-cong₁ _)
                                                                                (λ _ → P.refl)
                                                                                EPU.univ
                                                                                (P₁≃P₂ f)
                                                                                (step₁ f) ⟩
         PF.→-cong₁ _ (P₁≃P₂ f) (step₁ f)                                P.≡⟨⟩

         step₁ f ∘ PEq._≃_.from (P₁≃P₂ f)                                P.≡⟨ P.⟨ext⟩ (_↔_.to ≡↔≡ ∘ step₁≡step₂ f) ⟩∎

         step₂ f                                                         ∎)
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

  to-Coherentlyᴱ-cong-≡-property :
    (bl : Block "Coherentlyᴱ-cong-≡")
    {A : Type a} {B : Type b}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
    {f : A → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherentlyᴱ P₁ step₁ f) →
    PU.≡⇒→ (Coherentlyᴱ-cong-≡ bl P₁≃P₂ step₁≡step₂) c .property
      P.≡
    _≃_.to (P₁≃P₂ f) (c .property)
  to-Coherentlyᴱ-cong-≡-property
    ⊠ {P₁ = P₁} {P₂ = P₂} {f = f} P₁≃P₂ step₁≡step₂ c =

    P.transport (λ _ → P₂ f) P.0̲
      (_≃_.to (P₁≃P₂ f) (P.transport (λ _ → P₁ f) P.0̲ (c .property)))  P.≡⟨ P.cong (_$ _≃_.to (P₁≃P₂ f)
                                                                                         (P.transport (λ _ → P₁ f) P.0̲ (c .property))) $
                                                                            P.transport-refl P.0̲ ⟩

    _≃_.to (P₁≃P₂ f) (P.transport (λ _ → P₁ f) P.0̲ (c .property))      P.≡⟨ P.cong (λ g → _≃_.to (P₁≃P₂ f) (g (c .property))) $
                                                                            P.transport-refl P.0̲ ⟩∎
    _≃_.to (P₁≃P₂ f) (c .property)                                     ∎

  -- Another "computation rule".

  from-Coherentlyᴱ-cong-≡-property :
    (bl : Block "Coherentlyᴱ-cong-≡")
    {A : Type a} {B : Type b}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
    {step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
    {f : A → B}
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ P₂ f)
    (step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃_.from (P₁≃P₂ f) x) ≡ step₂ f x)
    (c : Coherentlyᴱ P₂ step₂ f) →
    PEq._≃_.from
      (PU.≡⇒≃ (Coherentlyᴱ-cong-≡ bl {step₁ = step₁} P₁≃P₂ step₁≡step₂))
      c .property P.≡
    _≃_.from (P₁≃P₂ f) (c .property)
  from-Coherentlyᴱ-cong-≡-property
    ⊠ {P₁ = P₁} {P₂ = P₂} {f = f} P₁≃P₂ step₁≡step₂ c =

    P.transport (λ _ → P₁ f) P.0̲
      (_≃_.from (P₁≃P₂ f) (P.transport (λ _ → P₂ f) P.0̲ (c .property)))  P.≡⟨ P.cong (_$ _≃_.from (P₁≃P₂ f)
                                                                                           (P.transport (λ _ → P₂ f) P.0̲ (c .property))) $
                                                                              P.transport-refl P.0̲ ⟩

    _≃_.from (P₁≃P₂ f) (P.transport (λ _ → P₂ f) P.0̲ (c .property))      P.≡⟨ P.cong (λ g → _≃_.from (P₁≃P₂ f) (g (c .property))) $
                                                                              P.transport-refl P.0̲ ⟩∎
    _≃_.from (P₁≃P₂ f) (c .property)                                     ∎

  -- A preservation lemma for Coherentlyᴱ.
  --
  -- The two directions of this equivalence compute the property
  -- fields in certain ways, see the "unit tests" below.
  --
  -- Note that P₁ and P₂ have to target the same universe. A more
  -- general result is given below (Coherentlyᴱ-cong).

  Coherentlyᴱ-cong-≃ᴱ :
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {@0 step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
    {@0 step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
    {f : A → B} →
    (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ᴱ P₂ f) →
    @0 ({A : Type a} (f : A → B) (x : P₂ f) →
        step₁ f (_≃ᴱ_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
    Coherentlyᴱ P₁ step₁ f ≃ᴱ Coherentlyᴱ P₂ step₂ f
  Coherentlyᴱ-cong-≃ᴱ
    {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂} {f = f}
    P₁≃P₂ step₁≡step₂ =

    block λ bl →
    EEq.[≃]→≃ᴱ
      (EEq.[proofs]
         (Eq.with-other-inverse
            (Eq.with-other-function
               (equiv bl)
               (to bl)
               (_↔_.from ≡↔≡ ∘ ≡to bl))
            (from bl)
            (_↔_.from ≡↔≡ ∘ ≡from bl)))

    where

    @0 equiv :
      Block "Coherentlyᴱ-cong-≡" →
      Coherentlyᴱ P₁ step₁ f ≃ Coherentlyᴱ P₂ step₂ f
    equiv bl =
      _↔_.from ≃↔≃ $ PU.≡⇒≃ $
      Coherentlyᴱ-cong-≡ bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂

    to :
      Block "Coherentlyᴱ-cong-≡" →
      Coherentlyᴱ P₁ step₁ f → Coherentlyᴱ P₂ step₂ f
    to _  c .property = _≃ᴱ_.to (P₁≃P₂ f) (c .property)
    to bl c .coherent =
      P.subst
        (Coherentlyᴱ P₂ step₂)
        (P.cong (step₂ f) $
         to-Coherentlyᴱ-cong-≡-property
           bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂ c) $
      _≃_.to (equiv bl) c .coherent

    @0 ≡to : ∀ bl c → _≃_.to (equiv bl) c P.≡ to bl c
    ≡to bl c i .property = to-Coherentlyᴱ-cong-≡-property
                             bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂ c i
    ≡to bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherentlyᴱ P₂ step₂
                     (step₂ f (to-Coherentlyᴱ-cong-≡-property
                                 bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂)
                                 step₁≡step₂ c i))) ]
          _≃_.to (equiv bl) c .coherent ≡
          P.subst
            (Coherentlyᴱ P₂ step₂)
            (P.cong (step₂ f) $
             to-Coherentlyᴱ-cong-≡-property
               bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂ c)
            (_≃_.to (equiv bl) c .coherent)
      lemma =
        PB._↔_.from (P.heterogeneous↔homogeneous _) P.refl

    from :
      Block "Coherentlyᴱ-cong-≡" →
      Coherentlyᴱ P₂ step₂ f → Coherentlyᴱ P₁ step₁ f
    from _  c .property = _≃ᴱ_.from (P₁≃P₂ f) (c .property)
    from bl c .coherent =
      P.subst
        (Coherentlyᴱ P₁ step₁)
        (P.cong (step₁ f) $
         from-Coherentlyᴱ-cong-≡-property
           bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂ c) $
      _≃_.from (equiv bl) c .coherent

    @0 ≡from : ∀ bl c → _≃_.from (equiv bl) c P.≡ from bl c
    ≡from bl c i .property = from-Coherentlyᴱ-cong-≡-property
                               bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂)
                               step₁≡step₂ c i
    ≡from bl c i .coherent = lemma i
      where
      lemma :
        P.[ (λ i → Coherentlyᴱ P₁ step₁
                     (step₁ f (from-Coherentlyᴱ-cong-≡-property
                                 bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂)
                                 step₁≡step₂ c i))) ]
          _≃_.from (equiv bl) c .coherent ≡
          P.subst
            (Coherentlyᴱ P₁ step₁)
            (P.cong (step₁ f) $
             from-Coherentlyᴱ-cong-≡-property
               bl (EEq.≃ᴱ→≃ ∘ P₁≃P₂) step₁≡step₂ c)
            (_≃_.from (equiv bl) c .coherent)
      lemma =
        PB._↔_.from (P.heterogeneous↔homogeneous _) P.refl

  -- Unit tests that ensure that Coherentlyᴱ-cong-≃ᴱ computes the
  -- property fields in certain ways.

  module _
    {A : Type a}
    {P₁ P₂ : {A : Type a} → (A → B) → Type p}
    {@0 step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
    {@0 step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
    {f : A → B}
    {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ᴱ P₂ f}
    {@0 step₁≡step₂ :
       {A : Type a} (f : A → B) (x : P₂ f) →
       step₁ f (_≃ᴱ_.from (P₁≃P₂ f) x) ≡ step₂ f x}
    where

    _ :
      {c : Coherentlyᴱ P₁ step₁ f} →
      _≃ᴱ_.to (Coherentlyᴱ-cong-≃ᴱ P₁≃P₂ step₁≡step₂) c .property ≡
      _≃ᴱ_.to (P₁≃P₂ f) (c .property)
    _ = refl _

    _ :
      {c : Coherentlyᴱ P₂ step₂ f} →
      _≃ᴱ_.from (Coherentlyᴱ-cong-≃ᴱ {step₁ = step₁} P₁≃P₂ step₁≡step₂)
        c .property ≡
      _≃ᴱ_.from (P₁≃P₂ f) (c .property)
    _ = refl _

  -- A lemma involving Coherentlyᴱ and ↑.

  Coherentlyᴱ-↑ :
    {A : Type a}
    {P : {A : Type a} → (A → B) → Type p}
    {@0 step : {A : Type a} (f : A → B) → P f → ∥ A ∥¹ᴱ → B}
    {f : A → B} →
    Coherentlyᴱ (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f ≃
    Coherentlyᴱ P step f
  Coherentlyᴱ-↑ {ℓ = ℓ} {P = P} {step = step} =
    Eq.↔→≃
      to
      from
      (_↔_.from ≡↔≡ ∘ to-from)
      (_↔_.from ≡↔≡ ∘ from-to)
    where
    to :
      Coherentlyᴱ (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f →
      Coherentlyᴱ P step f
    to c .property = lower (c .property)
    to c .coherent = to (c .coherent)

    from :
      Coherentlyᴱ P step f →
      Coherentlyᴱ (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f
    from c .property = lift (c .property)
    from c .coherent = from (c .coherent)

    to-from :
      (c : Coherentlyᴱ P step f) →
      to (from c) P.≡ c
    to-from c i .property = c .property
    to-from c i .coherent = to-from (c .coherent) i

    from-to :
      (c : Coherentlyᴱ (↑ ℓ ∘ P) ((_∘ lower) ∘ step) f) →
      from (to c) P.≡ c
    from-to c i .property = c .property
    from-to c i .coherent = from-to (c .coherent) i

-- A preservation lemma for Coherentlyᴱ.
--
-- The two directions of this equivalence compute the property
-- fields in certain ways, see the "unit tests" below.

Coherentlyᴱ-cong :
  {A : Type a}
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {@0 step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
  {@0 step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
  {f : A → B} →
  (P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ᴱ P₂ f) →
  @0 ({A : Type a} (f : A → B) (x : P₂ f) →
      step₁ f (_≃ᴱ_.from (P₁≃P₂ f) x) ≡ step₂ f x) →
  Coherentlyᴱ P₁ step₁ f ≃ᴱ Coherentlyᴱ P₂ step₂ f
Coherentlyᴱ-cong
  {p₁ = p₁} {p₂ = p₂}
  {P₁ = P₁} {P₂ = P₂} {step₁ = step₁} {step₂ = step₂} {f = f}
  P₁≃P₂ step₁≡step₂ =

  Coherentlyᴱ P₁ step₁ f                          ↔⟨ inverse Coherentlyᴱ-↑ ⟩

  Coherentlyᴱ (↑ p₂ ∘ P₁) ((_∘ lower) ∘ step₁) f  ↝⟨ Coherentlyᴱ-cong-≃ᴱ
                                                       (λ f →
    ↑ p₂ (P₁ f)                                           ↔⟨ B.↑↔ ⟩
    P₁ f                                                  ↝⟨ P₁≃P₂ f ⟩
    P₂ f                                                  ↔⟨ inverse B.↑↔ ⟩□
    ↑ p₁ (P₂ f)                                           □)
                                                       ((_∘ lower) ∘ step₁≡step₂) ⟩

  Coherentlyᴱ (↑ p₁ ∘ P₂) ((_∘ lower) ∘ step₂) f  ↔⟨ Coherentlyᴱ-↑ ⟩□

  Coherentlyᴱ P₂ step₂ f                          □

-- Unit tests that ensure that Coherentlyᴱ-cong computes the property
-- fields in certain ways.

module _
  {A : Type a}
  {P₁ : {A : Type a} → (A → B) → Type p₁}
  {P₂ : {A : Type a} → (A → B) → Type p₂}
  {@0 step₁ : {A : Type a} (f : A → B) → P₁ f → ∥ A ∥¹ᴱ → B}
  {@0 step₂ : {A : Type a} (f : A → B) → P₂ f → ∥ A ∥¹ᴱ → B}
  {f : A → B}
  {P₁≃P₂ : {A : Type a} (f : A → B) → P₁ f ≃ᴱ P₂ f}
  {@0 step₁≡step₂ :
     {A : Type a} (f : A → B) (x : P₂ f) →
     step₁ f (_≃ᴱ_.from (P₁≃P₂ f) x) ≡ step₂ f x}
  where

  _ :
    {c : Coherentlyᴱ P₁ step₁ f} →
    _≃ᴱ_.to (Coherentlyᴱ-cong P₁≃P₂ step₁≡step₂) c .property ≡
    _≃ᴱ_.to (P₁≃P₂ f) (c .property)
  _ = refl _

  _ :
    {c : Coherentlyᴱ P₂ step₂ f} →
    _≃ᴱ_.from (Coherentlyᴱ-cong {step₁ = step₁} P₁≃P₂ step₁≡step₂)
      c .property ≡
    _≃ᴱ_.from (P₁≃P₂ f) (c .property)
  _ = refl _

-- A "computation rule".

subst-Coherentlyᴱ-property :
  ∀ {B : Type b} {P : C → {A : Type a} → (A → B) → Type p}
    {@0 step : (c : C) {A : Type a} (f : A → B) → P c f → ∥ A ∥¹ᴱ → B}
    {f : C → A → B} {eq : x ≡ y} {c} →
  subst (λ x → Coherentlyᴱ (P x) (step x) (f x)) eq c .property ≡
  subst (λ x → P x (f x)) eq (c .property)
subst-Coherentlyᴱ-property
  {P = P} {step = step} {f = f} {eq = eq} {c = c} =
  elim¹
    (λ eq →
       subst (λ x → Coherentlyᴱ (P x) (step x) (f x)) eq c .property ≡
       subst (λ x → P x (f x)) eq (c .property))
    (subst (λ x → Coherentlyᴱ (P x) (step x) (f x)) (refl _) c .property  ≡⟨ cong property $ subst-refl _ _ ⟩
     c .property                                                          ≡⟨ sym $ subst-refl _ _ ⟩∎
     subst (λ x → P x (f x)) (refl _) (c .property)                       ∎)
    eq

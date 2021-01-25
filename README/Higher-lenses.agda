------------------------------------------------------------------------
-- Code related to the paper "Higher lenses" by Paolo Capriotti, Nils
-- Anders Danielsson and Andrea Vezzosi
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Most or all of the code referenced below can be found in modules
-- that are parametrised by a notion of equality. One can use them
-- both with Cubical Agda paths and with the Cubical Agda identity
-- type family.

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences.
--
-- An attempt has also been made to track uses of univalence by
-- passing around explicit proofs of the univalence axiom. However,
-- univalence is provable in Cubical Agda, and some library code that
-- is used does not adhere to this convention, so perhaps some use of
-- univalence is not tracked in this way. On the other hand some
-- library code that is not defined in Cubical Agda passes around
-- explicit proofs of function extensionality.
--
-- Some other differences are mentioned below.

{-# OPTIONS --cubical --safe #-}

module README.Higher-lenses where

import Category
import Circle
import Equality
import Equivalence
import Function-universe
import H-level
import H-level.Closure
import H-level.Truncation.Propositional
import Preimage
import Prelude
import Surjection

import Lens.Non-dependent.Bijection as B
import Lens.Non-dependent.Equivalent-preimages as P
import Lens.Non-dependent.Higher as H
import Lens.Non-dependent.Higher.Capriotti as HF
import Lens.Non-dependent.Higher.Erased as HE
import Lens.Non-dependent.Higher.Surjective-remainder as HR
import Lens.Non-dependent.Traditional as T
import Lens.Non-dependent.Traditional.Erased as TE

------------------------------------------------------------------------
-- 1: Introduction

-- Traditional lenses.

Traditional-lens = T.Lens

-- The function modify.

modify = T.Lens.modify

-- The cong function.
--
-- The axiomatisation of equality that is used makes it possible to
-- choose the implementation of cong. However, the implementation is
-- required to satisfy a property which implies that the definition is
-- unique.

cong        = Equality.Equality-with-J.cong
cong-refl   = Equality.Equality-with-J.cong-refl
cong-unique =
  Equality.Derived-definitions-and-properties.monomorphic-cong-canonical

-- The propositional truncation operator.

∥_∥ = H-level.Truncation.Propositional.∥_∥

-- Σ-types.
--
-- The code does not use the notation for Σ-types used in the paper.

Σ = Prelude.Σ
∃ = Prelude.∃

-- Equivalences.
--
-- The definition of _≃_ uses a record type instead of Σ.

_≃_            = Equivalence._≃_
Is-equivalence = Equivalence.Is-equivalence

------------------------------------------------------------------------
-- 2.1: Composition

-- Identity and composition.

id-traditional = T.Lens-combinators.id
∘-traditional  = T.Lens-combinators._∘_

-- Composition laws.

associativity-traditional  = T.Lens-combinators.associativity
left-identity-traditional  = T.Lens-combinators.left-identity
right-identity-traditional = T.Lens-combinators.right-identity

-- Lenses with definitionally equal getters and setters are equal if
-- the lens laws are pointwise equal.

equal-laws→≡ = T.equal-laws→≡

-- Alternative implementations of composition.

_∘′_ = T.Lens-combinators._∘′_
_∘″_ = T.Lens-combinators._∘″_

-- The alternative implementations are pointwise equal to _∘_.

∘≡∘′ = T.Lens-combinators.∘≡∘′
∘≡∘″ = T.Lens-combinators.∘≡∘″

------------------------------------------------------------------------
-- 2.2: Lenses with equal setters can be distinct

-- Lenses with equal setters have equal getters.

getters-equal-if-setters-equal = T.getters-equal-if-setters-equal

-- The circle.

𝕊¹ = Circle.𝕊¹

-- A function that is distinct from refl.

not-refl      = Circle.not-refl
not-refl≢refl = Circle.not-refl≢refl

-- The lens used for the counterexamples.

l = T.bad

-- Lemmas 6 and 7.

lemmas-6-and-7 = T.getter-equivalence-but-not-coherent

-- Split surjections.

_↠_ = Surjection._↠_

-- Lemma 8.

lemma-8 = T.¬-≃-↠-Σ-Lens-Is-equivalence-get

------------------------------------------------------------------------
-- 2.3: Homotopy levels

-- Homotopy levels.
--
-- The definitions are slightly different from the ones given in the
-- paper.

H-level        = H-level.H-level
Contractible   = Equality.Reflexive-relation′.Contractible
Is-proposition = Equality.Reflexive-relation′.Is-proposition
Is-set         = Equality.Reflexive-relation′.Is-set

-- Lemma 11.

lemma-11 = Function-universe.contractible↔≃⊤

-- H-level is upwards closed in its first argument.

H-level-upwards-closed = H-level.mono

-- The circle is not a set.

circle-not-set = Circle.¬-𝕊¹-set

-- Lemmas 14-16.

lemma-14 = T.h-level-respects-lens-from-inhabited
lemma-15 = T.contractible-to-contractible
lemma-16 = T.no-first-projection-lens

-- Lemma 16 for higher lenses.

lemma-16-for-higher = H.no-first-projection-lens

-- Lemmas 17-20.

lemma-17 = T.lens-preserves-h-level
lemma-18 = H-level.Closure.Σ-closure
lemma-19 = H-level.Closure.Π-closure
lemma-20 = T.lens-preserves-h-level-of-domain

------------------------------------------------------------------------
-- 2.4: Some equivalences

-- Lemmas 21-24.
--
-- The code uses a universe-polymorphic empty type.

lemma-21 = T.lens-to-proposition↔
lemma-22 = Equivalence.Σ-preserves
lemma-23 = T.lens-to-⊤↔
lemma-24 = T.lens-to-⊥↔

-- Traditional-lens 𝕊¹ ⊤ is not propositional.

Traditional-lens-𝕊¹-⊤-not-propositional = T.¬-lens-to-⊤-propositional

-- Lemmas 25-26.

lemma-25 = T.lens-from-⊤≃codomain-contractible
lemma-26 = T.lens-from-⊥≃⊤

-- Fibres.

_⁻¹_ = Preimage._⁻¹_

-- Lemma 28, and a variant of the lemma for lenses which satisfy
-- certain coherence laws.

lemma-28          = T.≃get⁻¹×
lemma-28-coherent = T.≃get⁻¹×-coherent

-- Lemma 29.

lemma-29 = T.≃Σ∥set⁻¹∥×

------------------------------------------------------------------------
-- 2.5: A category of lenses

-- Precategory and Category.
--
-- The definition of Precategory is a little different from the
-- definition in the paper.

Precategory = Category.Precategory
Category    = Category.Category

-- A precategory of lenses between sets in the same universe.

precategory-traditional = T.precategory

-- Isomorphisms between objects.

≅-precategory = Category.Precategory._≅_

-- Isomorphisms between types, expressed using lenses.

≅-lens = T._≅_

-- Lemmas 33-36.

lemma-33 = T.≅↠≃
lemma-34 = T.equality-characterisation-for-sets
lemma-35 = T.equality-characterisation-for-sets-≅
lemma-36 = T.≃≃≅
lemma-37 = T.≃≃≅-id≡id

-- A category of lenses between sets in the same universe.

category-traditional = T.category

------------------------------------------------------------------------
-- 2.6: Bi-invertibility

-- Is-bi-invertible and Has-quasi-inverse.
--
-- These functions are defined in a general way in a parametrised
-- module. The same applies to some other definitions below.

Is-bi-invertible-traditional = T.Is-bi-invertible
Has-quasi-inverse            = T.Has-quasi-inverse

-- Is-bi-invertible is propositional.

Is-bi-invertible-propositional = T.Is-bi-invertible-propositional

-- Has-quasi-inverse l is not necessarily propositional.

Has-quasi-inverse-not-propositional =
  T.Has-quasi-inverse-id-not-proposition

-- The relation _≊_, defined using traditional lenses.

≊-traditional = T._≊_

-- Lemmas 41-43.

lemma-41 = T.≊↠≃
lemma-42 = T.Is-bi-invertible≃Is-equivalence-get
lemma-43 = T.¬≃↠≊

------------------------------------------------------------------------
-- 3.1: Lenses based on bijections

-- Lenses based on bijections.

Bijection-lens = B.Lens

-- Lemma 45.

lemma-45 = B.Lens-⊥-⊥≃Type

------------------------------------------------------------------------
-- 3.2: A well-behaved variant of the lenses based on bijections

-- Higher lenses.
--
-- For performance reasons η-equality has been turned off for this
-- definition.

Higher-lens = H.Lens

-- Lemmas 47-48.

lemma-47 = H.isomorphism-to-lens
lemma-48 = H-level.Truncation.Propositional.∥∥×≃

-- The functions get, remainder and set.

get       = H.Lens.get
remainder = H.Lens.remainder
set       = H.Lens.set

-- Lemmas 52-55.

lemma-52 = H.Lens.get-set
lemma-53 = H.Lens.remainder-set
lemma-54 = H.Lens.set-get
lemma-55 = H.Lens.set-set

------------------------------------------------------------------------
-- 3.3: Coherence laws

-- Lemmas 56-60.

lemma-56 = H.Lens.get-set-get
lemma-57 = Equivalence._≃_.left-right-lemma
lemma-58 = Equivalence._≃_.right-left-lemma
lemma-59 = H.Lens.get-set-set
lemma-60 = Equality.Derived-definitions-and-properties.trans-symʳ

-- Lemma 61 is part of the axiomatisation of equality that is used.

lemma-61 = Equality.Derived-definitions-and-properties.cong-refl

------------------------------------------------------------------------
-- 3.4: Some equivalences

-- Lemmas 62-68.
--
-- Lemmas 63 and 65 are formulated slightly differently.

lemma-62 = H.lens-to-proposition↔get
lemma-63 = H.lens-to-contractible↔⊤
lemma-64 = H.lens-to-⊥↔¬
lemma-65 = H.lens-from-contractible↔codomain-contractible
lemma-66 = H.lens-from-⊥↔⊤
lemma-67 = H.get-equivalence≃inhabited-equivalence
lemma-68 = H.≃-≃-Σ-Lens-Is-equivalence-get

-- The right-to-left direction of Lemma 68 returns the lens's getter
-- (and some proof).

lemma-68-right-to-left = H.to-from-≃-≃-Σ-Lens-Is-equivalence-get≡get

-- Lemmas 69 and 70.

lemma-69 = H.remainder≃get⁻¹
lemma-70 = H.get⁻¹-constant

-- The functions get⁻¹-const and get⁻¹-const⁻¹.

get⁻¹-const   = H.get⁻¹-const
get⁻¹-const⁻¹ = H.get⁻¹-const⁻¹

-- Lemmas 73-75.

lemma-73 = H.get⁻¹-const-∘
lemma-74 = H.get⁻¹-const-inverse
lemma-75 = H.get⁻¹-const-id

------------------------------------------------------------------------
-- 3.5: Lenses with equal setters are sometimes equal

-- Lemmas 76-82.

lemma-76 = H.equality-characterisation₁
lemma-77 = H.equality-characterisation₂
lemma-78 = H.equality-characterisation₃
lemma-79 = H.lenses-with-inhabited-codomains-equal-if-setters-equal
lemma-80 = H.lenses-equal-if-setters-equal
lemma-81 = H.lenses-equal-if-setters-equal-and-remainder-propositional
lemma-82 = H.lenses-equal-if-setters-equal-and-remainder-set

------------------------------------------------------------------------
-- 3.6: Homotopy levels

-- Lemmas 83-89.

lemma-83 = H.h-level-respects-lens-from-inhabited
lemma-84 = H.remainder-has-same-h-level-as-domain
lemma-85 = H.get-equivalence→remainder-propositional
lemma-86 = H.Contractible-closed-codomain
lemma-87 = H.Is-proposition-closed-codomain
lemma-88 = H.domain-0+⇒lens-1+
lemma-89 = Equivalence.h-level-closure

------------------------------------------------------------------------
-- 3.7: Higher lenses are equivalent to traditional lenses for sets

-- Lemmas 90 and 91.
--
-- Lemma 91 takes an extra argument of type Unit, written as
-- Block "conversion". Some other definitions below also take such
-- arguments.

lemma-90 = H.¬Lens↠Traditional-lens
lemma-91 = H.Lens↔Traditional-lens

-- Lemma 91 preserves getters and setters in both directions.

lemma-91-preserves-get-and-set =
  H.Lens↔Traditional-lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- 3.8: Identity and composition

-- The identity lens.

id-higher = H.Lens-combinators.id

-- Lemma 93.

lemma-93 = H.Lens-combinators.id-unique

-- A composition operator for types in the same universe.

∘-higher = H.Lens-combinators._∘_

-- A more general composition operator.

∘-more-general = H.Lens-combinators.⟨_,_⟩_∘_

-- Composition laws.

associativity-higher  = H.Lens-combinators.associativity
left-identity-higher  = H.Lens-combinators.left-identity
right-identity-higher = H.Lens-combinators.right-identity

-- Lemma 95.
--
-- The lemma is formulated slightly differently.

lemma-95 = H.Lens-combinators.∘-unique

-- The composition operator produces lenses for which the setter
-- satisfies certain equations.

setter-correct = H.Lens-combinators.∘-set

-- Is-bi-invertible and _≊_.

Is-bi-invertible-higher = H.Is-bi-invertible
≊-higher                = H.[_]_≊_

-- Lemmas 98 and 99.

lemma-98 = H.≃≃≊
lemma-99 = H.Is-bi-invertible≃Is-equivalence-get

-- Lemma 98 maps bi-invertible lenses to their getter functions.

lemma-98-right-to-left = H.to-from-≃≃≊≡get

-- A precategory and a category of higher lenses between sets in the
-- same universe.

precategory-higher = H.precategory
category-higher    = H.category

-- The precategory of higher lenses is equal to the one for
-- traditional lenses (lifted), and similarly for the categories.

precategory≡precategory = H.precategory≡precategory
category≡category       = H.category≡category

------------------------------------------------------------------------
-- 3.9: Higher lenses with surjective remainder functions

-- Higher-lensᴿ.

Higher-lensᴿ = HR.Lens

-- Surjective.

Surjective = H-level.Truncation.Propositional.Surjective

-- Lemma 102.

lemma-102 = HR.Higher-lens↔Lens

------------------------------------------------------------------------
-- 3.10: Higher lenses where the family of fibres of the getter
-- factors through the propositional truncation

-- Higher-lens^F.

Higher-lens^F = HF.Lens

-- Lemma 104.

lemma-104 = HF.Lens.get⁻¹-≃

-- A setter.

set^F = HF.Lens.set

-- Lemma 106.

lemma-106 = HF.Lens≃Higher-lens

-- Lemma 106 preserves getters and setters in both directions.

lemma-106-preserves-get-and-set =
  HF.Lens≃Higher-lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- 3.11: Some results can be made a little stronger for stable types

-- Partial-lens.
--
-- For performance reasons η-equality has been turned off for this
-- definition.

Partial-lens = P.Lens

-- A translation from higher to partial lenses.

higher-to-partial = P.higher→

-- This translation preserves getters and setters.

higher-to-partial-preserves-get-and-set =
  P.higher→-preserves-getters-and-setters

-- Lemma 108.

lemma-108 = P.↠higher

-- Lemma 108 preserves getters and setters in both directions.

lemma-108-preserves-get-and-set =
  P.↠higher-preserves-getters-and-setters

-- Lemmas 109-113.

lemma-109 = P.lens-preserves-h-level
lemma-110 = P.lens-preserves-h-level-of-domain
lemma-111 = P.higher-lens-preserves-h-level-of-domain
lemma-112 = P._∘_
lemma-113 = P.⟨_⟩_⊚_

-- The composition operations of Lemmas 112 and 113 produce lenses for
-- which the setter satisfies certain equations.

setter-correct-112 = P.set-∘≡
setter-correct-113 = P.set-⊚≡

-- The composition operation of Lemma 113 matches ∘-higher when both
-- are defined.

composition-operations-match = P.⊚≡∘

------------------------------------------------------------------------
-- 4: Lenses with erased proofs

-- Lenses with erased proofs.

Traditional-lensᴱ = TE.Lens
Higher-lensᴱ      = HE.Lens

-- Lemma 116.

lemma-116 = HE.Lens≃ᴱTraditional-lens

-- For more results about lenses with erased proofs, see the following
-- modules:

import Lens.Non-dependent.Higher.Erased
import Lens.Non-dependent.Traditional.Erased

------------------------------------------------------------------------
-- 5: Related work

-- Lemmas 117-119.

lemma-117 = H.grenrus-example
lemma-118 = H.grenrus-example₁-true
lemma-119 = H.grenrus-example₂-false

-- The lenses used in Lemmas 118 and 119 are equal.

lenses-equal = H.grenrus-example₁≡grenrus-example₂

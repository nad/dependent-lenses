------------------------------------------------------------------------
-- Code related to the paper "Higher Lenses"
--
-- Nils Anders Danielsson
--
-- The paper is coauthored with Paolo Capriotti and Andrea Vezzosi.
------------------------------------------------------------------------

-- Most of the code referenced below can be found in modules that are
-- parametrised by a notion of equality. One can use them both with
-- Cubical Agda paths and with the Cubical Agda identity type family.

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences.

-- An attempt has also been made to track uses of univalence by
-- passing around explicit proofs of the univalence axiom (except in
-- README.Not-a-set). However, univalence is provable in Cubical Agda,
-- and some library code that is used does not adhere to this
-- convention, so perhaps some use of univalence is not tracked in
-- this way. On the other hand some library code that is not defined
-- in Cubical Agda passes around explicit proofs of function
-- extensionality.

-- Some other differences are mentioned below.

-- Note that there is a known problem with guarded corecursion in
-- Agda. Due to "quantifier inversion" certain types may not have the
-- expected semantics when the option --guardedness is used. I expect
-- that the results would still hold if this bug were fixed, but
-- because I do not know what the rules of a fixed version of Agda
-- would be I do not know if any changes to the code would be
-- required.

{-# OPTIONS --cubical --safe --guardedness #-}

module README.Higher-lenses where

import Circle
import Coherently-constant
import Equality
import Equality.Decidable-UIP
import Equivalence
import Equivalence.Half-adjoint
import Function-universe
import H-level
import H-level.Truncation.Propositional
import H-level.Truncation.Propositional.Non-recursive
import H-level.Truncation.Propositional.One-step
import Preimage
import Surjection

import Lens.Non-dependent.Bijection as B
import Lens.Non-dependent.Equivalent-preimages as EP
import Lens.Non-dependent.Higher as E
import Lens.Non-dependent.Higher.Capriotti as F
import Lens.Non-dependent.Higher.Coinductive as C
import Lens.Non-dependent.Higher.Coherently.Coinductive as Coh
import Lens.Non-dependent.Higher.Coherently.Not-coinductive as NC
import Lens.Non-dependent.Higher.Coinductive.Small as S
import Lens.Non-dependent.Higher.Combinators as EC
import Lens.Non-dependent.Traditional as T
import Lens.Non-dependent.Traditional.Combinators as TC

import README.Not-a-set

------------------------------------------------------------------------
-- I: Introduction

-- Traditional lenses.

Lensᵀ = T.Lens

-- The function modify.

modify = T.Lens.modify

-- The two variants of Tm, and proofs showing that Tm A is not a set
-- if A is inhabited.

Tm₁       = README.Not-a-set.Tm
¬-Tm₁-set = README.Not-a-set.¬-Tm-set
Tm₂       = README.Not-a-set.Tmˢ
¬-Tm₂-set = README.Not-a-set.¬-Tmˢ-set

------------------------------------------------------------------------
-- II: Homotopy type theory

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

-- Is-equivalence and _≃_.
--
-- Note that the syntax used for Σ-types in the paper is not valid
-- Agda syntax. Furthermore the code defines _≃_ as a record type
-- instead of using a Σ-type.

Is-equivalence = Equivalence.Half-adjoint.Is-equivalence
_≃_            = Equivalence._≃_

-- Lemma 6.

lemma-6 = Equivalence._≃_.left-right-lemma

-- H-level, Contractible, Is-proposition and Is-set.
--
-- Some of the definitions are slightly different from the ones given
-- in the paper.

H-level        = H-level.H-level
Contractible   = Equality.Reflexive-relation′.Contractible
Is-proposition = Equality.Reflexive-relation′.Is-proposition
Is-set         = Equality.Reflexive-relation′.Is-set

-- The circle.

𝕊¹ = Circle.𝕊¹

-- A function that is distinct from refl.

not-refl      = Circle.not-refl
not-refl≢refl = Circle.not-refl≢refl

-- The type base ≡ base is equivalent to ℤ.

base≡base≃ℤ = Circle.base≡base≃ℤ

-- The circle is not a set.

circle-not-set = Circle.¬-𝕊¹-set

-- The propositional truncation operator.

∥_∥ = H-level.Truncation.Propositional.∥_∥

------------------------------------------------------------------------
-- III: Traditional lenses

-- Lenses with equal setters have equal getters.

getters-equal-if-setters-equal = T.getters-equal-if-setters-equal

-- The identity lens.

id-traditional = TC.id

-- The lens used for the counterexamples.
--
-- This lens is a little different from the one in the text: the
-- source and view types are liftings of the circle instead of the
-- circle. This change also affects the proof of Lemma 12.

l = T.bad

-- Lemmas 12 and 13.

lemmas-12-and-13 = T.getter-equivalence-but-not-coherent

-- There are lenses with equal setters that are not equal.

equal-setters-but-not-equal =
  TC.equal-setters-and-equivalences-as-getters-but-not-equal

-- Lemma 14.

lemma-14 = T.lens-to-proposition↔

-- Lensᵀ A ⊤ is not necessarily a proposition (and thus not
-- necessarily equivalent to the unit type).

Traditional-lens-𝕊¹-⊤-not-propositional = T.¬-lens-to-⊤-propositional

-- Fibres.

_⁻¹_ = Preimage._⁻¹_

-- Lemmas 16 and 17, and a variant of Lemma 16 for lenses which
-- satisfy certain coherence laws.

lemma-16          = T.≃get⁻¹×
lemma-16-coherent = T.≃get⁻¹×-coherent
lemma-17          = T.≃Σ∥set⁻¹∥×

-- A variant of Lemma 17 without the requirement that the source type
-- is a set does not hold in general.

not-lemma-17-without-Is-set = TC.≄Σ∥set⁻¹∥×

------------------------------------------------------------------------
-- IV: Lenses based on bijections

-- Lenses based on bijections.

Lensᴮ = B.Lens

-- Lensᴮ ⊥ ⊥ is equivalent to Type.
--
-- Note that the definition of ⊥ that is used in the code can target
-- different universes, not just Type.

Lensᴮ-⊥-⊥≃Type = B.Lens-⊥-⊥≃Type

-- Lensᵀ ⊥ ⊥ is equivalent to ⊤.

Lensᵀ-⊥-⊥≃Type = T.lens-from-⊥≃⊤

------------------------------------------------------------------------
-- V: Higher lenses

-- Lensᴱ.
--
-- For performance reasons η-equality has been turned off for this
-- definition.

Lensᴱ = E.Lens

-- Lemma 20.

lemma-20 = E.isomorphism-to-lens

-- The functions get, remainder and set.

get       = E.Lens.get
remainder = E.Lens.remainder
set       = E.Lens.set

-- Lemmas 24-27.

lemma-24 = E.Lens.get-set
lemma-25 = E.Lens.remainder-set
lemma-26 = E.Lens.set-get
lemma-27 = E.Lens.set-set

-- Traditional lenses that have stable view types and that satisfy two
-- coherence laws can be translated to higher lenses with the same
-- getters and setters.

coherent-to-higher                       = EP.coherent↠higher
coherent-to-higher-preserves-get-and-set =
  EP.coherent↠higher-preserves-getters-and-setters

------------------------------------------------------------------------
-- VI: Coherence laws

-- Lemmas 28-29.

lemma-28 = E.Lens.get-set-get
lemma-29 = E.Lens.get-set-set

------------------------------------------------------------------------
-- VII: Some equivalences

-- Lemmas 30-37.
--
-- Lemmas 31 and 33 are formulated slightly differently.

lemma-30 = E.lens-to-proposition↔get
lemma-31 = E.lens-to-contractible↔⊤
lemma-32 = E.lens-to-⊥↔¬
lemma-33 = E.lens-from-contractible↔codomain-contractible
lemma-34 = E.lens-from-⊥↔⊤
lemma-35 = E.get-equivalence≃inhabited-equivalence
lemma-36 = E.≃-≃-Σ-Lens-Is-equivalence-get
lemma-37 = E.remainder≃get⁻¹

-- Lemmas 32-34 hold for traditional lenses.

lemma-32-for-traditional = T.lens-to-⊥↔
lemma-33-for-traditional = T.lens-from-⊤≃codomain-contractible
lemma-34-for-traditional = T.lens-from-⊥≃⊤

-- The right-to-left direction of Lemma 36 returns the lens's getter
-- (and some proof).

lemma-36-right-to-left = E.to-from-≃-≃-Σ-Lens-Is-equivalence-get≡get

-- Lemma 36 does not in general hold for traditional lenses.

¬-lemma-36-traditional = TC.¬Π≃-≃-Σ-Lens-Is-equivalence-get

------------------------------------------------------------------------
-- VIII: Equality of lenses with equal setters

-- Lemmas 38-44.

lemma-38 = E.equality-characterisation₁
lemma-39 = E.equality-characterisation₄
lemma-40 = E.lenses-with-inhabited-codomains-equal-if-setters-equal
lemma-41 = E.lenses-equal-if-setters-equal
lemma-42 = E.lenses-equal-if-setters-equal-and-remainder-set
lemma-43 = E.¬-lenses-equal-if-setters-equal
lemma-44 = E.lenses-equal-if-setters-equal→constant→coherently-constant

-- Constant and CC.

Constant = Equality.Decidable-UIP.Constant
CC       = Coherently-constant.Coherently-constant

-- Lemma 47.

lemma-47 = Coherently-constant.¬-Constant→Coherently-constant

------------------------------------------------------------------------
-- IX: Homotopy levels

-- Lemmas 48-54.

lemma-48 = E.h-level-respects-lens-from-inhabited
lemma-49 = E.contractible-to-contractible
lemma-50 = E.no-first-projection-lens
lemma-51 = E.remainder-has-same-h-level-as-domain
lemma-52 = E.get-equivalence→remainder-propositional
lemma-53 = E.Contractible-closed-codomain
lemma-54 = E.Is-proposition-closed-codomain

-- Lemmas 48-50 for traditional lenses.

lemma-48-for-traditional = T.h-level-respects-lens-from-inhabited
lemma-49-for-traditional = T.contractible-to-contractible
lemma-50-for-traditional = T.no-first-projection-lens

------------------------------------------------------------------------
-- X: Higher and traditional lenses are equivalent for sets

-- Split surjections.

_↠_ = Surjection._↠_

-- Lemmas 55 and 56.
--
-- Lemma 55 takes an extra argument of type Unit, written as
-- Block "conversion". Some other definitions below also take such
-- arguments.

lemma-55 = E.¬Lens↠Traditional-lens
lemma-56 = E.Lens↔Traditional-lens

-- Lemma 56 preserves getters and setters in both directions.

lemma-56-preserves-get-and-set =
  E.Lens↔Traditional-lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- XI: Identity and composition

-- The identity lens.

id = EC.id

-- Lemma 58.

lemma-58 = EC.id-unique

-- A composition operator for types in the same universe.

∘-same-universe = EC._∘_

-- A more general composition operator.

∘-more-general = EC.⟨_,_⟩_∘_

-- A lens from a type in a smaller universe to a type in a (possibly)
-- larger universe.

smaller-to-larger = E.↑-lens

-- Composition laws.

associativity  = EC.associativity
left-identity  = EC.left-identity
right-identity = EC.right-identity

-- Composition laws for traditional lenses.

associativity-traditional  = TC.associativity
left-identity-traditional  = TC.left-identity
right-identity-traditional = TC.right-identity

-- Lemma 60.
--
-- The lemma is formulated slightly differently.

lemma-60 = EC.∘-unique

-- The composition operator produces lenses for which the setter
-- satisfies certain equations.

setter-correct = EC.∘-set

-- Is-bi-invertible.

Is-bi-invertible = EC.Is-bi-invertible

-- Lemmas 62 and 63.

lemma-62 = EC.≃≃≊
lemma-63 = EC.Is-bi-invertible≃Is-equivalence-get

-- Lemma 62 maps bi-invertible lenses to their getter functions.

lemma-62-right-to-left = EC.to-from-≃≃≊≡get

-- Lemma 62 does not in general hold for traditional lenses.

not-lemma-62-for-traditional = TC.¬Π≃≃≊

-- A variant of Lemma 62 for traditional lenses (a split surjection in
-- the other direction).

lemma-62-for-traditional = TC.≊↠≃

-- Lemma 63 for traditional lenses.

lemma-63-for-traditional = TC.Is-bi-invertible≃Is-equivalence-get

-- A category of higher lenses between sets with the same universe
-- level.

category-higher = EC.category

-- A category of traditional lenses between sets with the same
-- universe level.

category-traditional = TC.category

-- The category of higher lenses is equal to the one for traditional
-- lenses (lifted, so that the two categories have the same type).

category≡category = EC.category≡category

-- Naive categories.

Naive-category = TC.Naive-category

-- A notion of univalence for naive categories.

Univalent = TC.Univalent

-- A naive category of higher lenses between types with the same
-- universe level.

naive-category-higher = EC.naive-category

-- This category is univalent.

naive-category-higher-univalent = EC.univalent

-- A naive category of traditional lenses between types with the same
-- universe level.

naive-category-traditional = TC.naive-category

-- This category is not univalent.

naive-category-traditional-not-univalent = TC.¬-univalent

------------------------------------------------------------------------
-- XII: Coherently constant families of fibres

-- Lens^F.

Lens^F = F.Lens

-- Lemma 65.

lemma-65 = F.Lens.get⁻¹-constant

-- A setter.

set^F = F.Lens.set

-- Lemma 67.
--
-- Unlike in the paper this lemma is defined in two steps, using a
-- minor variant of Lens^F "in the middle".

lemma-67 = F.Lens≃Higher-lens

-- Lemma 67 preserves getters and setters in both directions.

lemma-67-preserves-get-and-set =
  F.Lens≃Higher-lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- XIII: Coinductive lenses

-- The one-step truncation operator, and its non-dependent eliminator.

∥_∥¹ = H-level.Truncation.Propositional.One-step.∥_∥¹
rec  = H-level.Truncation.Propositional.One-step.rec′

-- Lemma 70.

lemma-70 = H-level.Truncation.Propositional.Non-recursive.∥∥→≃

-- ∥_∥¹-out, ∥_∥¹-in and ∣_,_∣-in.

∥_∥¹-out = H-level.Truncation.Propositional.One-step.∥_∥¹-out-^
∥_∥¹-in  = H-level.Truncation.Propositional.One-step.∥_∥¹-in-^
∣_,_∣-in = H-level.Truncation.Propositional.One-step.∣_,_∣-in-^

-- Lemmas 74 and 75.

lemma-74 = H-level.Truncation.Propositional.One-step.∥∥¹-out-^≃∥∥¹-in-^
lemma-75 = H-level.Truncation.Propositional.One-step.∣∣≡∣,∣-in-^

-- Coherently and CC^C.

Coherently = Coh.Coherently
CC^C       = C.Coherently-constant

-- Coherently can be defined without using coinduction.

Coherently-without-coinduction            = NC.Coherently
Coherently≃Coherently-without-coinduction =
 Coh.Coherently≃Not-coinductive-coherently

-- But then Lens^C would not be small (at least with the definition we
-- came up with).

Lens^C-without-coinduction        = S.Not-coinductive-lens
Lens^C-without-coinduction≃Lens^C = S.Not-coinductive-lens≃Lens

-- Constant¹ and CC^C1.

Constant¹ = C.Constant′
CC^C1     = C.Coherently-constant′

-- Lemmas 80-86.
--
-- Lemma 84 is more general than in the paper.

lemma-80 = C.Constant≃Constant′
lemma-81 = C.Coherently-constant≃Coherently-constant′
lemma-82 = C.∥∥→≃
lemma-83 = Equivalence.Σ-preserves
lemma-84 = Function-universe.Π-cong-contra
lemma-85 = C.Coherently-constant′≃
lemma-86 = C.Coherently-constant≃Coherently-constant

-- Constant^S and CC^S.

Constant^S = S.Constant-≃
CC^S       = S.Coherently-constant

-- Lemma 89.

lemma-89 = S.Coinductive-coherently-constant≃Coherently-constant

-- Lens^C.

Lens^C = S.Lens

-- Lemmas 91-92.

lemma-91 = S.Higher-lens≃Lens
lemma-92 = S.Lens.get⁻¹-constant

-- Lemma 91 preserves getters and setters.

lemma-91-preserves-get-and-set =
  S.Higher-lens≃Lens-preserves-getters-and-setters

------------------------------------------------------------------------
-- XIV: Unrestricted composition

-- Lemmas 93 and 94.

lemma-93 = S.Coherently-constant-map
lemma-94 = S.Coherently-constant-Σ

-- Composition.

∘-most-general = S.⟨_,_⟩_∘_

-- Lemma 96.

lemma-96 = S.set-∘

-- Composition laws.

associativity-stable  = S.associativity
left-identity-stable  = S.left-identity
right-identity-stable = S.right-identity

-- An unrestricted composition operator for Lensᴱ.

∘-most-general′ = S.⟨_,_,_,_,_,_,_,_⟩_⊚_

-- This operator matches "∘-more-general" when all types have the same
-- universe level and the view type of the resulting lens is stable.

∘-more-general-matches-∘-most-general′ = S.⊚≡∘

------------------------------------------------------------------------
-- XV: Homotopy levels, continued

-- Coherently′.

Coherently′ = Coh.Coherently-with-restriction

-- Lemma 98.

lemma-98 = Coh.Coherently≃Coherently-with-restriction

-- Coherently′ can be expressed as an indexed M-type for a certain
-- indexed container.

Coherently′-as-M-type =
  Coh.Coherently-with-restriction≃Coherently-with-restriction′

-- Lemmas 99-103.

lemma-99  = Coh.H-level-Coherently-with-restriction
lemma-100 = Coh.H-level-Coherently-→Type
lemma-101 = S.H-level-Coherently-constant
lemma-102 = S.lens-preserves-h-level
lemma-103 = S.h-level-respects-lens-from-inhabited

-- Lemma 103 and a variant of Lemma 102 hold for traditional lenses.

lemma-102-for-traditional = T.lens-preserves-h-level
lemma-103-for-traditional = T.lens-from-⊤≃codomain-contractible

------------------------------------------------------------------------
-- XVI: Related work

-- Lemmas 104-106.

lemma-104 = E.grenrus-example
lemma-105 = E.grenrus-example₁-true
lemma-106 = E.grenrus-example₂-false

-- The lenses used in Lemmas 105 and 106 are equal.

lenses-equal = E.grenrus-example₁≡grenrus-example₂

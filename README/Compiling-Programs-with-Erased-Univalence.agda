------------------------------------------------------------------------
-- Code related to the paper "Compiling Programs with Erased
-- Univalence"
--
-- Nils Anders Danielsson
--
-- The paper is coauthored with Andreas Abel and Andrea Vezzosi.
------------------------------------------------------------------------

-- Most of the code referenced below can be found in modules that are
-- parametrised by a notion of equality. One can use them both with
-- Cubical Agda paths and with the Cubical Agda identity type family.

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences.

-- An attempt has been made to track uses of univalence by passing
-- around explicit proofs of the univalence axiom (except in certain
-- README modules). However, some library code that is used does not
-- adhere to this convention (note that univalence is provable in
-- Cubical Agda), so perhaps some use of univalence is not tracked in
-- this way. On the other hand some library code that is not defined
-- in Cubical Agda passes around explicit proofs of function
-- extensionality.

-- Some other differences are mentioned below.

-- Note that there is a known problem with guarded corecursion in
-- Agda. Due to "quantifier inversion" (see "Termination Checking in
-- the Presence of Nested Inductive and Coinductive Types" by Thorsten
-- Altenkirch and myself) certain types may not have the expected
-- semantics when the option --guardedness is used. I expect that the
-- results would still hold if this bug were fixed, but because I do
-- not know what the rules of a fixed version of Agda would be I do
-- not know if any changes to the code would be required.

{-# OPTIONS --guardedness #-}

module README.Compiling-Programs-with-Erased-Univalence where

import Coherently-constant
import Colimit.Sequential
import Colimit.Sequential.Very-erased
import Equality.Path
import Equality.Path.Univalence
import Equivalence
import Equivalence.Erased
import Equivalence.Erased.Basics
import Equivalence.Erased.Contractible-preimages
import Equivalence.Half-adjoint
import Erased.Basics
import Erased.Cubical
import Erased.Level-1
import Erased.Stability
import H-level.Truncation.Propositional
import H-level.Truncation.Propositional.Erased
import H-level.Truncation.Propositional.Non-recursive
import H-level.Truncation.Propositional.Non-recursive.Erased
import H-level.Truncation.Propositional.One-step
import Preimage
import Univalence-axiom

import Lens.Non-dependent.Higher
import Lens.Non-dependent.Higher.Erased
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant
import Lens.Non-dependent.Higher.Coinductive
import Lens.Non-dependent.Higher.Coinductive.Erased
import Lens.Non-dependent.Higher.Coinductive.Small
import Lens.Non-dependent.Higher.Coinductive.Small.Erased

import README.Fst-snd

------------------------------------------------------------------------
-- 2: Cubical Agda

-- The functions cong and ext.

cong = Equality.Path.cong
ext  = Equality.Path.⟨ext⟩

-- The propositional truncation operator.
--
-- The current module uses --erased-cubical, so this operator, which
-- is defined using --cubical, can only be used in erased contexts.

@0 ∥_∥ : _
∥_∥ = H-level.Truncation.Propositional.∥_∥

-- The map function. This function is not defined in the same way as
-- in the paper, it is defined using a non-dependent eliminator.

@0 map : _
map = H-level.Truncation.Propositional.∥∥-map

-- The propositional truncation operator with an erased truncation
-- constructor.

∥_∥ᴱ = H-level.Truncation.Propositional.Erased.∥_∥ᴱ

-- Half adjoint equivalences. Note that, unlike in the paper, _≃_ is
-- defined as a record type.

Is-equivalence = Equivalence.Half-adjoint.Is-equivalence
_≃_            = Equivalence._≃_

-- Univalence. (This type family is not defined in exactly the same
-- way as in the paper.)

Univalence = Univalence-axiom.Univalence

-- A proof of univalence. The proof uses glue.

@0 univ : _
univ = Equality.Path.Univalence.univ

------------------------------------------------------------------------
-- 3: Postulating Erased Univalence

-- Erased.

Erased = Erased.Basics.Erased

-- []-cong for paths.

[]-cong = Erased.Cubical.[]-cong-Path

------------------------------------------------------------------------
-- 6.1: Equivalences with Erased Proofs

-- Equivalences with erased proofs. Note that, unlike in the paper,
-- _≃ᴱ_ is defined as a record type.

Is-equivalenceᴱ = Equivalence.Erased.Basics.Is-equivalenceᴱ
_≃ᴱ_            = Equivalence.Erased.Basics._≃ᴱ_
to              = Equivalence.Erased.Basics._≃ᴱ_.to
from            = Equivalence.Erased.Basics._≃ᴱ_.from
@0 to-from : _
to-from         = Equivalence.Erased.Basics._≃ᴱ_.right-inverse-of
@0 from-to : _
from-to         = Equivalence.Erased.Basics._≃ᴱ_.left-inverse-of

-- Erased≃ is stated a little differently.

Erased≃ = Erased.Level-1.Erased↔

-- Lemmas 41 and 42 are proved in modules parametrised by definitions
-- of []-cong, which is also assumed to satisfy certain properties
-- (that hold for the definition mentioned above). Some definitions
-- below are also defined in such modules.

Lemma-41 = Erased.Level-1.Erased-cong.Erased-cong-≃
Lemma-42 = Equivalence.Erased.[]-cong₁.Σ-cong-≃ᴱ-Erased

-- The functions substᴱ and subst.

substᴱ = Erased.Level-1.[]-cong₁.substᴱ
subst  = Equality.Path.subst

-- Lemmas 45–47.

Lemma-45 = Equivalence.Erased.[]-cong.drop-⊤-left-Σ-≃ᴱ-Erased
Lemma-46 = Equivalence.Erased.Σ-cong-≃ᴱ
Lemma-47 = Equivalence.Erased.drop-⊤-left-Σ-≃ᴱ

------------------------------------------------------------------------
-- 6.2: A Non-recursive Definition of the Propositional Truncation
-- Operator

-- ∥_∥¹ and Colimit.

@0 ∥_∥¹ : _
∥_∥¹ = H-level.Truncation.Propositional.One-step.∥_∥¹
@0 Colimit : _
Colimit = Colimit.Sequential.Colimit

-- Lemma 50.

@0 Lemma-50 : _
Lemma-50 = Colimit.Sequential.universal-property

-- ∥_∥¹-out and ∥_∥ᴺ.

@0 ∥_∥¹-out : _
∥_∥¹-out = H-level.Truncation.Propositional.One-step.∥_∥¹-out-^
@0 ∥_∥ᴺ : _
∥_∥ᴺ = H-level.Truncation.Propositional.Non-recursive.∥_∥

-- ∥_∥ᴺ and ∥_∥ are pointwise equivalent.

@0 ∥∥ᴺ≃∥∥ : _
∥∥ᴺ≃∥∥ = H-level.Truncation.Propositional.Non-recursive.∥∥≃∥∥

-- Colimitᴱ.

Colimitᴱ = Colimit.Sequential.Very-erased.Colimitᴱ

-- Lemma 54.

Lemma-54 = Colimit.Sequential.Very-erased.universal-property

-- ∥_∥ᴺᴱ.

∥_∥ᴺᴱ = H-level.Truncation.Propositional.Non-recursive.Erased.∥_∥ᴱ

-- Lemma 56 (or rather its inverse).

Lemma-56 = H-level.Truncation.Propositional.Erased.∥∥ᴱ≃∥∥ᴱ

------------------------------------------------------------------------
-- 6.3: Higher Lenses with Erased Proofs

-- Lensᴱ, get and set.

@0 Lensᴱ : _
Lensᴱ = Lens.Non-dependent.Higher.Lens
@0 get : _
get = Lens.Non-dependent.Higher.Lens.get
@0 set : _
set = Lens.Non-dependent.Higher.Lens.set

-- Lensᴱᴱ.

Lensᴱᴱ = Lens.Non-dependent.Higher.Erased.Lens

-- The function _⁻¹_.

_⁻¹_ = Preimage._⁻¹_

-- Lens^C (defined using a record type).

@0 Lens^C : _
Lens^C = Lens.Non-dependent.Higher.Coinductive.Small.Lens

-- Coherently-constant^C.

@0 Coherently-constant^C : _
Coherently-constant^C =
  Lens.Non-dependent.Higher.Coinductive.Small.Coherently-constant

-- Lens^CE (with the field name get⁻¹-coherently-constant instead of
-- cc).

Lens^CE = Lens.Non-dependent.Higher.Coinductive.Small.Erased.Lens

------------------------------------------------------------------------
-- 6.4: The Definitions Are Equivalent

-- Lemma 65 (or rather its inverse), and a proof (in an erased
-- context) showing that Lemma 65 preserves getters and setters.
--
-- Lemma 65 and some other lemmas use arguments of type Block s (for
-- some string s). This type is equivalent to the unit type. These
-- arguments are used to block definitions from being unfolded by the
-- type-checker.

Lemma-65 =
  Lens.Non-dependent.Higher.Coinductive.Small.Erased.Lens≃ᴱLensᴱ
@0 Lemma-65-preserves-getters-and-setters : _
Lemma-65-preserves-getters-and-setters =
  Lens.Non-dependent.Higher.Coinductive.Small.Erased.Lens≃ᴱLensᴱ-preserves-getters-and-setters

-- Lens₁ᴱ and Lens₂ᴱ.

Lens₁ᴱ = Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant.Lens
Lens₂ᴱ = Lens.Non-dependent.Higher.Coinductive.Erased.Lens

-- The function _⁻¹ᴱ_.

_⁻¹ᴱ_ = Equivalence.Erased.Contractible-preimages._⁻¹ᴱ_

-- Coherently-constant₁ᴱ, Coherently-constant, Coherently-constant₂ᴱ,
-- Coherently-constant₂^C and constant.

Coherently-constant₁ᴱ =
  Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant.Coherently-constant
@0 Coherently-constant : _
Coherently-constant = Coherently-constant.Coherently-constant
Coherently-constant₂ᴱ =
  Lens.Non-dependent.Higher.Coinductive.Erased.Coherently-constant
@0 Coherently-constant₂^C : _
Coherently-constant₂^C =
  Lens.Non-dependent.Higher.Coinductive.Coherently-constant
@0 constant : _
constant = Lens.Non-dependent.Higher.Coinductive.constant

-- Lemmas 74–77.

Lemma-74 = Erased.Stability.Erased-other-singleton≃ᴱ⊤
Lemma-75 = Lens.Non-dependent.Higher.Coinductive.Erased.∥∥ᴱ→≃
Lemma-76 = Equivalence.Erased.other-singleton-with-Π-≃ᴱ-≃ᴱ-⊤
Lemma-77 = H-level.Truncation.Propositional.Erased.Σ-Π-∥∥ᴱ-Erased-≡-≃

------------------------------------------------------------------------
-- 6.5: Compilation of Lenses

-- A slightly more general variant of sndᴱ.

sndᴱ = Lens.Non-dependent.Higher.Erased.snd

-- Lemma 79.

Lemma-79 = H-level.Truncation.Propositional.Erased-∥∥×≃

-- A slightly more general variant of snd^C.

snd^C = README.Fst-snd.snd-with-space-leak

-- Lemma 81.

Lemma-81 =
  Lens.Non-dependent.Higher.Coinductive.Small.Erased.with-other-setter

-- A slightly more general variant of the variant of snd^C with a
-- changed setter.

snd^C-with-changed-setter = README.Fst-snd.snd

------------------------------------------------------------------------
-- The lenses fst and snd
------------------------------------------------------------------------

-- This module uses univalence without tracking such uses in the types
-- of functions, and it is not parametrised by a notion of equality,
-- it uses path equality.

{-# OPTIONS --guardedness #-}

module README.Fst-snd where

open import Equality.Path
open import Equality.Path.Univalence
open import Prelude

open import Equivalence.Erased.Cubical equality-with-paths as EEq
  using (_≃ᴱ_)

import Lens.Non-dependent.Higher.Coinductive.Small.Erased
  equality-with-paths as S
import Lens.Non-dependent.Higher.Erased equality-with-paths as E

private
  variable
    a   : Level
    A B : Type a

-- A static variant of one consequence of S.Lens≃ᴱLensᴱ. Applications
-- of static functions are normalised by (at least) the GHC backend.

Lens→Lens : E.Lens A B → S.Lens univ A B
Lens→Lens = _≃ᴱ_.from (S.Lens≃ᴱLensᴱ ⊠ univ)

{-# STATIC Lens→Lens #-}

-- A lens for the first projection.

fst : S.Lens univ (A × B) A
fst = Lens→Lens E.fst

-- A lens for the second projection.
--
-- With the implementation that this lens had at the time of writing
-- (dependencies may later have changed) it turned out that when the
-- lens was compiled using the non-strict GHC backend of a certain
-- development version of Agda and GHC 9.0.1, then GHC's flag
-- -ddump-simpl suggested that you ended up with code that could lead
-- to a space leak: the code for the setter was something like
--
--   \p y -> Pair (case p of { Pair x _ -> x }) y
--
-- (where names have been changed, and code related to coercions and
-- casts has been removed).
--
-- Note that, unlike the lens snd^C discussed in "Compiling Programs
-- with Erased Univalence", this one (as well as the one below) takes
-- two universe level arguments.

snd-with-space-leak : S.Lens univ (A × B) B
snd-with-space-leak = Lens→Lens E.snd

-- A lens for the second projection.
--
-- This variant did not seem to have the problem exhibited by
-- snd-with-space-leak: the code for the setter was something like
--
--   \p y -> case p of { Pair x _ -> Pair x y }.

snd : S.Lens univ (A × B) B
snd =
  S.with-other-setter
    (Lens→Lens E.snd)
    (λ { (x , _) y → (x , y) })
    ((λ (x , _) y → (x , y))       ≡⟨⟩
     E.Lens.set E.snd              ≡⟨ sym $ proj₂ $ proj₂ (S.Lens≃ᴱLensᴱ-preserves-getters-and-setters ⊠ univ univ) E.snd ⟩∎
     S.Lens.set (Lens→Lens E.snd)  ∎)

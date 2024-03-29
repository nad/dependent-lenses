------------------------------------------------------------------------
-- Non-dependent and dependent lenses
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --cubical --guardedness #-}

module README where

-- Non-dependent lenses.

import Lens.Non-dependent
import Lens.Non-dependent.Traditional
import Lens.Non-dependent.Traditional.Combinators
import Lens.Non-dependent.Higher
import Lens.Non-dependent.Higher.Combinators
import Lens.Non-dependent.Higher.Capriotti.Variant
import Lens.Non-dependent.Higher.Capriotti
import Lens.Non-dependent.Higher.Coherently.Not-coinductive
import Lens.Non-dependent.Higher.Coherently.Coinductive
import Lens.Non-dependent.Higher.Coinductive
import Lens.Non-dependent.Higher.Coinductive.Small
import Lens.Non-dependent.Higher.Surjective-remainder
import Lens.Non-dependent.Equivalent-preimages
import Lens.Non-dependent.Bijection

-- Non-dependent lenses with erased proofs.

import Lens.Non-dependent.Traditional.Erased
import Lens.Non-dependent.Higher.Erased
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased
import Lens.Non-dependent.Higher.Capriotti.Variant.Erased.Variant
import Lens.Non-dependent.Higher.Coinductive.Erased
import Lens.Non-dependent.Higher.Coinductive.Small.Erased
import Lens.Non-dependent.Higher.Coherently.Coinductive.Erased

-- Dependent lenses.

import Lens.Dependent

-- Comparisons of different kinds of lenses, focusing on the
-- definition of composable record getters and setters.

import README.Record-getters-and-setters

-- Some code suggesting that types used in "programs" might not
-- necessarily be sets. (If lenses are only used in programs, and
-- types used in programs are always sets, then higher lenses might be
-- pointless.)

import README.Not-a-set

-- Pointers to code corresponding to many definitions and results from
-- the paper "Higher Lenses" by Paolo Capriotti, Nils Anders
-- Danielsson and Andrea Vezzosi.

import README.Higher-Lenses

-- The lenses fst and snd.

import README.Fst-snd

-- Pointers to code corresponding to some definitions and results from
-- the paper "Compiling Programs with Erased Univalence" by Andreas
-- Abel, Nils Anders Danielsson and Andrea Vezzosi.

import README.Compiling-Programs-with-Erased-Univalence

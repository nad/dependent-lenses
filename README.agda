------------------------------------------------------------------------
-- Non-dependent and dependent lenses
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module README where

-- Non-dependent lenses.

import Lens.Non-dependent
import Lens.Non-dependent.Traditional
import Lens.Non-dependent.Higher
import Lens.Non-dependent.Higher.Capriotti
import Lens.Non-dependent.Higher.Capriotti.Variant
import Lens.Non-dependent.Higher.Surjective-remainder
import Lens.Non-dependent.Equivalent-preimages
import Lens.Non-dependent.Bijection

-- Non-dependent lenses with erased proofs.

import Lens.Non-dependent.Traditional.Erased
import Lens.Non-dependent.Higher.Erased

-- Dependent lenses.

import Lens.Dependent

-- Comparisons of different kinds of lenses, focusing on the
-- definition of composable record getters and setters.

import README.Record-getters-and-setters

-- Pointers to code corresponding to many definitions and results from
-- the paper "Higher lenses" by Paolo Capriotti, Nils Anders
-- Danielsson and Andrea Vezzosi.

import README.Higher-lenses

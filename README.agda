------------------------------------------------------------------------
-- Non-dependent and dependent lenses
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module README where

-- Non-dependent lenses.

import Lens.Non-dependent
import Lens.Non-dependent.Traditional
import Lens.Non-dependent.Alternative

-- Dependent lenses.

import Lens.Dependent

-- Comparisons of different kinds of lenses, focusing on the
-- definition of composable record getters and setters.

import README.Record-getters-and-setters

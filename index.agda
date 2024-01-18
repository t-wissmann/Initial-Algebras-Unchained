{-# OPTIONS --without-K --safe #-}
--      ======================================================
--
--                Initial Algebras Unchained:
--
--       A novel and constructive initial algebra construction
--                 without transfinite induction
--
--      ======================================================
--
-- This file does not contain any proofs but provides links
-- to the respective modules of the formalization.
--
-- Some general categorical utils:
import Unchained-Utils

-- Colimits of coalgebras
import F-Coalgebra-Colimit

-- Properties of filtered diagrams
import Filtered
import Cofinal

-- definition of weak lfp category
import LFP-slices
import LFP

-- Properties about coalgebras:
import Coalgebra.Recursive
import Coalgebra.IdxProp
import Coalgebra.IdxProp-fmap

-- some lemmas about recursive coalgebras
import Lambek



-- Some properties of Setoids:
import Setoids-Choice -- a weak choice principle for preimages of elements of colimits
import Setoids-Colimit -- necessary/sufficient conditions when cocones are colimitting
import Setoids-LFP -- Setoids are an instance of a (weak) LFP category


import Iterate
import Unique-Proj
import Construction
import Classical-Case

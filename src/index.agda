{-# OPTIONS --without-K --safe #-}
--      ======================================================
--
--                  Initial Algebras Unchained
--                            ----
--              A Novel Initial Algebra Construction
--                     Formalized in Agda
--
--      ======================================================
--
-- This file provides links to the respective modules
-- of the formalization.
--

import Helper-Definitions

-- Some general results about colimits:
import Colimit-Lemmas
import F-Coalgebra-Colimit
import Cofinal

-- Properties of full subcategories of full subcategories:
import FullSub-map

-- Properties of filtered diagrams
import Filtered

-- Definition of weak lfp category
import Presentable
import LFP-slices
import LFP

-- Properties about coalgebras:
import Coalgebra.Recursive
import Coalgebra.IdxProp
import Coalgebra.IdxProp-fmap

-- A (slightly generalized) Lambek's Lemma
import Lambek

-- Some properties of Setoids:
import Setoids-Choice -- a weak choice principle for preimages of elements of colimits
import Setoids-Colimit -- necessary/sufficient conditions when cocones are colimitting
import Hom-Colimit-Choice -- instance of the above for colimits of hom sets

import FinCoequalizer -- (weak form of) finite coequalizers in Setoids for the verification of:
import Setoids-LFP -- Setoids are an instance of a (weak) LFP category

-- Coalgebras that arise as colimits:
import CoalgColim
import Unique-Proj

-- The construction to apply F-Coalgebra.iterate to coalgebra colimits,
-- i.e. if A,α is the a colimit of 'finite' coalgebras, then FA,Fα is
-- also a colimit of 'finite' coalgebras:
import Iterate.Assumptions
import Iterate.ProofGlobals
import Iterate.FiniteSubcoalgebra
import Iterate.DiagramScheme -- the diagram scheme for the claimed colimit
import Iterate.Colimit
import Iterate

-- The main result:
import Construction
-- Simplified assumptions if the law of excluded middle is assumed:
import Classical-Case

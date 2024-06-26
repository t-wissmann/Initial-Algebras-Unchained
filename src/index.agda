{-# OPTIONS --without-K --safe #-}
--      ============================================================
--
--                     Initial Algebras Unchained
--                               ----
--                 A Novel Initial Algebra Construction
--                        Formalized in Agda
--
--                 By Thorsten Wißmann and Stefan Milius
--                 accepted for publication at LICS 2024
--
--                            Preprint:
--                  https://arxiv.org/abs/2405.09504
--                       Agda source repository:
--      https://git8.cs.fau.de/software/initial-algebras-unchained
--
--      ============================================================
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

-- Definition of Fil-accessible categories
import Presentable
import Canonical-Cocone
import Accessible-Category

-- Example of a Fil-Accessible category: Setoids
import FinCoequalizer -- (weak form of) finite coequalizers in Setoids for the verification of:
import Setoids-Accessible -- Setoids are an instance of a (Fil-)accessible category

-- Some properties of colimits in Setoids:
import Setoids-Choice -- a weak choice principle for preimages of elements of colimits
import Setoids-Colimit -- necessary/sufficient conditions when cocones are colimitting
import Hom-Colimit-Choice -- instance of the above for colimits of hom sets

-- Properties of coalgebras:
import Coalgebra.Recursive
import Coalgebra.IdxProp
import Coalgebra.IdxProp-fmap
import CoalgColim -- Coalgebras that arise as colimits

-- Sufficient conditions such that the colimit injections
-- are the unique coalgebra morphisms:
import Unique-Proj

-- A (slightly generalized) Lambek's Lemma
import Lambek

-- The construction to apply F-Coalgebra.iterate to coalgebra colimits,
-- i.e. if A,α is the a colimit of 'finite' coalgebras, then FA,Fα is
-- also a colimit of 'finite' coalgebras:
import Iterate.Assumptions
import Iterate.ProofGlobals
import Iterate.FiniteSubcoalgebra
import Iterate.DiagramScheme -- the diagram scheme for the claimed colimit
import Iterate.Colimit
import Iterate

-- The main result: The initial F-Algebra constructed as the colimit
-- of all recursive coalgebras with presentable carrier.
import Construction
-- Simplified assumptions if the law of excluded middle is assumed:
import Classical-Case

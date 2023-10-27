{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Category.Slice
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Categories.Category.Product
open import Agda.Builtin.Equality renaming (refl to ≡-refl)
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.SubCategory
open import Categories.Category.Construction.Comma
open import Categories.Category.Slice
open import Categories.Functor.Slice as Sl
open import Categories.Functor.Construction.SubCategory
open import Categories.Functor using (Functor; Endofunctor)
open import Data.Product

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP using (WeaklyLFP)
open import Filtered
open import Cofinal
open import Setoids-Choice
open import Unchained-Utils

-- intuitively:
-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ fil-level}
  (𝒞 : Category o ℓ ℓ)
  (F : Endofunctor 𝒞)
  (Fil : ∀ {o' ℓ' e' : Level} → Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category ℓ ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 Fil Fil-to-filtered)
  where


open import LFP 𝒞 Fil Fil-to-filtered hiding (WeaklyLFP)

module 𝒞 = Category 𝒞
open import recursive-coalgebra 𝒞 F
open import LFP-slices 𝒞
open import Hom-Colimit-Choice 𝒞
open import Categories.Diagram.Pushout 𝒞
open import Categories.Morphism 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞
open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F}
open import Presented 𝒞 Fil

module F-Coalgebras = Category (F-Coalgebras F)

open import Iterate.Assumptions 𝒞 F Fil

module 𝒞-lfp = WeaklyLFP 𝒞-lfp
open import Prop-Coalgebra 𝒞 F FinitaryRecursive

import Iterate.Colimit as I-C
import Iterate.DiagramScheme as I-D
import Iterate.ProofGlobals as I-P

-- Proof: whenever (A,α) is locally finite, then so is (FA,Fα).
-- We structure the proof as a module because it makes it easier
-- to globally fix a certian parameters along the way.
iterate-CoalgColimit :
  (coalg-colim : LProp-Coalgebra {ℓ} {ℓ} {ℓ}) →
  Fil (LProp-Coalgebra.𝒟 coalg-colim) →
  -- ^- coalg is a colimit of a filtered diagram
  preserves-colimit (LProp-Coalgebra.carrier-diagram coalg-colim) F →
  -- ^- F preserves the colimit 'coalg'
  LProp-Coalgebra
iterate-CoalgColimit coalg-colim 𝒟-filtered F-preserves-colim = goal
  where
  goal = I-C.FA,Fα-locally-finite Fil
    (record
     { 𝒞 = 𝒞
     ; F = F
     ; Fil-to-filtered = Fil-to-filtered
     ; 𝒞-lfp = 𝒞-lfp
     ; coalg-colim = coalg-colim
     ; 𝒟-filtered = 𝒟-filtered
     ; F-preserves-colim = F-preserves-colim
     })
  module goal = LProp-Coalgebra goal
  module coalg-colim = LProp-Coalgebra coalg-colim
  -- Here, we double-check that the constructed coalgebra really normalizes to
  -- the iteration of the input coalgebra:
  test-correct-carrier : goal.to-Coalgebra ≡ iterate (coalg-colim.to-Coalgebra)
  test-correct-carrier = ≡-refl

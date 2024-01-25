{-# OPTIONS --without-K --safe #-}
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
open import Categories.Functor.Properties using (Full)
open import Function.Surjection using (Surjective)
open import Function.Equality hiding (_∘_)
open import Categories.Functor.Construction.SubCategory
open import Categories.Functor using (Functor; Endofunctor)
open import Data.Product

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP using (WeaklyLFP)
open import Filtered
open import Cofinal
open import Setoids-Choice
open import Colimit-Lemmas

-- intuitively:
-- o : level of 'classes'
-- ℓ : level of 'sets'
module Iterate {o ℓ fil-level}
  {o' ℓ' : Level } -- Level for diagram schemes
  (𝒞 : Category o ℓ ℓ)
  (F : Endofunctor 𝒞)
  (Fil : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)  → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 o' ℓ' ℓ' Fil Fil-to-filtered)
  where

open import LFP 𝒞 o' ℓ' ℓ' Fil Fil-to-filtered hiding (WeaklyLFP)

module 𝒞 = Category 𝒞
open import Coalgebra.Recursive 𝒞 F
open import LFP-slices 𝒞
open import Hom-Colimit-Choice
open import Categories.Diagram.Pushout 𝒞
open import Categories.Morphism 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞
open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F}
open import Presentable 𝒞 (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ) Fil

module F-Coalgebras = Category (F-Coalgebras F)

open import Iterate.Assumptions {o' = o'} {ℓ' = ℓ'} 𝒞 F Fil

private
  module 𝒞-lfp = WeaklyLFP 𝒞-lfp
open import CoalgColim 𝒞 F FiniteRecursive

import Iterate.Colimit as I-C
import Iterate.DiagramScheme as I-D
import Iterate.ProofGlobals as I-P

-- Proof: whenever (A,α) is locally finite, then so is (FA,Fα).
-- We structure the proof as a module because it makes it easier
-- to globally fix a certian parameters along the way.
iterate-CoalgColimit :
  (coalg-colim : CoalgColim {o' ⊔ ℓ} {ℓ' ⊔ ℓ} {ℓ' ⊔ ℓ}) →
  Fil (CoalgColim.𝒟 coalg-colim) →
  -- ^- coalg is a colimit of a filtered diagram
  preserves-colimit (CoalgColim.carrier-diagram coalg-colim) F →
  -- ^- F preserves the colimit 'coalg'
  CoalgColim
iterate-CoalgColimit coalg-colim 𝒟-filtered F-preserves-colim = goal
  where
    goal = I-C.FA,Fα-locally-finite Fil
      record
      { 𝒞 = 𝒞
      ; F = F
      ; Fil-to-filtered = Fil-to-filtered
      ; 𝒞-lfp = 𝒞-lfp
      ; coalg-colim = coalg-colim
      ; 𝒟-filtered = 𝒟-filtered
      ; F-preserves-colim = F-preserves-colim
      }
    module goal = CoalgColim goal
    module coalg-colim = CoalgColim coalg-colim
    -- Here, we double-check that the constructed coalgebra really normalizes to
    -- the iteration of the input coalgebra:
    test-correct-carrier : goal.to-Coalgebra ≡ iterate (coalg-colim.to-Coalgebra)
    test-correct-carrier = ≡-refl

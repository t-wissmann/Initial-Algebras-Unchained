{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Construction.SubCategory using (FullSub)
open import Categories.Functor using (Functor; Endofunctor)

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP
open import Filtered
open import Unchained-Utils

-- intuitively:
-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ e fil-level}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (Fil : Category ℓ ℓ ℓ → Set fil-level) -- some variant of 'filtered'
  (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ Fil)
  where

module 𝒞-lfp = WeaklyLFP 𝒞-lfp
open import recursive-coalgebra 𝒞 F
open import Fin-R-Coalgebra 𝒞 F 𝒞-lfp.fin IsRecursive

-- whenever (A,α) is locally finite, then so is (FA,Fα)
iterate-LFinCoalgebra : LFinCoalgebra → LFinCoalgebra
iterate-LFinCoalgebra coalg-colim =
  let
    -- the provided coalgebra:
    module coalg-colim = LFinCoalgebra coalg-colim
    open F-Coalgebra coalg-colim.to-Coalgebra
    -- ^- this brings A and α into scope
    open Functor F
    -- We show that (FA,Fα) is a colimit by taking the
    -- diagram scheme from the fact that FA is a colimit of
    -- finite objects:
    FA-colim = 𝒞-lfp.canonical-colimit (F₀ A)
    module FA-colim = Colimit FA-colim
  in
  {!!}
-- module _
--   (P : Category ℓ ℓ ℓ → Set prop-level)
--   (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
--   (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ P)
--   (𝒞-cocomplete : Cocomplete ℓ ℓ ℓ 𝒞)
--   where
--
--   module 𝒞-lfp = WeaklyLFP 𝒞-lfp
--   module F = Functor F

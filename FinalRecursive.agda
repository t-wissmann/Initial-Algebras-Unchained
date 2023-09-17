{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Cocomplete
open import Categories.Functor using (Functor; Endofunctor)

open import Data.Product
open import LFP
open import Filtered

-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ} (𝒞 : Category o ℓ ℓ) (F : Endofunctor 𝒞) where

open import recursive-coalgebra 𝒞 F

private
  variable
    -- levels of 'set'
    𝒟 : Category ℓ ℓ ℓ
    prop-level : Level

-- The global assumptions:
module _
  (P : Category ℓ ℓ ℓ → Set prop-level)
  (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
  (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ P)
  (𝒞-cocomplete : Cocomplete ℓ ℓ ℓ 𝒞)
  where

  module 𝒞-lfp = WeaklyLFP 𝒞-lfp
  module F = Functor F

  R-Coalgebras-fp : Category ℓ ℓ ℓ
  R-Coalgebras-fp = FullSubCategory (R-Coalgebras) {!!}
    where
      open import Categories.Category.SubCategory using (FullSubCategory)
      open Category 𝒞
      open Functor F
      -- Here, we have an issue: how can we define the family of fp R-Coalgebras
      -- such that it lives on the level ℓ and does not require level o?
      -- family : Σ[ i ∈ 𝒞-lfp.I ](?)
      -- family = {!!}

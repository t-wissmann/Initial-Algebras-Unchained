{-# OPTIONS --without-K #-}
open import Level
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
open import Data.Product

open import Categories.Functor.Coalgebra

open import LFP using (WeaklyLFP)
open import Filtered
open import Unchained-Utils

-- Here, we fix some modules/helper definitions
-- for the iteration proof.
module Iterate.Assumptions {o ℓ fil-level}
  (𝒞 : Category o ℓ ℓ)
  (F : Endofunctor 𝒞)
  (Fil : ∀ {o' ℓ' e' : Level} → Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  where

open import Presented 𝒞 Fil
open import recursive-coalgebra 𝒞 F

record FinitaryRecursive (coalg : F-Coalgebra F) : Set (o ⊔ suc ℓ ⊔ fil-level) where
  -- the property that a coalgebra
  field
    -- 1. has finite carrier
    finite-carrier : presented (F-Coalgebra.A coalg)
    -- 2. is recursive
    is-recursive : IsRecursive coalg

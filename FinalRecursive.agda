{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Cocomplete

open import LFP
open import Filtered

module FinalRecursive {o ℓ e} (𝒞 : Category o ℓ e) where

private
  variable
    -- levels for the diagram scheme:
    o' ℓ' e' : Level
    𝒟 : Category o' ℓ' e'
    prop-level : Level

-- The global assumptions:
module _
  (P : Category o' ℓ' e' → Set prop-level)
  (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
  (𝒞-lfp : WeaklyLFP 𝒞 o' ℓ' e'  P)
  (𝒞-cocomplete : Cocomplete o' ℓ' e' 𝒞)
  where

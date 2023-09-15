{-# OPTIONS --without-K #-}
open import Level

open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Filtered
open import LFP

module Setoid-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level
    -- levels for the diagram scheme:
    o' ℓ' e' : Level

-- setoids-LFP : WeaklyLFP (Setoids o ℓ) filtered
-- setoids-LFP = {!!}

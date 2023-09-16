{-# OPTIONS --without-K #-}
open import Level

open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Filtered renaming (filtered to filtered-general)
open import LFP
open import Data.Nat.Base
open import Data.Fin
open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to ≡-setoid)

module Setoid-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level

filtered : Category o ℓ ℓ → Set _
filtered = filtered-general


setoids-LFP : WeaklyLFP (Setoids o o) filtered
setoids-LFP = record {
  I = ℕ ;
  𝒞-fp = λ n → ≡-setoid {!!};
  all-I-fp = λ i 𝒟 x J → {!!} ;
  build-from-fp = {!!}
  }

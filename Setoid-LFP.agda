{-# OPTIONS --without-K #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Filtered renaming (filtered to filtered-general)
open import LFP
open import Data.Nat.Base using (ℕ)
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties

module Setoid-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level

filtered : Category o ℓ ℓ → Set _
filtered = filtered-general

-- we use a custom 'setoid' variation to achieve arbitrary levels o, ℓ
≡-setoid : ∀ {o ℓ : Level} → Set 0ℓ → Setoid o ℓ
≡-setoid {o} {ℓ} X =
  record { Carrier = Lift o X
  ; _≈_ = λ (lift x₁) (lift x₂) → L.Lift ℓ (x₁ ≡ x₂)
  ; isEquivalence =
    record {
      refl = Level.lift refl ;
      sym = λ (L.lift eq) → Level.lift (sym eq) ;
      trans = λ (L.lift x≡y) (L.lift y≡z) → Level.lift (trans x≡y y≡z) } }

setoids-LFP : WeaklyLFP (Setoids o ℓ) filtered
setoids-LFP = record {
  I = ℕ ;
  𝒞-fp = λ n → ≡-setoid (Fin n);
  all-I-fp = λ n 𝒟 𝒟-filtered J colim → {!!} ;
  build-from-fp = {!!}
  }

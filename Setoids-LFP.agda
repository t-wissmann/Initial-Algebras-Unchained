{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Filtered
open import LFP
open import Data.Nat.Base using (ℕ)
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Categories.Diagram.Cocone.Properties
open import Categories.Diagram.Colimit using (Colimit)

open import Setoids-Colimit

module Setoids-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level

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

Fin≈ : ℕ → Setoid 0ℓ 0ℓ
Fin≈ n = setoid (Fin n)

setoids-LFP : WeaklyLFP (Setoids 0ℓ 0ℓ) 0ℓ 0ℓ 0ℓ filtered
setoids-LFP = record {
  I = ℕ ;
  𝒞-fp = Fin≈ ;
  all-I-fp = λ n 𝒟 𝒟-filtered J colim →
    let
      open Hom (Setoids 0ℓ 0ℓ)
      hom-n = Hom[ (Fin≈ n) ,-]
      module colim = Colimit colim
      open Category (Setoids 0ℓ 0ℓ)
    in
    bounded-colimiting
      (hom-n ∘F J)
      (F-map-Coconeˡ hom-n (colim.colimit))
      (filtered.bounds 𝒟-filtered)
      (λ (f : Fin≈ n ⇒ colim.coapex) → {!!})
      λ k → {!!};
  build-from-fp = {!!}
  }

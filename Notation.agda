{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Notation {o ℓ e} where

open import Level

record  singleton-hom (𝒞 : Category o ℓ e) (X Y : Category.Obj 𝒞) : Set (ℓ ⊔ e) where
  -- the fact that a hom-setoid (from X to Y) is a singleton (up to ≈)
  field
    arr : 𝒞 [ X , Y ]
    unique : ∀ (f : 𝒞 [ X , Y ]) → 𝒞 [ arr ≈ f ]

  unique₂ : ∀ (f g : 𝒞 [ X , Y ]) → 𝒞 [ f ≈ g ]
  unique₂ f g =
    let open Category 𝒞 in
    Equiv.trans (Equiv.sym (unique f)) (unique g)

_[_=∃!=>_] : (𝒞 : Category o ℓ e) (X Y : Category.Obj 𝒞) → Set _
_[_=∃!=>_] = singleton-hom

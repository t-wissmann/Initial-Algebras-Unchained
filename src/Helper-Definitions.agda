{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Helper-Definitions {o ℓ e} where

open import Level

record Full-≈  {𝒞 : Category o ℓ e} {o' ℓ' e' : Level} {𝒟 : Category o' ℓ' e'} (F : Functor 𝒟 𝒞) : Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where
  -- A more explicit definition of 'Full'ness of a functor F.
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module F = Functor F
  field
    preimage : ∀ (X Y : 𝒟.Obj) → 𝒞 [ F.₀ X , F.₀ Y ] → 𝒟 [ X , Y ]
    preimage-prop : ∀ (X Y : 𝒟.Obj) → (f : 𝒞 [ F.₀ X , F.₀ Y ]) → 𝒞 [ F.₁ (preimage X Y f) ≈ f ]


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

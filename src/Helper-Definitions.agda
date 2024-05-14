{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Data.Product
open import Categories.Morphism
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.Construction.Cocones
open import Categories.Functor

module Helper-Definitions where
open import Level

_[_≅_] : {o ℓ e : Level} (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set _
_[_≅_] 𝒞 A B = _≅_ 𝒞 A B

record Full-≈ {o ℓ e} {𝒞 : Category o ℓ e} {o' ℓ' e' : Level} {𝒟 : Category o' ℓ' e'} (F : Functor 𝒟 𝒞) : Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where
  -- A more explicit definition of 'Full'ness of a functor F.
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module F = Functor F
  field
    preimage : ∀ (X Y : 𝒟.Obj) → 𝒞 [ F.₀ X , F.₀ Y ] → 𝒟 [ X , Y ]
    preimage-prop : ∀ (X Y : 𝒟.Obj) → (f : 𝒞 [ F.₀ X , F.₀ Y ]) → 𝒞 [ F.₁ (preimage X Y f) ≈ f ]


record  singleton-hom {o ℓ e} (𝒞 : Category o ℓ e) (X Y : Category.Obj 𝒞) : Set (ℓ ⊔ e) where
  -- the fact that a hom-setoid (from X to Y) is a singleton (up to ≈)
  field
    arr : 𝒞 [ X , Y ]
    unique : ∀ (f : 𝒞 [ X , Y ]) → 𝒞 [ arr ≈ f ]

  unique₂ : ∀ (f g : 𝒞 [ X , Y ]) → 𝒞 [ f ≈ g ]
  unique₂ f g =
    let open Category 𝒞 in
    Equiv.trans (Equiv.sym (unique f)) (unique g)

_[_=∃!=>_] : {o ℓ e : Level} → (𝒞 : Category o ℓ e) (X Y : Category.Obj 𝒞) → Set _
_[_=∃!=>_] = singleton-hom


_<===>_ : ∀ {a b : Level} → Set a → Set b → Set (a ⊔ b)
_<===>_ x y = (x → y) × (y → x)
infix -5 _<===>_

private
  variable
    o ℓ e : Level
    C D J J′ : Category o ℓ e

module _ {F : Functor J C} (G : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module CF = Cocone F
    GF = G ∘F F
    module CGF = Cocone GF

  F-map-Cocone-Functor : Functor (Cocones F) (Cocones (G ∘F F))
  F-map-Cocone-Functor = record
     { F₀ = F-map-Coconeˡ G
     ; F₁ = F-map-Cocone⇒ˡ G
     ; identity = λ {A} → G.identity
     ; homomorphism = λ {X} {Y} {Z} {f} {g} → G.homomorphism
     ; F-resp-≈ = G.F-resp-≈
     }

{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Construction.Comma
open import Categories.Functor.Construction.Constant
open import Categories.Diagram.Colimit using (Colimit; transport-by-iso)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties

module Cofinal where

open import Unchained-Utils

private
  variable
    -- levels for the diagram scheme:
    o ℓ e : Level
    o' ℓ' e' : Level
    o'' ℓ'' e'' : Level
    -- diagram scheme:
    𝒟 : Category o' ℓ' e'
    ℰ : Category o'' ℓ'' e''

-- First the definition of connected category:
module _ (𝒞 : Category o ℓ e) where
  private
    module 𝒞 = Category 𝒞

  data ZigZag : 𝒞.Obj → 𝒞.Obj → Set (o ⊔ ℓ) where
    nil : ∀ (A : 𝒞.Obj) → ZigZag A A
    forward : ∀ (A B C : 𝒞.Obj) → (A 𝒞.⇒ B) → ZigZag B C → ZigZag A C
    backward : ∀ (A B C : 𝒞.Obj) → (B 𝒞.⇒ A) → ZigZag B C → ZigZag A C

  record Connected : Set (o ⊔ ℓ) where
    field
      -- a category is connected
      -- if any two objects are connected by a zigzag
      connect : ∀ (A B : 𝒞.Obj) → ZigZag A B

module _ {ℰ : Category o'' ℓ'' e''} {𝒟 : Category o' ℓ' e'} where
  private
    module 𝒟 = Category 𝒟
    module ℰ = Category ℰ

  Comma_/_ : 𝒟.Obj → (E : Functor ℰ 𝒟) → Category _ _ _
  Comma_/_ d E = Comma (const! d) E

  record Final (E : Functor ℰ 𝒟) : Set (o'' ⊔ ℓ'' ⊔ o' ⊔ ℓ' ⊔ e') where
    field
      non-empty : ∀ (d : 𝒟.Obj) → Category.Obj (Comma d / E)
      connect : ∀ (d : 𝒟.Obj) → Connected (Comma d / E)

  final-pulls-colimit : {𝒞 : Category o ℓ e} (D : Functor 𝒟 𝒞) (E : Functor ℰ 𝒟)
                        → Final E
                        → Colimit D
                        → Colimit (D ∘F E)
  final-pulls-colimit {𝒞 = 𝒞} D E Final-E colimit-D = {!!}
    where
      module colimit-D = Colimit colimit-D
      module E = Functor E
      module D = Functor D

      η-codom : 𝒟.Obj → ℰ.Obj
      η-codom d = CommaObj.β (Final.non-empty Final-E d)

      η : ∀ (d : 𝒟.Obj) → (d 𝒟.⇒ E.₀ (η-codom d))
      η d = CommaObj.f (Final.non-empty Final-E d)

      cocone-D∘E : Cocone (D ∘F E)
      cocone-D∘E = record { coapex = record {
          ψ = λ X → colimit-D.proj (E.₀ X) ;
          commute = λ f → colimit-D.colimit-commute (E.₁ f)
        } }

      -- but we can also transform cocones in the other direction
      reflect-ψ : ∀ (K : Cocone (D ∘F E)) (d : 𝒟.Obj) → 𝒞 [ D.₀ d , {!!} ]
      reflect-ψ K d = {!!}

      cocone-reflect : Cocone (D ∘F E) → Cocone D
      cocone-reflect K = record { coapex = record {
          ψ = λ d →
              {!η-!}
              ;
          commute = {!!}
        } }
        where
          module K = Cocone K

      -- cocone-mor : ∀ (K : Cocone (D ∘F E)) → Cocone⇒ _ cocone-D∘E K
      -- cocone-mor = {!!}

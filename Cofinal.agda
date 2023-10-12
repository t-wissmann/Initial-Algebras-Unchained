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

  record Final (E : Functor ℰ 𝒟) : Set (o'' ⊔ ℓ'' ⊔ o' ⊔ ℓ' ⊔ e') where
    field
      non-empty : ∀ (d : 𝒟.Obj) → Category.Obj (d ↙ E)
      connect : ∀ (d : 𝒟.Obj) → Connected (d ↙ E)

  final-pulls-colimit : {𝒞 : Category o ℓ e} (D : Functor 𝒟 𝒞) (E : Functor ℰ 𝒟)
                        → Final E
                        → Colimit D
                        → Colimit (D ∘F E)
  final-pulls-colimit {𝒞 = 𝒞} D E Final-E colimit-D = {!!}
    where
      module colimit-D = Colimit colimit-D
      module E = Functor E
      module D = Functor D
      module 𝒞 = Category 𝒞

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
      module cocone-reflection (K : Cocone (D ∘F E)) where
        -- first some lemmas when we fix a 𝒟 object d:
        private
          module K = Cocone K
        module _  (d : 𝒟.Obj) where
          private
            module d/E = Category (d ↙ E)

          open Category 𝒞
          open HomReasoning

          eval-comma : d/E.Obj → 𝒞 [ D.₀ d , K.N ]
          eval-comma f = K.ψ (CommaObj.β f) 𝒞.∘ D.₁ (CommaObj.f f)

          reflect-ψ : 𝒞 [ D.₀ d , K.N ]
          reflect-ψ = K.ψ (η-codom d) 𝒞.∘ D.₁ (η d)

          -- this η is kind of a 'choice', which we now prove
          -- to be well-defined:
          zigzag-commutes : (A B : d/E.Obj) → ZigZag (d ↙ E) A B →
                            𝒞 [ eval-comma A ≈ eval-comma B ]
          zigzag-commutes A .A (nil .A) = 𝒞.Equiv.refl
          zigzag-commutes A C (forward .A B .C f B/C) = ?
          zigzag-commutes A C (backward .A B .C f zz) = {!!}


        to-D-cocone : Cocone D
        to-D-cocone = record { coapex = record {
            ψ = λ d → reflect-ψ d
                ;
            commute = {!!}
          } }

      -- cocone-mor : ∀ (K : Cocone (D ∘F E)) → Cocone⇒ _ cocone-D∘E K
      -- cocone-mor = {!!}

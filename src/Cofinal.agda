{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Construction.Comma
open import Categories.Functor.Construction.Constant
open import Categories.Diagram.Colimit using (Colimit; transport-by-iso)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties

module Cofinal where

open import Colimit-Lemmas

-- Formalization that (co)final diagrams have the same colimit.
-- See also: https://ncatlab.org/nlab/show/final+functor

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
      every-slice-connected : ∀ (d : 𝒟.Obj) → Connected (d ↙ E)

    zigzag : ∀ (d : 𝒟.Obj) → ∀ (A B : Category.Obj (d ↙ E)) → ZigZag (d ↙ E) A B
    zigzag d A B = Connected.connect (every-slice-connected d) A B

  final-pulls-colimit : {𝒞 : Category o ℓ e} (D : Functor 𝒟 𝒞) (E : Functor ℰ 𝒟)
                        → Final E
                        → Colimit D
                        → Colimit (D ∘F E)
  final-pulls-colimit {𝒞 = 𝒞} D E Final-E colimit-D =
    record {
      initial = record {
        ⊥ = cocone-D∘E ;
        ⊥-is-initial =
          let
              open Category 𝒞
              open HomReasoning
          in record {
          ! = λ {K} →
            let
                module K = Cocone K
                open cocone-reflection K
            in
            record {
              arr = colimit-D.rep to-D-cocone ;
              commute = λ {X} →
                let
                  id-EX : Category.Obj ((E.₀ X) ↙ E)
                  id-EX = record { f = 𝒟.id {E.₀ X} }
                in
                begin
                colimit-D.rep to-D-cocone ∘ cocone-D∘E.ψ X
                  ≡⟨⟩
                colimit-D.rep to-D-cocone ∘ colimit-D.proj (E.₀ X)
                  ≈⟨ colimit-D.commute ⟩
                Cocone.ψ to-D-cocone (E.₀ X)
                  ≡⟨⟩
                eval-comma (η (E.₀ X))
                  ≈⟨ eval-comma-constant (E.₀ X) (η (E.₀ X)) id-EX ⟩
                eval-comma id-EX
                  ≈⟨ (refl⟩∘⟨ D.identity) ○ 𝒞.identityʳ ⟩
                K.ψ  X
                ∎
            } ;
          !-unique =
             λ {K} other →
                colimit-is-jointly-epic colimit-D (λ d →
                let
                    module K = Cocone K
                    open cocone-reflection K
                    module other = Cocone⇒ other
                in
                begin
                colimit-D.rep to-D-cocone ∘ colimit-D.proj d
                  ≈⟨ colimit-D.commute ⟩
                eval-comma (η d)
                  ≡⟨⟩
                K.ψ (η-codom d) ∘ D.₁ (η-mor d)
                  ≈˘⟨ other.commute ⟩∘⟨refl ⟩
                (other.arr ∘ cocone-D∘E.ψ (η-codom d)) ∘ D.₁ (η-mor d)
                  ≈⟨ assoc ⟩
                other.arr ∘ (colimit-D.proj (E.₀ (η-codom d)) ∘ D.₁ (η-mor d))
                  ≈⟨ refl⟩∘⟨ colimit-D.colimit-commute (η-mor d) ⟩
                other.arr ∘ colimit-D.proj d
                ∎
                )
          }
      }
    }
    where
      module colimit-D = Colimit colimit-D
      module E = Functor E
      module D = Functor D
      module 𝒞 = Category 𝒞

      η : ∀ (d : 𝒟.Obj) → Category.Obj (d ↙ E)
      η d = Final.non-empty Final-E d

      η-codom : 𝒟.Obj → ℰ.Obj
      η-codom d = CommaObj.β (Final.non-empty Final-E d)

      η-mor : ∀ (d : 𝒟.Obj) → (d 𝒟.⇒ E.₀ (η-codom d))
      η-mor d = CommaObj.f (Final.non-empty Final-E d)

      cocone-D∘E : Cocone (D ∘F E)
      cocone-D∘E = record { coapex = record {
          ψ = λ X → colimit-D.proj (E.₀ X) ;
          commute = λ f → colimit-D.colimit-commute (E.₁ f)
        } }
      module cocone-D∘E = Cocone cocone-D∘E

      -- but we can also transform cocones in the other direction
      module cocone-reflection (K : Cocone (D ∘F E)) where
        -- first some lemmas when we fix a 𝒟 object d:
        private
          module K = Cocone K

        eval-comma : ∀ {d : 𝒟.Obj} → Category.Obj (d ↙ E) → 𝒞 [ D.₀ d , K.N ]
        eval-comma f = K.ψ (CommaObj.β f) 𝒞.∘ D.₁ (CommaObj.f f)

        module _  (d : 𝒟.Obj) where
          private
            module d/E = Category (d ↙ E)

          open Category 𝒞
          open HomReasoning

          -- this η is kind of a 'choice', which we now prove
          -- to be well-defined:
          -- First for comma objects that are linked directly:
          Comma⇒-commutes : {A B : d/E.Obj} → (h : Comma⇒ A B) →
                            𝒞 [ eval-comma A ≈ eval-comma B ]
          Comma⇒-commutes {A} {B} h =
            begin
            K.ψ (CommaObj.β A) ∘ D.₁ (CommaObj.f A)
            ≈˘⟨ K.commute (Comma⇒.h h) ⟩∘⟨refl ⟩
            (K.ψ (CommaObj.β B) ∘ D.₁ (E.₁ (Comma⇒.h h))) ∘ D.₁ (CommaObj.f A)
            ≈⟨ assoc ⟩
            K.ψ (CommaObj.β B) ∘ D.₁ (E.₁ (Comma⇒.h h)) ∘ D.₁ (CommaObj.f A)
            ≈˘⟨ refl⟩∘⟨ D.homomorphism ⟩
            K.ψ (CommaObj.β B) ∘ D.₁ (E.₁ (Comma⇒.h h) 𝒟.∘ (CommaObj.f A))
            ≈⟨ refl⟩∘⟨ D.F-resp-≈ (Comma⇒.commute h ) ⟩
            K.ψ (CommaObj.β B) ∘ D.₁ ((CommaObj.f B) 𝒟.∘ 𝒟.id)
            ≈⟨ refl⟩∘⟨ D.F-resp-≈ 𝒟.identityʳ  ⟩
            K.ψ (CommaObj.β B) ∘ D.₁ (CommaObj.f B)
            ∎

          -- And then for comma objects that are linked transitively along
          -- zigzags:
          zigzag-commutes : {A B : d/E.Obj} → ZigZag (d ↙ E) A B →
                            𝒞 [ eval-comma A ≈ eval-comma B ]
          zigzag-commutes {A} (nil A) = 𝒞.Equiv.refl
          zigzag-commutes {A} {C} (forward .A B .C h B-zz-C) =
             Comma⇒-commutes h ○ zigzag-commutes B-zz-C
          zigzag-commutes {A} {C} (backward .A B .C h B-zz-C) =
            ⟺ (Comma⇒-commutes h) ○ zigzag-commutes B-zz-C

          eval-comma-constant : (A B : d/E.Obj) → 𝒞 [ eval-comma A ≈ eval-comma B ]
          eval-comma-constant A B = zigzag-commutes (Final.zigzag Final-E d A B)


        to-D-cocone : Cocone D
        to-D-cocone = record { coapex = record {
            ψ = λ d → eval-comma (η d)
                ;
            commute = λ {d} {d'} f →
              let
                via-d' : Category.Obj (d ↙ E)
                via-d' = record { f = η-mor d' 𝒟.∘ f }
              in
              begin
              eval-comma (η d') ∘ D.F₁ f ≈⟨ assoc ⟩
              K.ψ (η-codom d') ∘ D.₁ (η-mor d') ∘ D.F₁ f ≈˘⟨ refl⟩∘⟨ D.homomorphism ⟩
              K.ψ (η-codom d') ∘ D.₁ (η-mor d' 𝒟.∘ f) ≡⟨⟩
              eval-comma via-d' ≈⟨ eval-comma-constant d via-d' (η d) ⟩
              eval-comma (η d)
              ∎
          } }
          where
            open Category 𝒞
            open HomReasoning

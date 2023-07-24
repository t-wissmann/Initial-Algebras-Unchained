{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Unchained-Utils {o ℓ e} {C : Category o ℓ e} where

open import Level

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.Cocones using (Cocones)
open import Categories.Functor.Coalgebra
open import Categories.Morphism using (_≅_)
open import Categories.Object.Initial using (IsInitial)

open import Categories.Diagram.Colimit using (Colimit; transport-by-iso)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Functor using (_∘F_)
open import Agda.Builtin.Equality

open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory using (FullSub)

-- the property whether a Sink is jointly epic:
jointly-epic : ∀ {i : Level} {I : Set i} {dom : I → Category.Obj C} {codom : Category.Obj C}
               (sink : (x : I) → C [ dom x , codom ]) → Set _
jointly-epic {i} {I} {dom} {codom} sink =
  ∀ (Z : Category.Obj C) (g h : C [ codom , Z ]) →
    (∀ (x : I) → C [ C [ g ∘ sink x ] ≈ C [ h ∘ sink x ] ]) →
    C [ g ≈ h ]

-- FullSubCategory (F-Coalgebras F) R-Coalgebra.coalg
FullSub-Colimit : {o' ℓ' e' i : Level}
                → {D : Category o' ℓ' e'}
                → {I : Set i}
                → (U : I → Category.Obj C)
                → (J : Functor D (FullSubCategory C U))
                → (C-colim : Colimit (FullSub C ∘F  J))
                → (lifted-colim-obj : I)
                → _≅_ C (Colimit.coapex C-colim) (U lifted-colim-obj)
                → Colimit J
FullSub-Colimit {D = D} {I = I} U J plain-C-colim lifted-colim-obj iso =
  let
    C-colim = (transport-by-iso (FullSub C ∘F  J) plain-C-colim iso)
    module C-colim = Colimit (C-colim)
    open Category C
    open HomReasoning
    module J = Functor J
    module iso = _≅_ iso

    -- by the transport, we have a colimit on an object in the subcategory:
    test : C-colim.coapex ≡ U lifted-colim-obj
    test = refl
    -- so, we now only need to lift the colimit along 'U'

    Sub-Cocone : Cocone J
    Sub-Cocone = record {
      N = lifted-colim-obj ;
      coapex = record { ψ = C-colim.proj ; commute = C-colim.colimit-commute } }

    Sub-Cocone-ump : {other : Cocone J} → Cocone⇒ J Sub-Cocone other
    Sub-Cocone-ump {other} =
      let
        module other = Cocone other
        C-other : Cocone (FullSub C ∘F J)
        C-other = (F-map-Coconeˡ (FullSub C) other)
        morph : C [ C-colim.coapex , U other.N ]
        morph = Cocone⇒.arr (C-colim.initial.! {A = C-other})
      in
      record {
        arr = morph ;
        commute = λ {X} →
          Cocone⇒.commute (C-colim.initial.! {A = C-other})
        }
    Sub-Cocone-initial : IsInitial (Cocones J) Sub-Cocone
    Sub-Cocone-initial = record {
      ! = Sub-Cocone-ump ;
      !-unique = λ {other : Cocone J} cocone-morph →
        let
          module other = Cocone other
          module cocone-morph = Cocone⇒ cocone-morph
          C-other : Cocone (FullSub C ∘F J)
          C-other = (F-map-Coconeˡ (FullSub C) other)

          -- send the cocone 'other' down to C:
          C-cocone-morph : Cocone⇒ (FullSub C ∘F J) C-colim.colimit C-other
          C-cocone-morph = record {
            arr = cocone-morph.arr ;
            commute = λ {X} → cocone-morph.commute }
        in
        IsInitial.!-unique C-colim.initial.⊥-is-initial C-cocone-morph
      }
  in
  record { initial = record { ⊥ = Sub-Cocone ; ⊥-is-initial = Sub-Cocone-initial } }

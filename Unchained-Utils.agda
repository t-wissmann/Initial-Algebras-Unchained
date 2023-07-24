{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Unchained-Utils {o ℓ e} {C : Category o ℓ e} where

open import Level

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Morphism using (_≅_)
open import Categories.Object.Initial using (IsInitial)

open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone
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
                → _≅_ C (U lifted-colim-obj) (Colimit.coapex C-colim)
                → Colimit J
FullSub-Colimit {D = D} {I = I} U J C-colim lifted-colim-obj iso =
  let
    module C-colim = Colimit C-colim
    open Category C
    open HomReasoning
    module J = Functor J
    module iso = _≅_ iso
  in
  record { initial = record {
    ⊥ = record {
      N = lifted-colim-obj ;
      coapex = record {
        ψ = λ X → iso.to ∘ C-colim.proj X ;
        commute = λ {X} {X'} f → begin
          (iso.to ∘ C-colim.proj X') ∘ J.F₁ f ≈⟨ assoc ⟩
          iso.to ∘ (C-colim.proj X' ∘ J.F₁ f) ≈⟨ refl⟩∘⟨ C-colim.colimit-commute f ⟩
          iso.to ∘ C-colim.proj X
          ∎}
      } ;
    ⊥-is-initial =
      record {
        ! = record { arr = ? ; commute = ? } ;
        !-unique = {!!}
      }
    } }

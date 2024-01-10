{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Diagram.Colimit
open import Categories.Object.Initial
open import Categories.Category.Construction.Cocones
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.Lift

open import Unchained-Utils
open import Filtered

module Lift-Diagram {o ℓ o' ℓ' e' o'' ℓ'' e'' fil-level}
  (𝒞 : Category o ℓ ℓ)
  -- (Fil : Category (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') → Set fil-level) -- some variant of 'filtered'
  where

open import Presented {fil-level = fil-level} 𝒞
open import Hom-Colimit-Choice 𝒞
open LiftHom

private
  module 𝒞 = Category 𝒞

unlift-presented : ∀ {X : 𝒞.Obj} → presented (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') Fil X →
  ∀ (𝒟 : Category o'' ℓ'' e'') → -- forall diagram schemes
  Fil (liftC (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') 𝒟) →       -- satisfying some notion of filteredness
  (J : Functor 𝒟 𝒞) →            -- and all their diagrams
  preserves-colimit J LiftHom[ X ,-]-lowered -- the hom-functor preserves all (existing) colimits
unlift-presented {X} X-pres 𝒟 𝒟-Fil J colim-J =
  record {
    ! = λ {other} →
      record {
        arr = {!!} ;
        commute = {!!} } ;
    !-unique = {!!}
  }
  where
    module J = Functor J
    module colim-J = Colimit colim-J
    unliftF' = unliftF (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') 𝒟
    unlift-Cocone : Cocone (J ∘F unliftF') → Cocone J
    unlift-Cocone cocone =
      let module cocone = Cocone _ cocone in
      record { coapex =
        record {
          ψ = λ x → cocone.ψ (lift x) ;
          commute = λ f → cocone.commute (lift f) } }

    unlift-Cocone⇒ : (C : Cocone J) → (C' : Cocone (J ∘F unliftF')) →
                     Cocone⇒ (J ∘F unliftF') (F-map-Coconeʳ unliftF' C) C' →
                     Cocone⇒ J C (unlift-Cocone C')
    unlift-Cocone⇒ C C' morph =
      record {
        arr = Cocone⇒.arr morph ; commute = Cocone⇒.commute morph }

    colim-J∘unliftF : Colimit (J ∘F unliftF')
    colim-J∘unliftF =
      record { initial = record {
        ⊥ = F-map-Coconeʳ (unliftF') colim-J.colimit
        ; ⊥-is-initial =
          record {
            ! = λ {other} →
              F-map-Cocone⇒ʳ unliftF' (colim-J.rep-cocone (unlift-Cocone other)) ;
            !-unique = λ {other} to-other →
              colim-J.initial.!-unique (unlift-Cocone⇒ colim-J.colimit other to-other)
          }
      } }

    higher-initial : IsInitial
      (Cocones (LiftHom[ X ,-]-higher ∘F J ∘F unliftF'))
      (F-map-Coconeˡ (LiftHom[ X ,-]-higher) (F-map-Coconeʳ unliftF' colim-J.colimit))
    higher-initial =
      X-pres
        (liftC (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') 𝒟)
        𝒟-Fil
        (J ∘F unliftF')
        colim-J∘unliftF

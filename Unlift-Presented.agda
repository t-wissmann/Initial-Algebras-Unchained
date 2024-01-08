{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Diagram.Colimit
open import Categories.Category.Lift

open import Unchained-Utils
open import Filtered

module Unlift-Presented {o ℓ o' ℓ' e' o'' ℓ'' e'' fil-level}
  (𝒞 : Category o ℓ ℓ)
  (Fil : Category (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') → Set fil-level) -- some variant of 'filtered'
  where

open import Presented {fil-level = fil-level} 𝒞
open import Hom-Colimit-Choice 𝒞
open LiftHom

private
  module 𝒞 = Category 𝒞

unlift-presented : ∀ {X : 𝒞.Obj} → presented (o' ⊔ o'') (ℓ' ⊔ ℓ'') (e' ⊔ e'') Fil X →
  ∀ (𝒟 : Category o'' ℓ'' e'') → -- forall diagram schemes
  Fil (liftC o' ℓ' e' 𝒟) →       -- satisfying some notion of filteredness
  (J : Functor 𝒟 𝒞) →            -- and all their diagrams
  preserves-colimit J (LiftHom[_,-] o'' ℓ'' e'' X) -- the hom-functor preserves all (existing) colimits
unlift-presented = {!!}

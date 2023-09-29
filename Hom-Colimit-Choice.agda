{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Diagram.Colimit

open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

import Setoids-Choice as Setoids
open import Unchained-Utils

module Hom-Colimit-Choice
  {o ℓ e} {𝒞 : Category o ℓ e}
  {o' ℓ' e'} {𝒟 : Category o' ℓ' e'}
  {D : Functor 𝒟 𝒞}
  (colim : Colimit D)
  where

open Hom 𝒞

module 𝒞 = Category 𝒞
module colim = Colimit colim
module 𝒟 = Category 𝒟
module D = Functor D

open Category 𝒞

record Triangle {P : 𝒞.Obj} (p : P ⇒ colim.coapex) : Set (o' ⊔ ℓ ⊔ e) where
  -- a factorization of a morphism through the diagram.
  field
    x : 𝒟.Obj
    p' : P ⇒ D.₀ x
    commutes : p ≈ colim.proj x ∘ p'

hom-colim-choice : (P : 𝒞.Obj) →
    preserves-colimit D (Hom[ P ,-]) →
    (p : P ⇒ colim.coapex) →
    Triangle p
hom-colim-choice P hom-preserves-colim p =
  let
    homset-colimit = Colimit-from-prop (hom-preserves-colim colim)
    -- x , p' = Setoids.colimit-choice homset-colimit p
  in
  record { x = {!!} ; p' = {!!} ; commutes = {!!} }

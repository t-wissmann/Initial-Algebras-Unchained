{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Data.Product

open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Functor.Construction.LiftSetoids
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
    preserves-colimit D (LiftSetoids (ℓ ⊔ o') (o' ⊔ ℓ' ⊔ e ⊔ ℓ) ∘F Hom[ P ,-]) →
    (p : P ⇒ colim.coapex) →
    Triangle p
hom-colim-choice P hom-preserves-colim p =
  let
    homset-colimit = Colimit-from-prop (hom-preserves-colim colim)
    module homset-colimit = Colimit homset-colimit

    x , p' = Setoids.colimit-choice {o'} {ℓ'} {e'} {ℓ ⊔ o'} {o' ⊔ ℓ' ⊔ e ⊔ ℓ} homset-colimit (lift p)

    open Setoid renaming (_≈_ to _[[_≈_]])
    commutes : homset-colimit.coapex [[ (lift p) ≈ homset-colimit.proj x ⟨$⟩ p' ]]
    commutes =
      (Setoids.colimit-choice-correct {o'} {ℓ'} {e'} {ℓ ⊔ o'} {o' ⊔ ℓ' ⊔ e ⊔ ℓ} homset-colimit {lift p})

    -- since hom functors are defined as bi-functor, we have an ∘id on the right:
    commutes-in-𝒞 : p ≈ colim.proj x ∘ (lower p') ∘ id
    commutes-in-𝒞 = lower commutes

    open HomReasoning
  in
  record { x = x ; p' = lower p' ;
    commutes =
      begin
      p                            ≈⟨ commutes-in-𝒞 ⟩
      colim.proj x ∘ (lower p') ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
      colim.proj x ∘ (lower p')
      ∎
    }

{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Filtered
open import LFP
open import Data.Nat.Base using (ℕ)
open import Data.Fin
open import Data.Product
open import Function.Equality hiding (≡-setoid; setoid; _∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Categories.Diagram.Cocone.Properties
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Functor.Construction.LiftSetoids
import Relation.Binary.Reasoning.Setoid as SetoidR


open import Setoids-Colimit
open import Setoids-Choice

module Setoids-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level

-- we use a custom 'setoid' variation to achieve arbitrary levels o, ℓ
≡-setoid : ∀ {o ℓ : Level} → Set 0ℓ → Setoid o ℓ
≡-setoid {o} {ℓ} X =
  record { Carrier = Lift o X
  ; _≈_ = λ (lift x₁) (lift x₂) → L.Lift ℓ (x₁ ≡ x₂)
  ; isEquivalence =
    record {
      refl = Level.lift refl ;
      sym = λ (L.lift eq) → Level.lift (sym eq) ;
      trans = λ (L.lift x≡y) (L.lift y≡z) → Level.lift (trans x≡y y≡z) } }

Fin≈ : ℕ → Setoid 0ℓ 0ℓ
Fin≈ n = setoid (Fin n)

Fin-is-presented : ∀ (n : ℕ) → presented (Setoids 0ℓ 0ℓ) 0ℓ 0ℓ 0ℓ filtered (Fin≈ n)
Fin-is-presented n 𝒟 𝒟-filtered J colim =
  let
    open Hom (Setoids 0ℓ 0ℓ)
    hom-n = Hom[ (Fin≈ n) ,-]
    lift-hom-n = LiftSetoids 0ℓ 0ℓ ∘F hom-n
    module colim = Colimit colim
    open Category (Setoids 0ℓ 0ℓ)
    module 𝒟 = Category 𝒟
    module J = Functor J
    module 𝒟-filtered = filtered 𝒟-filtered
  in
  bounded-colimiting
    (lift-hom-n ∘F J)
    (F-map-Coconeˡ lift-hom-n (colim.colimit))
    𝒟-filtered.bounds
    (λ (lift f) →
      let
        -- f is essentially a tuple of elements of the colimit:
        _ : Fin n → Setoid.Carrier colim.coapex
        _ = λ k → f ⟨$⟩ k
        -- since 'colim' is a colimit in setoids, every element
        -- of the family 'f' comes from some object in the diagram
        source-objects : Fin n → 𝒟.Obj
        source-objects k = proj₁ (colimit-choice colim (f ⟨$⟩ k))

        -- the diagram is filtered, so these objects have an upper bound:
        B : 𝒟.Obj
        B = 𝒟-filtered.fin-upper-bound source-objects

        -- and so f factors through it:
        g : Fin n → Setoid.Carrier (J.₀ B)
        g k =
          J.₁ (𝒟-filtered.fin-is-above source-objects k)
          ⟨$⟩ proj₂ (colimit-choice colim (f ⟨$⟩ k))


        open Setoid renaming (_≈_ to _[[_≈_]])
        g-correct : (k : Fin n) → colim.coapex [[ (f ⟨$⟩ k) ≈ colim.proj B ⟨$⟩ (g k) ]]
        g-correct k =
          let
            open SetoidR (colim.coapex)
            X , xₖ = colimit-choice colim (f ⟨$⟩ k)
            connecting-morph = 𝒟-filtered.fin-is-above source-objects k
          in
          begin
          (f ⟨$⟩ k)                   ≈⟨ colimit-choice-correct colim ⟩
          colim.proj X ⟨$⟩ xₖ         ≈˘⟨ colim.colimit-commute connecting-morph (Setoid.refl _) ⟩
          (colim.proj B ∘ J.₁ connecting-morph) ⟨$⟩ xₖ        ≡⟨⟩
          colim.proj B ⟨$⟩ (J.₁ connecting-morph ⟨$⟩ xₖ)       ≡⟨⟩
          colim.proj B ⟨$⟩ (g k)
          ∎
      in
      {!!})
    λ k → {!!}


setoids-LFP : WeaklyLFP (Setoids 0ℓ 0ℓ) 0ℓ 0ℓ 0ℓ filtered
setoids-LFP = record {
  Idx = ℕ ;
  fin = Fin≈ ;
  fin-presented = Fin-is-presented ;
  build-from-fin = λ X → {!!}
  }

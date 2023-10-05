{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Category.SubCategory
open import Categories.Functor using (Functor; Endofunctor; _∘F_)
open import Categories.Functor.Coalgebra hiding (to-Coalgebra)
open import Categories.Category.Construction.F-Coalgebras
import Categories.Functor.Coalgebra as Coalg
open import Categories.Functor.Construction.SubCategory
open import Categories.Diagram.Colimit

open import F-Coalgebra-Colimit

module Prop-Coalgebra {o ℓ e}
  {P-level : Level}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (Prop : F-Coalgebra F → Set P-level)  -- a property of coalgebras
  where

open import LFP 𝒞

private
  module 𝒞 = Category 𝒞
  module F = Functor F

record LProp-Coalgebra {o' ℓ' e'} : Set (o ⊔ ℓ ⊔ e ⊔ P-level ⊔ suc (o' ⊔ ℓ' ⊔ e')) where
  -- A locally finite coalgebra is a colimit of coalgebras whose carriers
  -- all satisfies a fixed property.
  field
    -- So it consists of: 1. a diagram scheme
    𝒟 : Category o' ℓ' e'
    -- 2. a diagram in coalgebras:
    D : Functor 𝒟 (F-Coalgebras F)
    -- 3. whose all satisfiy a given property:
    all-have-prop : ∀ {i : Category.Obj 𝒟} → Prop (Functor.₀ D i)
    -- 4. and a colimit in all coalgebras:
    carrier-colim : Colimit (forget-Coalgebra ∘F D)

  module D = Functor D
  module carrier-colim = Colimit carrier-colim

  colim : Colimit D
  colim = F-Coalgebras-Colimit D carrier-colim

  module colim = Colimit colim

  to-Coalgebra : F-Coalgebra F
  to-Coalgebra = colim.coapex

  -- the diagram 'D' restricted to the carriers / 𝒞-objects
  carrier-diagram : Functor 𝒟 𝒞
  carrier-diagram = forget-Coalgebra ∘F D

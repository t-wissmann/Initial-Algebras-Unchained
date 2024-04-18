{-# OPTIONS --without-K --safe #-}
-- Coalgebras:
-- 1. whose carrier comes from an indexed family
-- 2. satisfy a given property
open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory

open import F-Coalgebra-Colimit

module Coalgebra.IdxProp {o ℓ e : Level} (𝒞 : Category o ℓ e) (F : Endofunctor 𝒞)
                         {i : Level} {Idx : Set i} (family : Idx → Category.Obj 𝒞)
                         {prop-level : Level}  (P : F-Coalgebra F → Set prop-level)
                         where

private
  module 𝒞 = Category 𝒞

record IdxPropCoalgebra : Set (i ⊔ ℓ ⊔ prop-level) where
  -- a IdxProp coalgebra consists of one of the generators for 𝒞-lfp
  -- together with a coalgebra structure on it
  field
      carrier : Idx
      structure : F-Coalgebra-on F (family carrier)

  A,α : F-Coalgebra F
  A,α = to-Coalgebra structure
  open F-Coalgebra (A,α) public

  -- and moreover we require it to satisfy the property P:
  field
      has-prop : P A,α

-- such coalgebras define a full subcategory of all coalgebras:
IdxPropCoalgebras : Category (i ⊔ ℓ ⊔ prop-level) (e ⊔ ℓ) e
IdxPropCoalgebras = FullSubCategory (F-Coalgebras F) IdxPropCoalgebra.A,α

forget-IdxProp : Functor IdxPropCoalgebras (F-Coalgebras F)
forget-IdxProp = FullSub (F-Coalgebras F) {U = IdxPropCoalgebra.A,α}

forget-IdxPropCoalgebra : Functor IdxPropCoalgebras 𝒞
forget-IdxPropCoalgebra = forget-Coalgebra ∘F FullSub (F-Coalgebras F)


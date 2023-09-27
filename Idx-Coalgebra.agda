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

-- Coalgebras where the carrier comes from a fixed family of objects

module Idx-Coalgebra {o ℓ e}
  {P-level : Level}
  {Idx : Set ℓ}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (fin : Idx → Category.Obj 𝒞)    -- a family of 'finite' objects
  (P : F-Coalgebra F → Set P-level)  -- a property of coalgebras
  where

private
  module 𝒞 = Category 𝒞
  module F = Functor F

record Idx-Coalgebra : Set (ℓ ⊔ P-level) where
  -- A idx coalgebra with a property: Essentially, it lives on level ℓ,
  -- because the carrier is itself just the index of a finite object and then a
  -- coalgebra structure on the corresponding 𝒞 object:
  field
    carrier-idx : Idx
    structure : F-Coalgebra-on F (fin carrier-idx)
    has-prop : P (Coalg.to-Coalgebra structure)

  carrier : 𝒞.Obj
  carrier = fin carrier-idx

  to-Coalgebra : F-Coalgebra F
  to-Coalgebra = Coalg.to-Coalgebra structure

-- the full subcategory of finite coalgebras:
Idx-Coalgebras : Category (ℓ ⊔ P-level) (e ⊔ ℓ) e
Idx-Coalgebras = FullSubCategory (F-Coalgebras F) Idx-Coalgebra.to-Coalgebra

-- the forgetful functor to (plain) F-Coalgebras
Idx-Coalgebras-to-Coalg : Functor Idx-Coalgebras (F-Coalgebras F)
Idx-Coalgebras-to-Coalg = FullSub (F-Coalgebras F)

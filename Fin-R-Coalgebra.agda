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



module Fin-R-Coalgebra {o ℓ e}
  {P-level : Level}
  {Idx : Set ℓ}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (fin : Idx → Category.Obj 𝒞)    -- a family of 'finite' objects
  (P : F-Coalgebra F → Set P-level)  -- a property of coalgebras
  where

open import recursive-coalgebra 𝒞 F

module 𝒞 = Category 𝒞
module F = Functor F

record FinCoalgebra : Set (ℓ ⊔ P-level) where
  -- A finite coalgebra with a property: Essentially, it lives on level ℓ,
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
FinCoalgebras : Category (ℓ ⊔ P-level) (e ⊔ ℓ) e
FinCoalgebras = FullSubCategory (F-Coalgebras F) FinCoalgebra.to-Coalgebra

-- the forgetful functor to (plain) F-Coalgebras
FinCoalgebras-to-Coalg : Functor FinCoalgebras (F-Coalgebras F)
FinCoalgebras-to-Coalg = FullSub (F-Coalgebras F)

record LFinCoalgebra {o' ℓ' e'} : Set (o ⊔ ℓ ⊔ e ⊔ P-level ⊔ suc (o' ⊔ ℓ' ⊔ e')) where
  -- A locally finite coalgebra is a colimit of finite coalgebras.
  field
    -- So it consists of: 1. a diagram scheme
    𝒟 : Category o' ℓ' e'
    -- 2. a diagram in finite coalgebras:
    D : Functor 𝒟 FinCoalgebras
    -- 3. and a colimit in all coalgebras:
    colim : Colimit (FinCoalgebras-to-Coalg ∘F D)

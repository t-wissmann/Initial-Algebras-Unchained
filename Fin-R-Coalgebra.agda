{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Coalgebra
open import Categories.Functor.Construction.SubCategory using (FullSub)


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
  -- A finite coalgebra lives on level ℓ, because
  -- the carrier is itself just the index of a finite object
  -- and then a coalgebra structure on the corresponding 𝒞 object:
  field
    carrier-idx : Idx
    structure : F-Coalgebra-on F (fin carrier-idx)
    has-prop : P (to-Coalgebra structure)

  carrier : 𝒞.Obj
  carrier = fin carrier-idx

-- the full subcategory of finite coalgebras:
-- FinCoalgebras : FullSub

record LFinCoalgebra {o' ℓ' e'} : Set (ℓ ⊔ suc (o' ⊔ ℓ' ⊔ e')) where
  -- A locally finite coalgebra is a colimit of finite coalgebras
  field
    𝒟 : Category o' ℓ' e' -- a diagram scheme
    -- D : Functor 𝒟 {!!}

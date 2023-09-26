{-# OPTIONS --without-K #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Coalgebra

module Fin-R-Coalgebra {o ℓ e} {Idx : Set ℓ}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (fin : Idx → Category.Obj 𝒞) -- a family of 'finite' objects
  where

open import recursive-coalgebra 𝒞 F

module 𝒞 = Category 𝒞
module F = Functor F

record FinCoalgebra : Set (ℓ) where
  -- A finite coalgebra lives on level ℓ, because
  -- the carrier is itself just the index of a finite object
  -- and then a coalgebra structure on the corresponding 𝒞 object:
  field
    carrier-idx : Idx
    structure : F-Coalgebra-on F (fin carrier-idx)

  carrier : 𝒞.Obj
  carrier = fin carrier-idx

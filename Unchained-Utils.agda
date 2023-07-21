{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Unchained-Utils {o ℓ e} {C : Category o ℓ e} where

open import Level

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial using (IsInitial)

-- the property whether a Sink is jointly epic:
jointly-epic : ∀ {i : Level} {I : Set i} {dom : I → Category.Obj C} {codom : Category.Obj C}
               (sink : (x : I) → C [ dom x , codom ]) → Set _
jointly-epic {i} {I} {dom} {codom} sink =
  ∀ (Z : Category.Obj C) (g h : C [ codom , Z ]) →
    (∀ (x : I) → C [ C [ g ∘ sink x ] ≈ C [ h ∘ sink x ] ]) →
    C [ g ≈ h ]

{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Construction.SubCategory using (FullSub)
open import Categories.Functor using (Functor; Endofunctor)

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP
open import Filtered

-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ} (𝒞 : Category o ℓ ℓ) (F : Endofunctor 𝒞) where

open import recursive-coalgebra 𝒞 F

private
  variable
    -- levels of 'set'
    𝒟 : Category ℓ ℓ ℓ
    prop-level : Level

-- the following disables universe level checking.
-- This might be a workaround to the isse, but does it lead to
-- (known) inconsistencies?
{-# NO_UNIVERSE_CHECK #-}
record IsRecursiveHack {ℓ} : Set ℓ where
  field
    foo : (A : Set ℓ) → A

-- The global assumptions:
module _
  (P : Category ℓ ℓ ℓ → Set prop-level)
  (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
  (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ P)
  (𝒞-cocomplete : Cocomplete ℓ ℓ ℓ 𝒞)
  where

  module 𝒞-lfp = WeaklyLFP 𝒞-lfp
  module F = Functor F

  record FinCoalgebra : Set (ℓ) where
    field
      carrier : 𝒞-lfp.I
      structure : 𝒞 [ (𝒞-lfp.𝒞-fp carrier) , F.F₀(𝒞-lfp.𝒞-fp carrier) ]

    coalgebra : F-Coalgebra F
    coalgebra = to-Coalgebra structure

  record FinCoalgebraProp {p-lev : Level} (P : F-Coalgebra F → Set p-lev) : Set (ℓ ⊔ p-lev) where
    field
      fin-coalg : FinCoalgebra
      satisfies : P (FinCoalgebra.coalgebra fin-coalg)
    open FinCoalgebra fin-coalg public

  FCPSubCat : {p-lev : Level} (P : F-Coalgebra F → Set p-lev) → Category (ℓ ⊔ p-lev) ℓ ℓ
  FCPSubCat P = FullSubCategory (F-Coalgebras F) {I = FinCoalgebraProp P} FinCoalgebraProp.coalgebra
    where
      open import Categories.Category.SubCategory using (FullSubCategory)

  FinRCoalgebra : Set (o ⊔ ℓ)
  FinRCoalgebra = FinCoalgebraProp {o ⊔ ℓ} IsRecursive

  inj-FinRCoalgebra : FinRCoalgebra → R-Coalgebra
  inj-FinRCoalgebra coalg = record { coalg = coalgebra ; ump = satisfies }
    where open FinCoalgebraProp coalg

  R-Coalgebras-fp : Category (o ⊔ ℓ) ℓ ℓ
  R-Coalgebras-fp = FullSubCategory (R-Coalgebras) inj-FinRCoalgebra
    where open import Categories.Category.SubCategory using (FullSubCategory)

  R-Coalgebras-fp-functor : Functor R-Coalgebras-fp (F-Coalgebras F)
  R-Coalgebras-fp-functor = FullSub (F-Coalgebras F)

  module _ (fin-join : Colimit R-Coalgebras-fp-functor) where

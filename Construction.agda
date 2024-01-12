{-# OPTIONS --without-K #-}
open import Level

-- The construction in its most general Form

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Coalgebra
open import Categories.Diagram.Colimit
open import Categories.Category.SubCategory

open import Filtered
open import LFP using (WeaklyLFP)
open import CoalgColim
open import F-Coalgebra-Colimit
open import Data.Product
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Functor.Properties using (Full)
open import Function.Surjection using (Surjective)
open import Function.Equality hiding (_∘_)
open import Categories.Functor.Construction.SubCategory using (FullSub)

open import Notation
open import Unchained-Utils

module Construction {o ℓ}
  (𝒞 : Category (o ⊔ ℓ) ℓ ℓ)
  (F : Endofunctor 𝒞)
  {fil-level : Level}
  (Fil : Category (o ⊔ ℓ) ℓ ℓ → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category (o ⊔ ℓ) ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 (o ⊔ ℓ) ℓ ℓ Fil Fil-to-filtered)
  where

open import recursive-coalgebra 𝒞 F
open import Unique-Proj 𝒞 F Fil Fil-to-filtered 𝒞-lfp

private
    module 𝒞 = Category 𝒞
    module 𝒞-lfp = WeaklyLFP 𝒞-lfp

module FinProp {prop-level : Level} (P : F-Coalgebra F → Set prop-level) where
  record FinPropCoalgebra : Set (ℓ ⊔ prop-level) where
    -- a 'fin' coalgebra consists of one of the generators for 𝒞-lfp
    -- together with a coalgebra structure on it
    field
        carrier : 𝒞-lfp.Idx
        structure : F-Coalgebra-on F (𝒞-lfp.fin carrier)

    A,α : F-Coalgebra F
    A,α = to-Coalgebra structure
    open F-Coalgebra (A,α) public

    -- and moreover we require it to satisfy the property P:
    field
        has-prop : P A,α

    -- such coalgebras define a full subcategory of all coalgebras:
  FinPropCoalgebras : Category (ℓ ⊔ prop-level) ℓ ℓ
  FinPropCoalgebras = FullSubCategory (F-Coalgebras F) FinPropCoalgebra.A,α

  forget-FinProp : Functor FinPropCoalgebras (F-Coalgebras F)
  forget-FinProp = FullSub (F-Coalgebras F)

  forget-FinPropCoalgebra : Functor FinPropCoalgebras 𝒞
  forget-FinPropCoalgebra = forget-Coalgebra ∘F FullSub (F-Coalgebras F)


module FinalRecursive
       (carrier-colimit : Colimit (FinProp.forget-FinPropCoalgebra IsRecursive))
       (coalgebras-filtered : Fil (FinProp.FinPropCoalgebras IsRecursive))
       (F-finitary : preserves-colimit (FinProp.forget-FinPropCoalgebra IsRecursive) F)
       where

  open FinProp IsRecursive
  open import Iterate.Assumptions {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil
  open import Iterate {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil Fil-to-filtered 𝒞-lfp
  private
    module carrier-colimit = Colimit carrier-colimit

  -- colimit-in-Coalgebras : Colimit forget-FinProp
  -- colimit-in-Coalgebras = F-Coalgebras-Colimit forget-FinProp carrier-colimit
  -- private
  --   module colimit-in-Coalgebras = Colimit colimit-in-Coalgebras

  -- if the finite recursive coalgebras have a colimit on the object level,
  -- then this lifts to the category of coalgebras:
  coalgebra-colimit : CoalgColim {o ⊔ ℓ} {ℓ} {ℓ} 𝒞 F FinitaryRecursive
  coalgebra-colimit = record
                       { 𝒟 = FinPropCoalgebras
                       ; D = forget-FinProp
                       ; all-have-prop =
                         λ {i} → record {
                           finite-carrier = 𝒞-lfp.fin-presented (FinPropCoalgebra.carrier i) ;
                           is-recursive = FinPropCoalgebra.has-prop i }
                       ; cocone = F-Coalgebras-Lift-Cocone forget-FinProp carrier-colimit
                       ; carrier-colimitting = F-Coalgebras-Colimit-Carrier-Limitting forget-FinProp carrier-colimit
                       }

  module coalgebra-colimit = CoalgColim.CoalgColim coalgebra-colimit

  iterated-coalgebra : CoalgColim 𝒞 F FinitaryRecursive
  iterated-coalgebra = iterate-CoalgColimit coalgebra-colimit coalgebras-filtered F-finitary

  -- universal-property : ∀ (E : F-Coalgebra F) → FinitaryRecursive E →
  --   (F-Coalgebras F) [ E =∃!=> coalgebra-colimit.to-Coalgebra ]
  -- universal-property E E-fin-rec = {!!}

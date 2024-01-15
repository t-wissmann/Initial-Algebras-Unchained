{-# OPTIONS --without-K #-}
open import Level
open import LFP using (WeaklyLFP)
open import F-Coalgebra-Colimit
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Diagram.Colimit
open import Categories.Diagram.Colimit.DualProperties using (≃-resp-colim)
open import Categories.Object.Initial
open import Categories.Functor.Coalgebra
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

open import Notation
open import Unchained-Utils
open import Filtered

module Classical-Case {o ℓ}
       (𝒞 : Category (o ⊔ ℓ) ℓ ℓ)
       (F : Endofunctor 𝒞)
       {fil-level : Level}
       (Fil : Category (o ⊔ ℓ) ℓ ℓ → Set fil-level) -- some variant of 'filtered'
       (Fil-to-filtered : ∀ {𝒟 : Category (o ⊔ ℓ) ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
       (𝒞-lfp : WeaklyLFP 𝒞 (o ⊔ ℓ) ℓ ℓ Fil Fil-to-filtered)
       -- The law of excluded middle means that for every set A, we know whether it is
       -- empty or non-empty:
       (law-of-excluded-middle : ∀ (A : Set (o ⊔ ℓ)) → Dec A)
       where

open import recursive-coalgebra 𝒞 F
open import Construction {o = o} 𝒞 F Fil Fil-to-filtered 𝒞-lfp

record IsRecursive-via-LEM (R : F-Coalgebra F): Set 0ℓ where
  -- Under the assumption of the law of excluded middle, we can push down
  -- the property of recursiveness down to level 0
  field
    is-recursive-dec : True (law-of-excluded-middle (IsRecursive R))

  is-recursive : IsRecursive R
  is-recursive = toWitness is-recursive-dec

build-IsRecursive-via-LEM : ∀ (R : F-Coalgebra F) → IsRecursive R → IsRecursive-via-LEM R
build-IsRecursive-via-LEM R rec = record { is-recursive-dec = fromWitness rec }


initial-algebra-from-colimit :
       (carrier-colimit : Colimit (FinProp.forget-FinPropCoalgebra IsRecursive-via-LEM))
       (coalgebras-filtered : Fil (FinProp.FinPropCoalgebras IsRecursive))
       (F-finitary : preserves-colimit (FinProp.forget-FinPropCoalgebra IsRecursive) F)
       → Initial (F-Algebras F)
initial-algebra-from-colimit small-colimit coalg-filtered F-finitary =
  FinalRecursive.initial-algebra big-colimit coalg-filtered F-finitary
  where
    big-colimit : Colimit (FinProp.forget-FinPropCoalgebra IsRecursive)
    big-colimit =

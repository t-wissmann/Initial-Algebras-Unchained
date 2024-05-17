{-# OPTIONS --without-K --safe #-}
open import Level
open import Agda.Builtin.Equality renaming (refl to ≡-refl)
open import Accessible-Category using (Accessible)
open import F-Coalgebra-Colimit
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Object.Initial
open import Categories.Diagram.Colimit
open import Categories.Functor.Coalgebra
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

open import Helper-Definitions
open import Colimit-Lemmas
open import Filtered
open import Cofinal

module Classical-Case {o ℓ}
       (𝒞 : Category (o ⊔ ℓ) ℓ ℓ)
       (F : Endofunctor 𝒞)
       {fil-level : Level}
       (Fil : Category (o ⊔ ℓ) ℓ ℓ → Set fil-level) -- some variant of 'filtered'
       (Fil-to-filtered : ∀ {𝒟 : Category (o ⊔ ℓ) ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
       (𝒞-lfp : Accessible 𝒞 (o ⊔ ℓ) ℓ ℓ Fil Fil-to-filtered)
       -- The law of excluded middle means that for every set A, we know whether it is
       -- empty or non-empty:
       (law-of-excluded-middle : ∀ (A : Set (o ⊔ ℓ)) → Dec A)
       where

private
  module 𝒞 = Category 𝒞
  module 𝒞-lfp = Accessible 𝒞-lfp

open import Coalgebra.Recursive 𝒞 F
open import Coalgebra.IdxProp 𝒞 F 𝒞-lfp.fin
open import Coalgebra.IdxProp-fmap 𝒞 F 𝒞-lfp.fin
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

-- the diagram of the coalgebras satisfying IsRecursive-via-LEM is small but has
-- the same colimit as the 'large' diagram from the construction (using IsRecursive),
-- because IsRecursive-via-LEM and IsRecursive are equivalent
build-large-colimit : Colimit (forget-IdxPropCoalgebra IsRecursive-via-LEM)
                    → Colimit (forget-IdxPropCoalgebra IsRecursive)
build-large-colimit = fmap-colimit build-IsRecursive-via-LEM
                                 (λ c → IsRecursive-via-LEM.is-recursive {c})


initial-algebra-from-colimit :
       (carrier-colimit : Colimit (forget-IdxPropCoalgebra IsRecursive-via-LEM))
       (coalgebras-filtered : Fil (IdxPropCoalgebras IsRecursive))
       (F-finitary : preserves-colimit (forget-IdxPropCoalgebra IsRecursive) F)
       → Initial (F-Algebras F)
initial-algebra-from-colimit small-colimit coalg-filtered F-finitary =
  FinalRecursive.initial-algebra (build-large-colimit small-colimit) coalg-filtered F-finitary

{-# OPTIONS --without-K #-}
open import Level
open import Agda.Builtin.Equality renaming (refl to ≡-refl)
open import LFP using (WeaklyLFP)
open import F-Coalgebra-Colimit
open import Categories.Category
open import Categories.Functor
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.Comma
open import Categories.Diagram.Colimit
open import Categories.Diagram.Colimit.DualProperties using (≃-resp-colim)
open import Categories.Diagram.Cocone.Properties
open import Categories.Object.Initial
open import Categories.Functor.Coalgebra
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Notation
open import Unchained-Utils
open import Filtered
open import Cofinal

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

private
  module 𝒞 = Category 𝒞

open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory
open import FullSub-map (F-Coalgebras F)
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

-- the diagram of the coalgebras satisfying IsRecursive-via-LEM is small but has
-- the same colimit as the 'big' diagram from the construction (using IsRecursive)
build-big-colimit : Colimit (FinProp.forget-FinPropCoalgebra IsRecursive-via-LEM)
                  → Colimit (FinProp.forget-FinPropCoalgebra IsRecursive)
build-big-colimit small = expanded
  where
    open FinProp
    module small = Colimit small
    coalgs = F-Coalgebras F
    module coalgs = Category coalgs
    f : FinPropCoalgebra IsRecursive → FinPropCoalgebra IsRecursive-via-LEM
    f = FinProp-fmap build-IsRecursive-via-LEM
    rec-to-lemrec : Functor (FinPropCoalgebras IsRecursive) (FinPropCoalgebras IsRecursive-via-LEM)
    rec-to-lemrec = FullSub (FinPropCoalgebras IsRecursive-via-LEM) {U = f}

    final-rec-to-lemrec : Final rec-to-lemrec
    final-rec-to-lemrec =
      let
        f⁻¹ : FinPropCoalgebra IsRecursive-via-LEM → FinPropCoalgebra IsRecursive
        f⁻¹ d = FinProp-fmap (λ c → IsRecursive-via-LEM.is-recursive {c}) d
        η : (d : FinPropCoalgebra IsRecursive-via-LEM) → Category.Obj (d ↙ rec-to-lemrec)
        η d = record { β = f⁻¹ d ; f = coalgs.id {FinPropCoalgebra.A,α d} }
      in
      record
      { non-empty = η
      ; every-slice-connected = λ (d : FinPropCoalgebra IsRecursive-via-LEM) →
                  record { connect = λ A B → let
                    module d = FinPropCoalgebra d
                    open Category 𝒞
                    open HomReasoning
                    h : ∀ (AB : _) → (d ↙ rec-to-lemrec) [ η d , AB ]
                    h AB = record { g = lift _ ; h = CommaObj.f AB ;
                      commute = begin
                        F-Coalgebra-Morphism.f (CommaObj.f AB) ∘ 𝒞.id ≡⟨⟩
                        F-Coalgebra-Morphism.f (coalgs [ (CommaObj.f AB) ∘ coalgs.id ])
                        ∎
                        }
                  in
                  backward _ _ _ (h A) (forward _ _ _ (h B) (nil _))
                  }
      }
    nested-colimit : Colimit ((forget-Coalgebra ∘F FullSub coalgs) ∘F rec-to-lemrec)
    nested-colimit = final-pulls-colimit
      (forget-Coalgebra ∘F FullSub coalgs)
      rec-to-lemrec final-rec-to-lemrec small

    fun-iso :
      NaturalIsomorphism
        (FullSub coalgs {U = FinPropCoalgebra.A,α {P = IsRecursive}})
        (FullSub coalgs {U = FinPropCoalgebra.A,α}
          ∘F FullSub (FinPropCoalgebras IsRecursive-via-LEM) {U = f})
    fun-iso = FullSubSubCat (FinPropCoalgebra.A,α {P = λ x → IsRecursive-via-LEM x}) f
    nested-colimit' : Colimit (forget-Coalgebra ∘F FullSub coalgs ∘F rec-to-lemrec)
    nested-colimit' = ≃-resp-colim
                      (associator rec-to-lemrec (FullSub coalgs) forget-Coalgebra)
                      nested-colimit
    expanded : Colimit (forget-Coalgebra ∘F
                           FullSub coalgs {U = FinPropCoalgebra.A,α {P = IsRecursive}})
    expanded = ≃-resp-colim (sym (forget-Coalgebra ⓘˡ fun-iso)) nested-colimit'


initial-algebra-from-colimit :
       (carrier-colimit : Colimit (FinProp.forget-FinPropCoalgebra IsRecursive-via-LEM))
       (coalgebras-filtered : Fil (FinProp.FinPropCoalgebras IsRecursive))
       (F-finitary : preserves-colimit (FinProp.forget-FinPropCoalgebra IsRecursive) F)
       → Initial (F-Algebras F)
initial-algebra-from-colimit small-colimit coalg-filtered F-finitary =
  FinalRecursive.initial-algebra (build-big-colimit small-colimit) coalg-filtered F-finitary

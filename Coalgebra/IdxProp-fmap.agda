{-# OPTIONS --without-K #-}

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory
open import Categories.Diagram.Colimit
open import Categories.Category.Construction.Comma
open import Categories.Diagram.Colimit
open import Data.Product
open import Relation.Unary using () renaming (_⊆′_ to _⊆_)
open import Categories.Diagram.Colimit.DualProperties using (≃-resp-colim)
open import Categories.Diagram.Cocone.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism

open import F-Coalgebra-Colimit
open import Cofinal

module Coalgebra.IdxProp-fmap
                         {o ℓ e : Level} (𝒞 : Category o ℓ e) (F : Endofunctor 𝒞)
                         {i : Level} {Idx : Set i} (family : Idx → Category.Obj 𝒞)
                         where

private
  module 𝒞 = Category 𝒞

open import Coalgebra.IdxProp 𝒞 F family
open import FullSub-map (F-Coalgebras F)

IdxProp-fmap : {p p' : Level} {P : F-Coalgebra F → Set p} {P' : F-Coalgebra F → Set p'}
              → (∀ (c : _) → P c → P' c)
              → IdxPropCoalgebra P → IdxPropCoalgebra P'
IdxProp-fmap {P = P} f coalg =
  let open IdxPropCoalgebra P coalg in
  record { carrier = carrier ; structure = structure ; has-prop = f A,α has-prop }

module _ {p q : Level} {P : F-Coalgebra F → Set p} {Q : F-Coalgebra F → Set q} where
  -- For two equivalent properties P and Q, their colimits are the same:
  fmap-colimit : P ⊆ Q → Q ⊆ P
               → Colimit (forget-IdxPropCoalgebra Q)
               → Colimit (forget-IdxPropCoalgebra P)
  fmap-colimit P⇒Q Q⇒P small = expanded
    where
      module small = Colimit small
      coalgs = F-Coalgebras F
      module coalgs = Category coalgs
      f : IdxPropCoalgebra P → IdxPropCoalgebra Q
      f = IdxProp-fmap P⇒Q
      rec-to-lemrec : Functor (IdxPropCoalgebras P) (IdxPropCoalgebras Q)
      rec-to-lemrec = FullSub (IdxPropCoalgebras Q) {U = f}

      f⁻¹ : IdxPropCoalgebra Q → IdxPropCoalgebra P
      f⁻¹ d = IdxProp-fmap Q⇒P d
      η : (d : IdxPropCoalgebra Q) → Category.Obj (d ↙ rec-to-lemrec)
      η d = record { β = f⁻¹ d ; f = coalgs.id {IdxPropCoalgebra.A,α Q d} }

      final-rec-to-lemrec : Final rec-to-lemrec
      final-rec-to-lemrec =
        record
        { non-empty = η
        ; every-slice-connected = λ (d : IdxPropCoalgebra Q) →
            record { connect = λ A B → let
              module d = IdxPropCoalgebra Q d
              open Category 𝒞
              open HomReasoning
              h : ∀ (AB : _) → (d ↙ rec-to-lemrec) [ η d , AB ]
              h AB = record
                { g = lift _
                ; h = CommaObj.f AB
                ; commute = begin
                   F-Coalgebra-Morphism.f (CommaObj.f AB) ∘ 𝒞.id ≡⟨⟩
                   F-Coalgebra-Morphism.f (coalgs [ (CommaObj.f AB) ∘ coalgs.id ])
                   ∎
                }
            in
            backward _ _ _ (h A) (forward _ _ _ (h B) (nil _))
            }
        }

      nested-colimit : Colimit ((forget-Coalgebra ∘F FullSub coalgs) ∘F rec-to-lemrec)
      nested-colimit =
        final-pulls-colimit (forget-Coalgebra ∘F FullSub coalgs)
          rec-to-lemrec final-rec-to-lemrec small

      fun-iso : NaturalIsomorphism
            (FullSub coalgs {U = IdxPropCoalgebra.A,α P})
            (FullSub coalgs {U = IdxPropCoalgebra.A,α Q}
              ∘F FullSub (IdxPropCoalgebras Q) {U = f})
      fun-iso = FullSubSubCat (IdxPropCoalgebra.A,α Q) f

      nested-colimit' : Colimit (forget-Coalgebra ∘F FullSub coalgs ∘F rec-to-lemrec)
      nested-colimit' = ≃-resp-colim
                     (associator rec-to-lemrec (FullSub coalgs) forget-Coalgebra)
                     nested-colimit

      expanded : Colimit (forget-Coalgebra ∘F
                         FullSub coalgs {U = IdxPropCoalgebra.A,α P})
      expanded = ≃-resp-colim (sym (forget-Coalgebra ⓘˡ fun-iso)) nested-colimit'

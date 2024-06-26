{-# OPTIONS --without-K --safe #-}
module Setoids-Choice where

open import Level
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to refl-by-def)

open import Agda.Builtin.Sigma
open import Data.Product
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cocomplete
open import Categories.Diagram.Cocone
open import Categories.Diagram.Colimit
open import Categories.Object.Initial
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Categories.Category.Construction.Cocones using (Cocones)
open import Categories.Category.Instance.Properties.Setoids.Cocomplete
open import Filtered

open import Colimit-Lemmas using (IsLimitting)
import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e c ℓ'} {D : Category o ℓ e} {J : Functor D (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ'))} where
  private
    construction = Setoids-Cocomplete o ℓ e c ℓ' J
    open Setoid renaming (_≈_ to _[[_≈_]])
    module construction = Colimit construction
    module D = Category D
    module J = Functor J

  J₀ : D.Obj → Set _
  J₀ i = Setoid.Carrier (J.F₀ i)

  module _ (Colim : Colimit J) where
    -- Given an element in the carrier set of a colimit,
    -- choose an object in the diagram scheme and an element in the corresponding
    -- set in the diagram:
    module Colim = Colimit Colim
    colimit-choice : Setoid.Carrier Colim.coapex → Σ[ i ∈ D.Obj ] (Setoid.Carrier (J.F₀ i))
    colimit-choice x =
        let
            -- apply the universal property to get an element in the standard
            -- setoid colimit construction!
            cocone-morph = Colim.rep-cocone construction.colimit
            module cocone-morph = Cocone⇒ cocone-morph
        in
        cocone-morph.arr ⟨$⟩ x

    -- The other direction is simply the colimit injection: we just use it
    -- as a shorthand in the correctness statement.
    colimit-inject : Σ[ i ∈ D.Obj ] (Setoid.Carrier (J.F₀ i)) → Setoid.Carrier Colim.coapex
    colimit-inject (i , elem) = Colim.proj i ⟨$⟩ elem

    -- The correctness of `colimit-choice`: given `x` in the colimit,
    -- if we choose some element somewhere in the diagram, then injecting
    -- it into the colimit yields `x` again:

    colimit-choice-correct : ∀ {x : Setoid.Carrier Colim.coapex} →
                            Colim.coapex [[
                              x ≈
                                Colim.proj (fst (colimit-choice x))
                                  ⟨$⟩ (snd (colimit-choice x)) ]]
    colimit-choice-correct {top-level-x} =
      same-cocone-morph (refl Colim.coapex)
        where
        -- we show the equality by the uniqueness of cocone morphisms, so we
        -- construct a couple of cocone morphisms for the above equation.
        -- 1. the identity cocone morphism:
        id-cmorph : Cocone⇒ _ Colim.colimit Colim.colimit
        id-cmorph = Category.id (Cocones _)

        -- 2a. for another endomorphism on Colim, we first take the choice:
        choice-cmorph : Cocone⇒ _ Colim.colimit construction.colimit
        choice-cmorph = Colim.rep-cocone construction.colimit

        -- 2b. and then inject back
        inject-cmorph : Cocone⇒ _ construction.colimit Colim.colimit
        inject-cmorph = construction.rep-cocone Colim.colimit
        module inject-cmorph = Cocone⇒ inject-cmorph

        inject-cmorph-correct : ∀ x → inject-cmorph.arr ⟨$⟩ x ≡ colimit-inject x
        inject-cmorph-correct x = refl-by-def

        same-cocone-morph : Cocones J [ id-cmorph ≈ (Cocones J [ inject-cmorph ∘ choice-cmorph ]) ]
        same-cocone-morph =
            Colim.initial.!-unique₂
              id-cmorph
              (Cocones J [ inject-cmorph ∘ choice-cmorph ])

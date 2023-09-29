{-# OPTIONS --without-K #-}
module Setoids-Choice where

open import Level
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to refl-by-def)

open import Agda.Builtin.Sigma
open import Data.Product
open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality

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

open import Unchained-Utils using (IsLimitting)
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

  record identified-in-diagram {X Y : D.Obj} (x : J₀ X) (y : J₀ Y) : Set (o ⊔ ℓ ⊔ c ⊔ ℓ') where
      field
        -- that two elements x and y are identified in the diagram means that
        -- 1. there is an object B in the diagram
        B : D.Obj
        -- 2. which is above X and Y
        inj₁ : D [ X , B ]
        inj₂ : D [ Y , B ]
        -- 3. such that both x and y are sent to the same element in B
        identifies : J.F₀ B [[ J.F₁ inj₁ ⟨$⟩ x ≈ J.F₁ inj₂ ⟨$⟩ y ]]

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
        let
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

        inject-cmorph-correct : ∀ x → Π._⟨$⟩_ inject-cmorph.arr x ≡ colimit-inject x
        inject-cmorph-correct x = refl-by-def

        same-cocone-morph : Cocones J [ id-cmorph ≈ (Cocones J [ inject-cmorph ∘ choice-cmorph ]) ]
        same-cocone-morph =
            -- TODO: why is this so long?
            IsInitial.!-unique₂
            (Initial.⊥-is-initial Colim.initial)
            id-cmorph
            (Cocones J [ inject-cmorph ∘ choice-cmorph ])
        in
        same-cocone-morph (refl Colim.coapex)


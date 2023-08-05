module Setoid-Choice where

open import Level
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
open import Agda.Builtin.Equality using (_≡_)

open import Agda.Builtin.Sigma
open import Data.Product
open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cocomplete
open import Categories.Diagram.Cocone
open import Categories.Diagram.Colimit
open import Categories.Category.Construction.Cocones using (Cocones)
open import Categories.Category.Instance.Properties.Setoids.Cocomplete

import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e} c ℓ' {D : Category o ℓ e} (J : Functor D (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ'))) where
  construction = Setoids-Cocomplete o ℓ e c ℓ' J
  module construction = Colimit construction
  module D = Category D
  module J = Functor J

  construction-choice : Setoid.Carrier construction.coapex → Σ[ i ∈ D.Obj ] (Setoid.Carrier (J.F₀ i))
  construction-choice (i , elem) = i , elem

  module _ (Colim : Colimit J) where
    -- given an element in the carrier set of a colimit,
    -- choose an object in the diagram and an element there
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

    colimit-inject : Σ[ i ∈ D.Obj ] (Setoid.Carrier (J.F₀ i)) → Setoid.Carrier Colim.coapex
    colimit-inject (i , elem) = Colim.proj i ⟨$⟩ elem

    module _ where
        open Setoid renaming (_≈_ to _⊢_≈_)
        colimit-choice-correct : ∀ {x : Setoid.Carrier Colim.coapex} →
                                Colim.coapex ⊢ x ≈ colimit-inject (colimit-choice x)
        colimit-choice-correct {x} =
          let
            (i , elem) = colimit-choice x

            -- the identity cocone morphism:
            id-cmorph : Cocone⇒ _ Colim.colimit Colim.colimit
            id-cmorph = Category.id (Cocones _)

            -- for another endomorphism on Colim, we first take the choice:
            choice-cmorph : Cocone⇒ _ Colim.colimit construction.colimit
            choice-cmorph = Colim.rep-cocone construction.colimit

            -- and then inject back
            inject-cmorph : Cocone⇒ _ construction.colimit Colim.colimit
            inject-cmorph = construction.rep-cocone Colim.colimit
            module inject-cmorph = Cocone⇒ inject-cmorph

            inject-cmorph-correct : ∀ x → Π._⟨$⟩_ inject-cmorph.arr x ≡ colimit-inject x
            inject-cmorph-correct x = {!!}
          in
          {!!}

module Setoid-Choice where

open import Level
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Category.Instance.Properties.Setoids.Cocomplete

import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e} c ℓ' {D : Category o ℓ e} (J : Functor D (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ'))) where
  construction = Setoids-Cocomplete o ℓ e c ℓ' J
  module construction = Colimit construction
  module D = Category D
  -- foo = {!!}
  construction-choice : Setoid.Carrier construction.coapex → D.Obj
  construction-choice x = {!!}

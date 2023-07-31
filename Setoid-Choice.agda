module Setoid-Choice where

open import Level
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Cocomplete

import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e} c ℓ′ {J : Category o ℓ e} (F : Functor J (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′))) where


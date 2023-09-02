module Setoid-Choice where

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

import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e} c ℓ' {D : Category o ℓ e} (J : Functor D (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ'))) where
  construction = Setoids-Cocomplete o ℓ e c ℓ' J
  open Setoid renaming (_≈_ to _[[_≈_]])
  module construction = Colimit construction
  module D = Category D
  module J = Functor J

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
                            Colim.coapex [[ x ≈ colimit-inject (colimit-choice x)]]
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



    -- Lemma: if two elements are idenitfied in the colimit of a filtered diagram,
    -- then they are already identified somewhere in the diagram
    J₀ : D.Obj → Set _
    J₀ i = Setoid.Carrier (J.F₀ i)

    record identified-in-diagram {X Y : D.Obj} (x : J₀ X) (y : J₀ Y) : Set (o ⊔ ℓ ⊔ c ⊔ ℓ') where
      field
        B : D.Obj
        inj₁ : D [ X , B ]
        inj₂ : D [ Y , B ]
        identifies : J.F₀ B [[ J.F₁ inj₁ ⟨$⟩ x ≈ J.F₁ inj₂ ⟨$⟩ y ]]

    -- We first show the lemma for the canonically constructed colimit.
    -- For the constructed colimit, we know that ≈ means that x and y
    -- are connected by a zigzag. So we can recurse over the zigzag structure.
    filter-identification-constr : (filtered D) → ∀ {X Y : D.Obj} → (x : J₀ X) (y : J₀ Y)
       → construction.coapex [[ construction.proj X ⟨$⟩ x ≈ construction.proj Y ⟨$⟩ y ]]
       → identified-in-diagram x y
    filter-identification-constr fil {X} {Y} x y (Plus⇔.forth (f , fx≈y)) =
      record { B = Y ; inj₁ = f ; inj₂ = D.id ; identifies =
        let open SetoidR (J.F₀ Y) in
        begin
        (J.F₁ f ⟨$⟩ x)  ≈⟨ fx≈y ⟩
        y              ≈˘⟨ J.identity (refl (J.F₀ Y)) ⟩
        (J.F₁ D.id ⟨$⟩ y)
        ∎
        }
    filter-identification-constr fil {X} {Y} x y (Plus⇔.back (f , fy≈x)) =
      record { B = X ; inj₁ = D.id ; inj₂ = f ; identifies =
        let open SetoidR (J.F₀ X) in
        begin
        (J.F₁ D.id ⟨$⟩ x)  ≈⟨ J.identity (refl (J.F₀ X)) ⟩
        x                 ≈˘⟨ fy≈x ⟩
        (J.F₁ f ⟨$⟩ y)
        ∎
        }
    filter-identification-constr fil {X} {Z} x z (Plus⇔.forth⁺ {_} {Y , y} {_} (f , fx≈y) y≈z) =
      let
        -- easy recursive case:
        -- f sends x to y and we have a bound of y and z:
        y∨z = filter-identification-constr fil y z y≈z
        module y∨z = identified-in-diagram y∨z
      in
      record {
        B = y∨z.B ;
        inj₁ = D [ y∨z.inj₁ ∘ f ] ;
        inj₂ = y∨z.inj₂ ;
        identifies =
        let
            open SetoidR (J.F₀ y∨z.B)
        in
        begin
        J.F₁ (D [ y∨z.inj₁ ∘ f ]) ⟨$⟩ x ≈⟨ J.homomorphism (refl (J.F₀ X)) ⟩
        J.F₁ y∨z.inj₁ ⟨$⟩ (J.F₁ f ⟨$⟩ x) ≈⟨ cong (J.F₁ y∨z.inj₁) fx≈y ⟩
        J.F₁ y∨z.inj₁ ⟨$⟩ y             ≈⟨ y∨z.identifies ⟩
        J.F₁ y∨z.inj₂ ⟨$⟩ z
        ∎
      }
    filter-identification-constr fil {X} {Z} x z (Plus⇔.back⁺ {_} {Y , y} {_} (f , fy≈x) y≈z) =
      let
        -- non-trivial recursive case, because we now use filteredness:
        -- f sends y to x and we have a bound V of y and z:
        -- X <- Y -> V <- Z
        V = filter-identification-constr fil y z y≈z
        module V = identified-in-diagram V

        open filtered fil

        -- the new upper bound and the two injections
        W = close-span-obj f V.inj₁
        w₁ = close-span-morph₁ f V.inj₁
        w₂ = close-span-morph₂ f V.inj₁
      in
      record {
        B = W;
        inj₁ = w₁;
        inj₂ = D [ w₂ ∘ V.inj₂ ] ;
        identifies =
        let
            open SetoidR (J.F₀ (close-span-obj f V.inj₁))
        in
        begin
        J.F₁ w₁ ⟨$⟩ x               ≈˘⟨ cong (J.F₁ w₁) fy≈x ⟩
        J.F₁ w₁ ⟨$⟩ (J.F₁ f ⟨$⟩ y)   ≈⟨ {!!} ⟩
        J.F₁ w₂ ⟨$⟩ ((J.F₁ V.inj₂) ⟨$⟩ z) ≈˘⟨ J.homomorphism (refl (J.F₀ Z)) ⟩
        J.F₁ (D [ w₂ ∘ V.inj₂ ]) ⟨$⟩ z
        ∎
      }

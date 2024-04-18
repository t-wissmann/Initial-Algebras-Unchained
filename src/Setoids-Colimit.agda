{-# OPTIONS --without-K --safe #-}
module Setoids-Colimit where

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

open import Colimit-Lemmas using (IsLimitting)
import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e c ℓ'} {D : Category o ℓ e} (J : Functor D (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ'))) where
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
    private
      module Colim = Colimit Colim

    -- Lemma: if two elements are idenitfied in the colimit of a filtered diagram,
    -- then they are already identified somewhere in the diagram.

    -- We first show the lemma for the canonically constructed colimit.
    -- For the constructed colimit, we know that ≈ means that x and y
    -- are connected by a zigzag. So we can recurse over the zigzag structure.
    filtered-identification-constr : (filtered D) → ∀ {X Y : D.Obj} → (x : J₀ X) (y : J₀ Y)
       → construction.coapex [[ construction.proj X ⟨$⟩ x ≈ construction.proj Y ⟨$⟩ y ]]
       → identified-in-diagram x y
    filtered-identification-constr fil {X} {Y} x y (Plus⇔.forth (f , fx≈y)) =
      record { B = Y ; inj₁ = f ; inj₂ = D.id ; identifies =
        let open SetoidR (J.F₀ Y) in
        begin
        (J.F₁ f ⟨$⟩ x)  ≈⟨ fx≈y ⟩
        y              ≈˘⟨ J.identity (refl (J.F₀ Y)) ⟩
        (J.F₁ D.id ⟨$⟩ y)
        ∎
        }
    filtered-identification-constr fil {X} {Y} x y (Plus⇔.back (f , fy≈x)) =
      record { B = X ; inj₁ = D.id ; inj₂ = f ; identifies =
        let open SetoidR (J.F₀ X) in
        begin
        (J.F₁ D.id ⟨$⟩ x)  ≈⟨ J.identity (refl (J.F₀ X)) ⟩
        x                 ≈˘⟨ fy≈x ⟩
        (J.F₁ f ⟨$⟩ y)
        ∎
        }
    filtered-identification-constr fil {X} {Z} x z (Plus⇔.forth⁺ {_} {Y , y} {_} (f , fx≈y) y≈z) =
      let
        -- easy recursive case:
        -- f sends x to y and we have a bound of y and z:
        y∨z = filtered-identification-constr fil y z y≈z
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
    filtered-identification-constr fil {X} {Z} x z (Plus⇔.back⁺ {_} {Y , y} {_} (f , fy≈x) y≈z) =
      let
        -- non-trivial recursive case, because we now use filteredness:
        -- f sends y to x and we have a bound V of y and z:
        -- X <- Y -> V <- Z
        V = filtered-identification-constr fil y z y≈z
        module V = identified-in-diagram V

        open filtered fil

        -- the new upper bound and the two injections
        W : ClosedSpan _ f V.inj₁
        W = close-span f V.inj₁
        module W = ClosedSpan W
        w₁ = W.close-fst
        w₂ = W.close-snd
      in
      record {
        B = W.tip;
        inj₁ = w₁;
        inj₂ = D [ w₂ ∘ V.inj₂ ] ;
        identifies =
        let
            open SetoidR (J.F₀ W.tip)
        in
        begin
        J.F₁ w₁ ⟨$⟩ x               ≈˘⟨ cong (J.F₁ w₁) fy≈x ⟩
        J.F₁ w₁ ⟨$⟩ (J.F₁ f ⟨$⟩ y)   ≈˘⟨ J.homomorphism (refl (J.F₀ Y)) ⟩
        J.F₁ (D [ w₁ ∘ f ]) ⟨$⟩ y   ≈⟨ J.F-resp-≈ W.commutes (refl (J.F₀ Y)) ⟩
        J.F₁ (D [ w₂ ∘ V.inj₁ ]) ⟨$⟩ y   ≈⟨ J.homomorphism (refl (J.F₀ Y)) ⟩
        J.F₁ w₂ ⟨$⟩ ((J.F₁ V.inj₁) ⟨$⟩ y) ≈⟨ cong (J.F₁ w₂) V.identifies ⟩
        J.F₁ w₂ ⟨$⟩ ((J.F₁ V.inj₂) ⟨$⟩ z) ≈˘⟨ J.homomorphism (refl (J.F₀ Z)) ⟩
        J.F₁ (D [ w₂ ∘ V.inj₂ ]) ⟨$⟩ z
        ∎
      }

    filtered-identification-colim : (filtered D) → ∀ {X Y : D.Obj} → {x : J₀ X} {y : J₀ Y}
       → Colim.coapex [[ Colim.proj X ⟨$⟩ x ≈ Colim.proj Y ⟨$⟩ y ]]
       → identified-in-diagram x y
    filtered-identification-colim fil {X} {Y} {x} {y} x≈y =
      filtered-identification-constr fil x y constr⊢x≈y
      where
        -- the unique cocone morphism:
        u = Colim.rep-cocone construction.colimit
        module u = Cocone⇒ u

        open SetoidR (construction.coapex)
        constr⊢x≈y =
          begin
          construction.proj X ⟨$⟩ x ≈˘⟨ u.commute (refl (J.F₀ X)) ⟩
          u.arr ⟨$⟩ (Colim.proj X ⟨$⟩ x) ≈⟨ cong u.arr x≈y ⟩
          u.arr ⟨$⟩ (Colim.proj Y ⟨$⟩ y) ≈⟨ u.commute (refl (J.F₀ Y)) ⟩
          construction.proj Y ⟨$⟩ y
          ∎


  -- the next results characterize: when is a Cocone a Colimit in Setoids?
  open import Function.Equality using (_⟶_)
  -- (f: A ⟶ B)
  record KernelPairs {o'' e'' : Level} {A B : Setoid o'' e''} (f : A ⟶ B) : Set (o'' ⊔ e'') where
    field
        pr₁ : Setoid.Carrier A
        pr₂ : Setoid.Carrier A
        identified : B [[ f ⟨$⟩ pr₁ ≈ f ⟨$⟩ pr₂ ]]

  module _ (C : Cocone J) where
    private
      module C = Cocone C

    record comes-from-diagram (x : Setoid.Carrier C.N) : Set (o ⊔ ℓ ⊔ c ⊔ ℓ') where
      field
        i : D.Obj
        preimage : Setoid.Carrier (J.F₀ i)
        x-sent-to-c : C.N [[ ((C.ψ i) ⟨$⟩ preimage) ≈ x ]]


    -- Lemma: For a diagram with upper bounds, a cocone is colimitting if the
    -- following conditions are met:
    -- 1. every element in the Cocone Setoid is in the image
    --    of some colimit injection
    -- 2. whenever two elements in a set in the diagram are
    --    identified in the cocone, then they are already
    --    identified within the diagram.
    bounded-colimiting : (has-upper-bounds D) →
      (∀ (x : Setoid.Carrier C.N) → comes-from-diagram x) →
      (∀ {i : D.Obj} (k : KernelPairs (C.ψ i)) →
        identified-in-diagram (KernelPairs.pr₁ k) (KernelPairs.pr₂ k)) →
      -- ^- wow, agda managed to infer that (pr₁ k) is of shape J₀ X for some X
      IsLimitting C
    bounded-colimiting bounds get-preimage get-identifier =
      let
        refl-auto : ∀ {i : D.Obj} {elem : J₀ i} → J.F₀ i [[ elem ≈ elem ]]
        refl-auto {i} = refl (J.F₀ i)

        -- the lemma says that whenever two elements x y from
        -- somewhere in the diagram are identified in the cocone C,
        -- then they must be identified in any other cocone, too.
        -- (We have E as the first parameter to make the application
        -- of this lemma easier)
        lemma : ∀ (E : Cocone J) →
                ∀ {X Y : D.Obj} (x : J₀ X) (y : J₀ Y) →
                  C.N [[ C.ψ X ⟨$⟩ x ≈ C.ψ Y ⟨$⟩ y ]] →
                  (Cocone.N E) [[ Cocone.ψ E X ⟨$⟩ x ≈ Cocone.ψ E Y ⟨$⟩ y ]]
        lemma E {X} {Y} x y eq-in-C =
          let
            module E = Cocone E
            module B = has-upper-bounds bounds

            V = B.upper-bound X Y
            inj-X = B.is-above₁ X Y
            inj-Y = B.is-above₂ X Y

            x-in-V = (J.F₁ inj-X ⟨$⟩ x)
            y-in-V = (J.F₁ inj-Y ⟨$⟩ y)

            -- but having them in the same object does not yet
            -- imply that they are identified already.
            -- They are identified in the diagram by the second assumption:
            ident : identified-in-diagram x-in-V y-in-V
            ident = get-identifier (record {
              pr₁ = x-in-V ; pr₂ = y-in-V ; identified =
              let open SetoidR (C.N) in
              begin
              C.ψ V ⟨$⟩ (J.F₁ inj-X ⟨$⟩ x) ≈⟨ C.commute inj-X (refl-auto) ⟩
              C.ψ X ⟨$⟩ x                 ≈⟨ eq-in-C ⟩
              C.ψ Y ⟨$⟩ y                 ≈˘⟨ C.commute inj-Y (refl-auto) ⟩
              C.ψ V ⟨$⟩ (J.F₁ inj-Y ⟨$⟩ y)
              ∎
              })
            module ident = identified-in-diagram ident

            -- now we can show that they must be identified in E, too:
            open SetoidR (E.N)
          in
          begin
          E.ψ X ⟨$⟩ x                   ≈˘⟨ E.commute inj-X refl-auto ⟩
          E.ψ V ⟨$⟩ (J.F₁ inj-X ⟨$⟩ x)   ≡⟨⟩
          E.ψ V ⟨$⟩ x-in-V              ≈˘⟨ E.commute ident.inj₁ refl-auto ⟩
          E.ψ ident.B ⟨$⟩ (J.F₁ ident.inj₁ ⟨$⟩ x-in-V)
              ≈⟨ cong (E.ψ ident.B) ident.identifies ⟩
          E.ψ ident.B ⟨$⟩ (J.F₁ ident.inj₂ ⟨$⟩ y-in-V)
                                        ≈⟨ E.commute ident.inj₂ refl-auto ⟩
          E.ψ V ⟨$⟩ y-in-V              ≡⟨⟩
          E.ψ V ⟨$⟩ (J.F₁ inj-Y ⟨$⟩ y)   ≈⟨ E.commute inj-Y refl-auto ⟩
          E.ψ Y ⟨$⟩ y
          ∎

        ump : ∀ (E : Cocone J) → Cocone⇒ _ C E
        ump E =
          let
            module E = Cocone E
            f : Setoid.Carrier C.N → Setoid.Carrier E.N
            f x =
              let
                preim = get-preimage x
                module preim = comes-from-diagram preim
              in
              E.ψ preim.i ⟨$⟩ preim.preimage

            f-well-def : C.N ⟶ E.N
            f-well-def = record
              { _⟨$⟩_ = f ; cong =
              λ {x} {y} x≈y →
                let
                  X = get-preimage x
                  module X = comes-from-diagram X
                  Y = get-preimage y
                  module Y = comes-from-diagram Y
                  open SetoidR (C.N)
                in
                lemma E X.preimage Y.preimage (
                begin
                C.ψ X.i ⟨$⟩ X.preimage ≈⟨ X.x-sent-to-c ⟩
                x                     ≈⟨ x≈y ⟩
                y                     ≈˘⟨ Y.x-sent-to-c ⟩
                C.ψ Y.i ⟨$⟩ Y.preimage
                ∎
                )
              }
          in
          record {
            arr = f-well-def ;
            commute = λ {X} {x} {x'} x≈x' →
              let
                P = get-preimage (C.ψ X ⟨$⟩ x)
                module P = comes-from-diagram P
                open SetoidR (E.N)
              in
              begin
              f (C.ψ X ⟨$⟩ x)         ≡⟨⟩
              E.ψ P.i ⟨$⟩ P.preimage  ≈⟨ lemma E P.preimage x P.x-sent-to-c ⟩
              E.ψ X ⟨$⟩ x             ≈⟨ cong (E.ψ X) x≈x' ⟩
              E.ψ X ⟨$⟩ x'
              ∎
            }
      in
      record {
        ! = ump _ ;
        !-unique = λ {E} w {x} {y} x≈y →
          let
            module E = Cocone E
            module w = Cocone⇒ w
            f = Cocone⇒.arr (ump E)
            module y = comes-from-diagram (get-preimage y)
            module x = comes-from-diagram (get-preimage x)

            preimages-identified =
              -- show that x.preimage and y.preimage
              -- are sent to the same in C.N
              let open SetoidR (C.N) in
              begin
              C.ψ x.i ⟨$⟩ x.preimage ≈⟨ x.x-sent-to-c ⟩
              x                     ≈⟨ x≈y ⟩
              y                     ≈˘⟨ y.x-sent-to-c ⟩
              C.ψ y.i ⟨$⟩ y.preimage
              ∎

            open SetoidR (E.N)
          in
          begin
          f ⟨$⟩ x         ≈⟨ lemma E x.preimage y.preimage preimages-identified ⟩
          E.ψ y.i ⟨$⟩ y.preimage                  ≈˘⟨ w.commute refl-auto ⟩
          w.arr ⟨$⟩ (C.ψ y.i ⟨$⟩ y.preimage)       ≈⟨ cong w.arr y.x-sent-to-c ⟩
          w.arr ⟨$⟩ y
          ∎
      }

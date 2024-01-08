{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Category.Lift
open import Categories.Functor using (Functor)
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory
open import Categories.Object.Initial
open import Categories.Category.Construction.Thin
open import Categories.Category.Cocomplete
open import Categories.Category.Slice
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Construction.LiftSetoids
open import Data.Product

open import Unchained-Utils
open import Filtered

open import Categories.Functor using (_∘F_)

open import Relation.Binary using (Poset)

-- For the future generalization from LFP to Locally Presentable:
-- type-theoretic generalization of presentable categories.
-- In usual L(F)P-Categories, one considers a (regular) cardinal λ and
-- then defines λ-presentable objects as those whose hom-set preserves
-- colimits of λ-directed diagrams. The notion 'λ-directed' means that
-- the diagram has upper bounds for any set of elements of size smaller than λ.
-- Since this is inherently ordinal based, we change the definition for the
-- formalization in agda: instead of a (proper) upper bounds λ, we fix a type
-- κ and require that every κ-indexed family of elements has an upper bound.
-- This has the disadvantage that (Fin 2)-directed and (Fin 3)-directed are the
-- same concepts, because they both boil down to having bounds for any finite
-- set of elements. The advantage is that we do not need any ordinals at all.
--
module LFP {o ℓ prop-level} (𝒞 : Category o ℓ ℓ)
                 (P : Category ℓ ℓ ℓ → Set prop-level)
                 (P⇒filtered : ∀ {𝒟} → P 𝒟 → filtered 𝒟)
                 where

private
  module 𝒞 = Category 𝒞

open import LFP-slices (𝒞)
open import Categories.Functor.Slice (𝒞) using (Forgetful)
open import Categories.Functor.Hom
open import Categories.Object.Coproduct (𝒞)
open import Categories.Morphism (𝒞)
open import Categories.Morphism.Reasoning.Core 𝒞
open import Categories.Diagram.Coequalizer (𝒞)
open import Categories.Diagram.Pushout (𝒞)
open import Categories.Diagram.Pushout.Properties (𝒞)
open import Presented 𝒞 ℓ ℓ ℓ P
import Setoids-Colimit

open Hom

private
  variable
    -- levels for the diagram scheme:
    o' ℓ' e' : Level
    -- diagram scheme:
    𝒟 : Category o' ℓ' e'


open import Hom-Colimit-Choice 𝒞
open LiftHom ℓ ℓ ℓ


record WeaklyLFP : Set (o ⊔ suc (ℓ ⊔ prop-level)) where
  field
    -- a (small)family (resp. 'set') of objects ...
    Idx : Set ℓ
    fin : Idx → 𝒞.Obj
    -- ... of which every element is fp:
    fin-presented : ∀ (i : Idx) → presented (fin i)
    -- All other objects are built from those fp objects:
    build-from-fin : ∀ (X : 𝒞.Obj) → IsLimitting (Cocone[ fin ↓ X ])
    -- and moreover every canonical diagram is filtered
    canonical-has-prop : ∀ (X : 𝒞.Obj) → P (Cat[ fin ↓ X ])

    -- also, we need finite colimits of presented objects:
    coproduct : ∀ (A B : 𝒞.Obj) → presented A → presented B → Coproduct A B
    -- coequalizer : ∀ {A B} (f g : 𝒞 [ A , B ]) → presented A → presented B → Coequalizer f g

  -- pushout : ∀ {A B C} (f : 𝒞 [ A , B ]) (g : 𝒞 [ A , C ]) →
  --             presented A → presented B → presented C →
  --             Pushout f g
  -- pushout f g A-pres B-pres C-pres =
  --   let
  --     B+C = (coproduct _ _ B-pres C-pres)
  --   in
  --   Coproduct×Coequalizer⇒Pushout
  --     B+C (coequalizer _ _ A-pres (presented-coproduct B+C P⇒filtered B-pres C-pres))

  canonical-diagram-scheme : ∀ (X : 𝒞.Obj) → Category ℓ ℓ ℓ
  canonical-diagram-scheme X = Cat[ fin ↓ X ]

  canonical-diagram : ∀ (X : 𝒞.Obj) → Functor (canonical-diagram-scheme X) 𝒞
  canonical-diagram X = Functor[ fin ↓ X ]

  canonical-colimit : ∀ (X : 𝒞.Obj) → Colimit (canonical-diagram X)
  canonical-colimit X = Colimit-from-prop (build-from-fin X)

  -- the family 'fin' forms a generator. This means that for every X,
  -- the morphisms 'fin k ⇒ X' are jointly epic
  fin-generator : ∀ (X : 𝒞.Obj) →
    jointly-epic
      {𝒞 = 𝒞}
      {codom = X}
      (Cocone.ψ Cocone[ fin ↓ X ])
  fin-generator X = colimit-is-jointly-epic (Colimit-from-prop (build-from-fin X))

  presentable-split-in-fin : ∀ (X : 𝒞.Obj) → presented X → Σ[ i ∈ Idx ] (Retract X (fin i))
  presentable-split-in-fin X X-pres = (proj₁ (Triangle.x t)) ,
    (record {
      section = Triangle.p' t ;
      retract = (proj₂ (Triangle.x t)) ;
      is-retract = 𝒞.Equiv.sym (Triangle.commutes t) })
    where
      -- we let the identity on X factor through the canonical
      -- diagram for X:
      t : Triangle (canonical-colimit X) (𝒞.id{X})
      t = hom-colim-choice
            (canonical-colimit X)
            X
            (X-pres
              (canonical-diagram-scheme X)
              (canonical-has-prop X)
              (canonical-diagram X)) (𝒞.id{X})

  -- the family of presented objects
  presented-obj : Σ 𝒞.Obj presented → 𝒞.Obj
  presented-obj = proj₁

  presented-colimit : ∀ (X : 𝒞.Obj) → IsLimitting (Cocone[ presented-obj ↓ X ])
  presented-colimit X = record {
      ! = λ {K} → record {
        arr = fin-colimit.rep (pres-cocone-to-fin K) ;
        commute = λ{ {(A , A-pres), f} →
          let
            k , g = presentable-split-in-fin A A-pres
            module g = Retract g
            module K = Cocone K
            k-obj : Category.Obj (Cat[ fin ↓ X ])
            k-obj = k , (f ∘ g.retract)
            sliceident =
              begin
              (f ∘ g.retract) ∘ g.section
              ≈⟨ assoc ⟩
              f ∘ g.retract ∘ g.section
              ≈⟨ elimʳ g.is-retract ⟩
              f
              ∎
          in
          begin
          fin-colimit.rep (pres-cocone-to-fin K) ∘ f
            ≈˘⟨ refl⟩∘⟨ elimʳ g.is-retract ⟩
          fin-colimit.rep (pres-cocone-to-fin K) ∘ f ∘ g.retract ∘ g.section
            ≈˘⟨ assoc²' ⟩
          (fin-colimit.rep (pres-cocone-to-fin K) ∘ f ∘ g.retract) ∘ g.section
            ≈⟨ fin-colimit.commute ⟩∘⟨refl ⟩
          Cocone.ψ (pres-cocone-to-fin K) k-obj ∘ g.section
            ≡⟨⟩
          K.ψ (((fin k) , (fin-presented k)) , f ∘ g.retract) ∘ g.section
            ≈⟨ K.commute (slicearr sliceident) ⟩
          K.ψ ((A , A-pres), f)
          ∎
          }};
      !-unique = λ {K} f →
        begin
        fin-colimit.rep (pres-cocone-to-fin K)
            ≈⟨ fin-colimit.initial.!-unique (transform-cocone⇒ f) ⟩
        Cocone⇒.arr f
        ∎
        }
    where
      open Category 𝒞
      open HomReasoning

      pres = presented-obj
      fin-colimit : Colimit (Functor[ fin ↓ X ])
      fin-colimit = Colimit-from-prop (build-from-fin X)
      module fin-colimit = Colimit fin-colimit

      pres-cocone-to-fin : Cocone (Functor[ pres ↓ X ]) → Cocone (Functor[ fin ↓ X ])
      pres-cocone-to-fin K =
        record { coapex =
          record {
            ψ = λ {(k , f) → K.ψ (((fin k) , (fin-presented k)) , f)} ;
            commute = K.commute
          } }
        where
          module K = Cocone K

      transform-cocone⇒ : ∀ {K : Cocone _} →
                          Cocone⇒ _ (Cocone[ presented-obj ↓ X ]) K →
                          Cocone⇒ _ (fin-colimit.colimit) (pres-cocone-to-fin K)
      transform-cocone⇒ {K} mor =
        record {
          arr = Cocone⇒.arr mor ;
          commute = λ { {(k , f)} → Cocone⇒.commute mor }
        }

-- is-presented : { o' e' ℓ₁ ℓ₂ : Level } → 𝒞.Obj → Set _
-- is-presented {o'} {e'} {ℓ₁} {ℓ₂} X =
--   ∀ (P : Poset o' ℓ₁ ℓ₂) →    -- forall diagram schemes
--   non-empty P →               -- which are non-empty
--   directed P →                -- and are directed
--   (J : Functor (Thin e' P) 𝒞) →  -- and all their diagrams
--   preserves-colimit J (Hom[ 𝒞 ][ X ,-]) -- the hom-functor preserves all (existing) colimits

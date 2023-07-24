{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.Construction.Cocones
open import Categories.Object.Initial
open import Categories.Category.Construction.Thin

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
module LFP {o ℓ e} {𝒞 : Category o ℓ e} (κ : Set ℓ) where

module 𝒞 = Category 𝒞

open import Categories.Functor.Hom

open Hom

private
  variable
    -- levels for the diagram scheme:
    o' ℓ' e' : Level
    -- diagram scheme:
    𝒟 : Category o' ℓ' e'
    -- some other category
    o'' ℓ'' e'' : Level
    ℰ : Category o'' ℓ'' e''

-- The property that a functor F preserves the colimit of diagram J:
preserves-colimit : (J : Functor 𝒟 𝒞) → (F : Functor 𝒞 ℰ) → Set _
preserves-colimit J F =
  ∀ (colim : Colimit J) → IsInitial (Cocones (F ∘F J)) (F-map-Coconeˡ F (Colimit.colimit colim))

is-upper-bound : { o' ℓ₁ ℓ₂ : _ } → (P : Poset o' ℓ₁ ℓ₂) → (fam : κ → Poset.Carrier P) → (b : Poset.Carrier P) → Set _
is-upper-bound P fam b = ∀ (x : κ) → fam x ≤ b
  where open Poset P

record UpperBound { o' ℓ₁ ℓ₂ : _ } (P : Poset o' ℓ₁ ℓ₂) (fam : κ → Poset.Carrier P) : Set (suc (o' ⊔ ℓ₁ ⊔ ℓ₂) ⊔ ℓ) where
  field
    bound : Poset.Carrier P
    is-above : is-upper-bound P fam bound

directed : { o' ℓ₁ ℓ₂ : _ } → (P : Poset o' ℓ₁ ℓ₂) → Set _
directed P = ∀ (fam : κ → Poset.Carrier P) → UpperBound P fam

non-empty : { o' ℓ₁ ℓ₂ : _ } → (P : Poset o' ℓ₁ ℓ₂) → Set _
non-empty P = Poset.Carrier P

is-presented : { o' e' ℓ₁ ℓ₂ : Level } → 𝒞.Obj → Set _
is-presented {o'} {e'} {ℓ₁} {ℓ₂} X =
  ∀ (P : Poset o' ℓ₁ ℓ₂) →    -- forall diagram schemes
  non-empty P →               -- which are non-empty
  directed P →                -- and are directed
  (J : Functor (Thin e' P) 𝒞) →  -- and all their diagrams
  preserves-colimit J (Hom[ 𝒞 ][ X ,-]) -- the hom-functor preserves all (existing) colimits


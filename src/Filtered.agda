{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Lift

open import Data.Fin
open import Data.Nat.Base hiding (_⊔_)

module Filtered {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
private
  module 𝒞 = Category 𝒞

record UpperBound (X Y : 𝒞.Obj) : Set (o ⊔ ℓ) where
  -- Upper bound for two objects
  open Category 𝒞
  field
    obj : 𝒞.Obj
    i₁ : X ⇒ obj
    i₂ : Y ⇒ obj

-- The property of having upper bounds for finite sets of objects:
record has-upper-bounds : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞
  field
    non-empty : Obj
    upper-bound : Obj → Obj → Obj
    is-above₁ : ∀ (X Y : Obj) → X ⇒ upper-bound X Y
    is-above₂ : ∀ (X Y : Obj) → Y ⇒ upper-bound X Y

  construct-upper-bound : (X Y : Obj) → UpperBound X Y
  construct-upper-bound X Y =
    record {
      obj = upper-bound X Y ;
      i₁ = is-above₁ X Y ;
      i₂ = is-above₂ X Y }

  fin-upper-bound : ∀ {n : ℕ} → (f : Fin n → Obj) → Obj
  fin-upper-bound {ℕ.zero} f = non-empty
  fin-upper-bound {ℕ.suc n} f = upper-bound
    (f (Fin.zero))
    (fin-upper-bound (λ k → f (Fin.suc k)))

  fin-is-above : ∀ {n : ℕ} → (f : Fin n → Obj) → (k : Fin n) → (f k ⇒ fin-upper-bound f)
  fin-is-above {ℕ.suc n} f Fin.zero = is-above₁ _ _
  fin-is-above {ℕ.suc n} f (Fin.suc k) = is-above₂ _ _ ∘ fin-is-above _ k

-- The property that the diagram of every pair of parallel morphisms
-- has a cocone. There is no name for this in nlab (https://ncatlab.org/nlab/show/filtered+category)
-- nor in the Adamek/Rosicky-book. So let us call it 'merge
record MergedMorphisms {X Y : 𝒞.Obj} (g h : 𝒞 [ X , Y ]) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞
  field
    -- for a pair of parallel morphisms g and h, we obtain:
    -- 1. an object in which the two morphisms will become equal
    tip : 𝒞.Obj
    -- 2. a morphism  to that object:
    merge : Y ⇒ tip
    -- 3. and the property that it makes g and h equal:
    prop : merge ∘ g ≈ merge ∘ h

record MergeAllParallelMorphisms : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞
  field
    merge-all : ∀ {X Y : 𝒞.Obj} (g h : 𝒞 [ X , Y ]) → MergedMorphisms g h

-- the completion of a span to a commuting square
record ClosedSpan {X Y Z : 𝒞.Obj} (g : 𝒞 [ X , Y ]) (h : 𝒞 [ X , Z ]) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞
  field
    tip : 𝒞.Obj
    close-fst : Y ⇒ tip
    close-snd : Z ⇒ tip
    commutes : close-fst ∘ g ≈ close-snd ∘ h

-- the property of a category being filtered
record filtered : Set (o ⊔ ℓ ⊔ e) where
  field
    bounds : has-upper-bounds
    merge-parallel : MergeAllParallelMorphisms

  -- make all fields of bounds and w-coequalizers available
  -- directly here in filtered:
  module bounds = has-upper-bounds bounds
  open bounds public

  module merge-parallel = MergeAllParallelMorphisms merge-parallel
  open merge-parallel public

  open Category 𝒞

  -- We can combine the two fields above to close any span of morphisms
  -- to a commuting square
  close-span : ∀ {X Y Z : Obj} (g : X ⇒ Y) (h : X ⇒ Z) → ClosedSpan g h
  close-span {X} {Y} {Z} g h = record {
    tip = M.tip ;
    close-fst = M.merge ∘ B.i₁;
    close-snd = M.merge ∘ B.i₂ ;
    commutes = assoc ○ M.prop ○ sym-assoc
    }
    where
      open HomReasoning
      B : UpperBound Y Z
      B = construct-upper-bound Y Z
      module B = UpperBound B
      M : MergedMorphisms (B.i₁ ∘ g) (B.i₂ ∘ h)
      M = merge-all (B.i₁ ∘ g) (B.i₂ ∘ h)
      module M = MergedMorphisms M


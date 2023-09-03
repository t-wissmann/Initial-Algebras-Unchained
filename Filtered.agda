{-# OPTIONS --without-K #-}
open import Categories.Category
open import Categories.Functor using (Functor)


module Filtered {o ℓ e} (C : Category o ℓ e) where

open import Level

-- the property of having upper bounds
record has-upper-bounds : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  field
    upper-bound : Obj → Obj → Obj
    is-above₁ : ∀ (X Y : Obj) → X ⇒ upper-bound X Y
    is-above₂ : ∀ (X Y : Obj)  → Y ⇒ upper-bound X Y

-- the property that the diagram of every pair of parallel morphisms
-- has a cocone. There is no name for this in nlab (https://ncatlab.org/nlab/show/filtered+category)
-- nor in the Adamek/Rosicky-book. So let us call it 'fuse'
record fuse-parallel-morphisms : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  field
    -- for each pair of parallel morphisms g and h, we obtain:
    -- 1. an object in which the two morphisms will become equal
    fuse-obj : ∀ {X Y : Obj } ( g h : X ⇒ Y ) → Obj
    -- 2. a morphism  to that object:
    fuse-morph : ∀ {X Y : Obj } ( g h : X ⇒ Y ) →
      (Y ⇒ fuse-obj g h)
    -- 3. and the property that it makes g and h equal:
    fuse-prop : ∀ {X Y : Obj } ( g h : X ⇒ Y ) →
      fuse-morph g h ∘ g ≈ fuse-morph g h ∘ h

-- the property of a category being filtered
record filtered : Set (o ⊔ ℓ ⊔ e) where
  -- so far we do not need non-emptiness
  field
    bounds : has-upper-bounds
    fuse-parallel : fuse-parallel-morphisms

  -- make all fields of bounds and w-coequalizers available
  -- directly here in filtered:
  module bounds = has-upper-bounds bounds
  open bounds public

  module fuse-parallel = fuse-parallel-morphisms fuse-parallel
  open fuse-parallel public

  open Category C

  -- we can combine the above two fields to close any span of morphisms
  -- to a commuting square
  close-span-obj : ∀ {X Y Z : Obj} (y : X ⇒ Y) (z : X ⇒ Z) → Obj
  close-span-obj {X} {Y} {Z} y z =
    fuse-obj (is-above₁ Y Z ∘ y) (is-above₂ Y Z ∘ z)

  close-span-morph₁ : ∀ {X Y Z : Obj} (y : X ⇒ Y) (z : X ⇒ Z) → (Y ⇒ close-span-obj y z)
  close-span-morph₁ {X} {Y} {Z} y z =
    fuse-morph _ _ ∘ (is-above₁ Y Z)

  close-span-morph₂ : ∀ {X Y Z : Obj} (y : X ⇒ Y) (z : X ⇒ Z) → (Z ⇒ close-span-obj y z)
  close-span-morph₂ {X} {Y} {Z} y z =
    fuse-morph _ _ ∘ (is-above₂ Y Z)

  close-span-commutes : ∀ {X Y Z : Obj} (y : X ⇒ Y) (z : X ⇒ Z) →
      (close-span-morph₁ y z ∘ y) ≈ (close-span-morph₂ y z ∘ z)
  close-span-commutes {X} {Y} {Z} y z =
    let
      open HomReasoning
    in
    begin
    close-span-morph₁ y z ∘ y     ≡⟨⟩
    (fuse-morph _ _ ∘ (is-above₁ Y Z)) ∘ y ≈⟨ assoc ⟩
    fuse-morph _ _ ∘ ((is-above₁ Y Z) ∘ y) ≈⟨ fuse-prop _ _ ⟩
    fuse-morph _ _ ∘ ((is-above₂ Y Z) ∘ z) ≈⟨ sym-assoc ⟩
    (fuse-morph _ _ ∘ (is-above₂ Y Z)) ∘ z ≡⟨⟩
    close-span-morph₂ y z ∘ z
    ∎

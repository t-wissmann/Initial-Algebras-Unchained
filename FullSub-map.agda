{-# OPTIONS --without-K --safe #-}
-- Some results about full subcategories when changing the index set
open import Level
open import Agda.Builtin.Equality renaming (refl to ≡-refl)

open import Categories.Category
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Functor hiding (id)

open import Categories.Functor.Construction.SubCategory

open import Unchained-Utils
open import Categories.NaturalTransformation.NaturalIsomorphism

module FullSub-map {o ℓ e} (𝒞 : Category o ℓ e)
                   where

open import Categories.Category.SubCategory
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

𝒞|_ = FullSubCategory 𝒞

private
  module 𝒞 = Category 𝒞

FullSubSubCategory : {i : Level} {I : Set i} (U : I → 𝒞.Obj)
         {i' : Level} {I' : Set i'} (f : I' → I)
         → (𝒞| λ x → U (f x)) ≡ FullSubCategory (𝒞| U) f
FullSubSubCategory U f = ≡-refl

FullSubSubCat : {i : Level} {I : Set i} (U : I → 𝒞.Obj)
         {i' : Level} {I' : Set i'} (f : I' → I)
         → NaturalIsomorphism
            (FullSub 𝒞 {U = λ x → U (f x)})
            (FullSub 𝒞 {U = U} ∘F FullSub (𝒞| U) {U = f})
FullSubSubCat U f =
  let
    open Category 𝒞
    open HomReasoning
  in
  niHelper (record {
    η = λ X → 𝒞.id {U (f X)} ;
    η⁻¹ = λ X → 𝒞.id {U (f X)} ;
    commute = λ h → begin
      id ∘ Functor.F₁ (FullSub 𝒞 {U = λ x → U (f x)}) h ≈⟨ identityˡ ⟩
      Functor.F₁ (FullSub 𝒞 {U = λ x → U (f x)}) h ≡⟨⟩
      Functor.F₁ (FullSub 𝒞 {U = U} ∘F FullSub (𝒞| U) {U = f}) h ≈˘⟨ identityʳ ⟩
      Functor.F₁ (FullSub 𝒞 {U = U} ∘F FullSub (𝒞| U) {U = f}) h ∘ id
      ∎;
    iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityˡ } })

module _ {i : Level} {I : Set i} (U : I → Category.Obj 𝒞)
         {i' : Level} {I' : Set i'} (U' : I' → Category.Obj 𝒞)
         where
  record Reindexing : Set (ℓ ⊔ i ⊔ i' ⊔ e) where
    field
      f : I → I'
      f-≅ : ∀ (x : I) → U x ≅ U' (f x)

    module f-≅ x = _≅_ (f-≅ x)

    to-Functor : Functor (𝒞| U) (𝒞| U')
    to-Functor =
      let open Category 𝒞
          open HomReasoning
          open _≅_
      in
      record
      { F₀ = f
      ; F₁ = λ {A} {B} h → (f-≅ B).from ∘ h ∘ (f-≅ A).to
      ; identity = λ {A} →
        begin
        (f-≅ A).from ∘ id {U A} ∘ (f-≅ A).to ≈⟨ refl⟩∘⟨ identityˡ ⟩
        (f-≅ A).from ∘ (f-≅ A).to ≈⟨ (f-≅ A).isoʳ  ⟩
        id {U' (f A)}
        ∎
      ; homomorphism = λ {X} {Y} {Z} {g} {h} → Equiv.sym (begin
        ((f-≅ Z).from ∘ h ∘ (f-≅ Y).to) ∘ ((f-≅ Y).from ∘ g ∘ (f-≅ X).to) ≈⟨ assoc ⟩
        (f-≅ Z).from ∘ (h ∘ (f-≅ Y).to) ∘ ((f-≅ Y).from ∘ g ∘ (f-≅ X).to) ≈⟨ refl⟩∘⟨ assoc ⟩
        (f-≅ Z).from ∘ h ∘ (f-≅ Y).to ∘ (f-≅ Y).from ∘ g ∘ (f-≅ X).to ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ elimˡ (f-≅.isoˡ Y)) ⟩
        (f-≅ Z).from ∘ h ∘ g ∘ (f-≅ X).to ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        (f-≅ Z).from ∘ (h ∘ g) ∘ (f-≅ X).to
        ∎)
      ; F-resp-≈ = λ {g} {h} g≈h → refl⟩∘⟨ g≈h ⟩∘⟨refl
      }

  _~~>_ : Set _
  _~~>_ = Reindexing


-- translate-colimit : {i i' : Level} {I : Set i} {I' : Set i'}
--                     → (U : I → 𝒞.Obj) → (U' : I' → 𝒞.Obj)
--                     → (f : U ~~> U') → (f⁻¹ : U' ~~> U)
--                     → {o' ℓ' e' : Level}
--                     → {𝒟 : Category o' ℓ' e'}
--                     → {J : Functor (𝒞| U) 𝒟}
--                     → (cocone : Cocone J)
--                     → IsLimitting (F-map-Coconeʳ (Reindexing.to-Functor f⁻¹) cocone)
--                     → IsLimitting cocone
-- translate-colimit U U' f f⁻¹ {J = J} cocone limitting = record
--     { ! = λ {K} → {!limitting.! {F-map-Coconeʳ (Reindexing.to-Functor f⁻¹) K}!}
--     ; !-unique = λ f₁ → {!!}
--     }

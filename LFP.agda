{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.Construction.Cocones
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
module LFP {o ℓ e} (𝒞 : Category o ℓ e) where

private
  module 𝒞 = Category 𝒞

open import Categories.Functor.Slice (𝒞) using (Forgetful)
open import Categories.Functor.Hom
open import Categories.Object.Coproduct (𝒞)
open import Categories.Morphism.Reasoning.Core 𝒞
import Setoids-Colimit

open Hom

private
  variable
    -- levels for the diagram scheme:
    o' ℓ' e' : Level
    -- diagram scheme:
    𝒟 : Category o' ℓ' e'
    -- property of a diagram scheme:
    prop-level : Level
    -- some other category
    o'' ℓ'' e'' : Level
    ℰ : Category o'' ℓ'' e''

-- For each family of fp objects and another objects, we have a slice category:
Cat[_↓_] : {I : Set o'} → (𝒞-fp : I → 𝒞.Obj) → 𝒞.Obj → Category (o' ⊔ ℓ) (ℓ ⊔ e) e
Cat[_↓_]  {I = I} 𝒞-fp X = FullSubCategory (Slice 𝒞 X) objects
  where
    open Category 𝒞
    objects : Σ[ i ∈ I ] (𝒞-fp i ⇒ X) → Category.Obj (Slice 𝒞 X)
    objects (i , i⇒X) = sliceobj i⇒X

-- and an obvious forgetful functor (resp. diagram)
Functor[_↓_] : {I : Set o'} → (𝒞-fp : I → 𝒞.Obj) → (X : 𝒞.Obj) → Functor (Cat[ 𝒞-fp ↓ X ]) 𝒞
Functor[_↓_]  𝒞-fp X = Forgetful ∘F (FullSub _)

-- which has a canonical Cocone: X itself
Cocone[_↓_] : {I : Set o'} → (𝒞-fp : I → 𝒞.Obj) → (X : 𝒞.Obj) → Cocone (Functor[ 𝒞-fp ↓ X ])
Cocone[_↓_]  𝒞-fp X = record { coapex = record {
    ψ = λ (i , i⇒X) → i⇒X ;
    commute = Slice⇒.△
  } }

module _ (o' ℓ' e' : _) (P : Category o' ℓ' e' → Set prop-level) where

  open import Hom-Colimit-Choice 𝒞
  open LiftHom o' ℓ' e'

  presented : 𝒞.Obj → Set _
  presented X =
    ∀ (𝒟 : Category o' ℓ' e') →    -- forall diagram schemes
    P 𝒟 →                          -- satisfying P
    (J : Functor 𝒟 𝒞) →            -- and all their diagrams
    preserves-colimit J LiftHom[ X ,-] -- the hom-functor preserves all (existing) colimits

  -- presented objects are closed under coproducts
  presented-coproduct : {A B : 𝒞.Obj} →
    (∀ {𝒟} → P 𝒟 → filtered 𝒟) → (coprod : Coproduct A B) →
    presented A → presented B → presented (Coproduct.A+B coprod)
  presented-coproduct {A} {B} P⇒filtered coprod A-pres B-pres 𝒟 𝒟-has-P J J-colim =
    hom-colim-construct
      J-colim
      (filtered.bounds (P⇒filtered 𝒟-has-P))
      A+B
      -- Part 1: every morphism A+B -> colim J needs to factor through the diagram:
      (λ [f,g] →
        let
          f = [f,g] ∘ i₁
          g = [f,g] ∘ i₂
          T-f : Triangle _ f
          T-f = hom-colim-choice J-colim A (A-pres 𝒟 𝒟-has-P J) f
          module T-f = Triangle T-f
          T-g : Triangle _ g
          T-g = hom-colim-choice J-colim B (B-pres 𝒟 𝒟-has-P J) g
          module T-g = Triangle T-g

          B = upper-bound T-f.x T-g.x
          p' = [ (J.₁ (is-above₁ _ _) ∘ T-f.p') , (J.₁ (is-above₂ _ _) ∘ T-g.p')  ]

          open HomReasoning
          case1 = begin
            [f,g] ∘ i₁                             ≡⟨⟩
            f                                               ≈⟨ T-f.commutes ⟩
            J-colim.proj T-f.x ∘ T-f.p' ≈˘⟨ J-colim.colimit-commute _ ⟩∘⟨refl ⟩
            (J-colim.proj B ∘ J.₁ (is-above₁ _ _)) ∘ T-f.p' ≈⟨ assoc ⟩
            J-colim.proj B ∘ (J.₁ (is-above₁ _ _) ∘ T-f.p') ≈˘⟨ refl⟩∘⟨ inject₁ ⟩
            J-colim.proj B ∘ p' ∘ i₁ ≈⟨ sym-assoc ⟩
            (J-colim.proj B ∘ p') ∘ i₁
            ∎
          case2 = begin
            [f,g] ∘ i₂                            ≈⟨ T-g.commutes ⟩
            J-colim.proj T-g.x ∘ T-g.p' ≈˘⟨ J-colim.colimit-commute _ ⟩∘⟨refl ⟩
            (J-colim.proj B ∘ J.₁ (is-above₂ _ _)) ∘ T-g.p' ≈⟨ assoc ⟩
            J-colim.proj B ∘ (J.₁ (is-above₂ _ _) ∘ T-g.p') ≈˘⟨ refl⟩∘⟨ inject₂ ⟩
            J-colim.proj B ∘ p' ∘ i₂ ≈⟨ sym-assoc ⟩
            (J-colim.proj B ∘ p') ∘ i₂
            ∎
        in
        record {
          x = B ;
          p' = p' ;
          commutes =
            begin
            [f,g]        ≈˘⟨ g-η ⟩
            [ f , g ]    ≈⟨ unique (⟺ case1) (⟺ case2) ⟩
            J-colim.proj B ∘ p'
            ∎
          })
      -- Part 2: if we have two factorizations, then they
      -- are identified within the diagram:
      λ {i} [f,g] [f',g'] pr∘fg≈pr∘fg' →
        let
          module fil = filtered (P⇒filtered 𝒟-has-P)
          open HomReasoning

          f = [f,g] ∘ i₁
          g = [f,g] ∘ i₂
          f' = [f',g'] ∘ i₁
          g' = [f',g'] ∘ i₂
          pr∘f≈pr∘f' : J-colim.proj i ∘ ([f,g] ∘ i₁) ≈ J-colim.proj i ∘ ([f',g'] ∘ i₁)
          pr∘f≈pr∘f' = extendʳ pr∘fg≈pr∘fg'
          i-f , u-f , (u-f' , u-f∘f≈u-f'∘f') =
            hom-colim-unique-factor J-colim (P⇒filtered 𝒟-has-P)
                  A A-preserves-J _ _ pr∘f≈pr∘f'
          v-f = fil.fuse-morph u-f u-f' 𝒟.∘ u-f
          v-f-prop : J.₁ v-f ∘ f ≈ J.₁ v-f ∘ f'
          v-f-prop =
            begin
            J.₁ v-f ∘ f         ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
            (J.₁ (fil.fuse-morph u-f u-f') ∘ J.₁ u-f) ∘ f    ≈⟨ extendˡ u-f∘f≈u-f'∘f' ⟩
            (J.₁ (fil.fuse-morph u-f u-f') ∘ J.₁ u-f') ∘ f'  ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
            J.₁ (fil.fuse-morph u-f u-f' 𝒟.∘ u-f') ∘ f'      ≈˘⟨ J.F-resp-≈ (fil.fuse-prop u-f u-f') ⟩∘⟨refl ⟩
            J.₁ v-f ∘ f'
            ∎

          -- same for g:
          i-g , u-g , (u-g' , u-g∘g≈u-g'∘g') =
            hom-colim-unique-factor J-colim (P⇒filtered 𝒟-has-P)
                  B B-preserves-J g g' (extendʳ pr∘fg≈pr∘fg')
          v-g = fil.fuse-morph u-g u-g' 𝒟.∘ u-g
          v-g-prop : J.₁ v-g ∘ g ≈ J.₁ v-g ∘ g'
          v-g-prop =
            begin
            J.₁ v-g ∘ g         ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
            (J.₁ (fil.fuse-morph u-g u-g') ∘ J.₁ u-g) ∘ g    ≈⟨ extendˡ u-g∘g≈u-g'∘g' ⟩
            (J.₁ (fil.fuse-morph u-g u-g') ∘ J.₁ u-g') ∘ g'  ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
            J.₁ (fil.fuse-morph u-g u-g' 𝒟.∘ u-g') ∘ g'      ≈˘⟨ J.F-resp-≈ (fil.fuse-prop u-g u-g') ⟩∘⟨refl ⟩
            J.₁ v-g ∘ g'
            ∎

          -- we then merge the span v-f and v-g to one commuting square
          i' = fil.close-span-obj v-f v-g
          e-f = fil.close-span-morph₁ v-f v-g
          e-g = fil.close-span-morph₂ v-f v-g
          m = e-f 𝒟.∘ v-f
          case1 =
            begin
            (J.₁ m ∘ [f,g]) ∘ i₁        ≈⟨ assoc ⟩
            J.₁ m ∘ f          ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
            (J.₁ e-f ∘ J.₁ v-f) ∘ f        ≈⟨ assoc ⟩
            J.₁ e-f ∘ (J.₁ v-f ∘ f)        ≈⟨ refl⟩∘⟨ v-f-prop ⟩
            J.₁ e-f ∘ (J.₁ v-f ∘ f')        ≈⟨ sym-assoc ⟩
            (J.₁ e-f ∘ J.₁ v-f) ∘ f'        ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
            J.₁ m ∘ [f',g'] ∘ i₁        ≈⟨ sym-assoc ⟩
            (J.₁ m ∘ [f',g']) ∘ i₁
            ∎
          case2 =
            begin
            (J.₁ m ∘ [f,g]) ∘ i₂        ≈⟨ assoc ⟩
            J.₁ m ∘ g          ≈⟨ J.F-resp-≈ (fil.close-span-commutes v-f v-g) ⟩∘⟨refl ⟩
            J.₁ (e-g 𝒟.∘ v-g) ∘ g          ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
            (J.₁ e-g ∘ J.₁ v-g) ∘ g        ≈⟨ assoc ⟩
            J.₁ e-g ∘ (J.₁ v-g ∘ g)        ≈⟨ refl⟩∘⟨ v-g-prop ⟩ -- refl⟩∘⟨ v-g-prop ⟩
            J.₁ e-g ∘ (J.₁ v-g ∘ g')        ≈⟨ sym-assoc ⟩
            (J.₁ e-g ∘ J.₁ v-g) ∘ g'        ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
            J.₁ (e-g 𝒟.∘ v-g) ∘ [f',g'] ∘ i₂        ≈˘⟨ J.F-resp-≈ (fil.close-span-commutes v-f v-g) ⟩∘⟨refl ⟩
            J.₁ m ∘ [f',g'] ∘ i₂        ≈⟨ sym-assoc ⟩
            (J.₁ m ∘ [f',g']) ∘ i₂
            ∎
        in
        i' , (m , (m , (
            begin
            (J.₁ m ∘ [f,g])        ≈˘⟨ g-η ⟩
            [ (J.₁ m ∘ [f,g]) ∘ i₁ , (J.₁ m ∘ [f,g]) ∘ i₂ ]        ≈⟨ []-cong₂ case1 case2 ⟩
            [ (J.₁ m ∘ [f',g']) ∘ i₁ , (J.₁ m ∘ [f',g']) ∘ i₂ ]        ≈⟨ g-η ⟩
            (J.₁ m ∘ [f',g'])
            ∎
            )))
    where
      open Coproduct coprod
      open Category 𝒞
      module 𝒟 = Category 𝒟
      module J = Functor J
      module J-colim = Colimit J-colim
      open has-upper-bounds (filtered.bounds (P⇒filtered 𝒟-has-P))
      A-preserves-J = A-pres 𝒟 𝒟-has-P J J-colim
      B-preserves-J = B-pres 𝒟 𝒟-has-P J J-colim
      Hom-A-colim = Colimit-from-prop A-preserves-J
      Hom-B-colim = Colimit-from-prop B-preserves-J


  record WeaklyLFP : Set (o ⊔ suc (ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e' ⊔ prop-level)) where
    field
      -- a (small)family (resp. 'set') of objects ...
      Idx : Set o'
      fin : Idx → 𝒞.Obj
      -- ... of which every element is fp:
      fin-presented : ∀ (i : Idx) → presented (fin i)
      -- All other objects are built from those fp objects:
      build-from-fin : ∀ (X : 𝒞.Obj) → IsLimitting (Cocone[ fin ↓ X ])
      -- and moreover every canonical diagram is filtered
      canonical-has-prop : ∀ (X : 𝒞.Obj) → filtered (Cat[ fin ↓ X ])

    canonical-diagram-scheme : ∀ (X : 𝒞.Obj) → Category (o' ⊔ ℓ) (e ⊔ ℓ) e
    canonical-diagram-scheme X = Cat[ fin ↓ X ]

    canonical-diagram : ∀ (X : 𝒞.Obj) → Functor (canonical-diagram-scheme X) 𝒞
    canonical-diagram X = Functor[ fin ↓ X ]

    canonical-colimit : ∀ (X : 𝒞.Obj) → Colimit (canonical-diagram X)
    canonical-colimit X = Colimit-from-prop (build-from-fin X)




-- is-presented : { o' e' ℓ₁ ℓ₂ : Level } → 𝒞.Obj → Set _
-- is-presented {o'} {e'} {ℓ₁} {ℓ₂} X =
--   ∀ (P : Poset o' ℓ₁ ℓ₂) →    -- forall diagram schemes
--   non-empty P →               -- which are non-empty
--   directed P →                -- and are directed
--   (J : Functor (Thin e' P) 𝒞) →  -- and all their diagrams
--   preserves-colimit J (Hom[ 𝒞 ][ X ,-]) -- the hom-functor preserves all (existing) colimits

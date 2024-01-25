{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Diagram.Colimit

open import Data.Product

open import Colimit-Lemmas
open import Filtered

module Presentable {o ℓ fil-level}
  (𝒞 : Category o ℓ ℓ)
  (o' ℓ' e' : Level) -- The level for the diagram schemes of interest
  (Fil : Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  where

private
  module 𝒞 = Category 𝒞

open import Hom-Colimit-Choice 𝒞
open LiftHom o' ℓ' e'
open import Categories.Object.Coproduct (𝒞)
open import Categories.Morphism (𝒞)
open import Categories.Morphism.Reasoning.Core 𝒞

presentable : 𝒞.Obj → Set _
presentable X =
  ∀ (𝒟 : Category o' ℓ' e') → -- forall diagram schemes
  Fil 𝒟 →                     -- satisfying some notion of filteredness
  (J : Functor 𝒟 𝒞) →         -- and all their diagrams
  preserves-colimit J LiftHom[ X ,-] -- the hom-functor preserves all (existing) colimits

-- presentable objects are closed under coproducts
presentable-coproduct : {A B : 𝒞.Obj} → (coprod : Coproduct A B) →
  (∀ {𝒟} → Fil 𝒟 → filtered 𝒟) → -- 'Fil' implies filtered
  presentable A → presentable B → presentable (Coproduct.A+B coprod)
presentable-coproduct {A} {B} coprod P⇒filtered A-pres B-pres 𝒟 𝒟-has-P J J-colim =
  hom-colim-construct
    J-colim
    (filtered.bounds (P⇒filtered 𝒟-has-P))
    A+B
    -- Part 1: every morphism A+B -> colim J needs to factor through the diagram:
    (λ [f,g] → Part1.goal [f,g])
    -- Part 2: if we have two factorizations, then they
    -- are identified within the diagram:
    λ {i} [f,g] [f',g'] pr∘fg≈pr∘fg' →
      let
        open Part2 i [f,g] [f',g'] pr∘fg≈pr∘fg'
      in
      i' , (m , (m , (
          coproduct-jointly-epic coprod
            (record { case-precompose-i₁ = case1 ; case-precompose-i₂ = case2 }))))
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

    module Part1 ([f,g] : A+B ⇒ J-colim.coapex) where
        f = [f,g] ∘ i₁
        g = [f,g] ∘ i₂
        T-f : Triangle _ f
        T-f = hom-colim-choice J-colim A (A-pres 𝒟 𝒟-has-P J) f
        module T-f = Triangle T-f
        T-g : Triangle _ g
        T-g = hom-colim-choice J-colim B (B-pres 𝒟 𝒟-has-P J) g
        module T-g = Triangle T-g

        Bo = upper-bound T-f.x T-g.x
        p' = [ (J.₁ (is-above₁ _ _) ∘ T-f.p') , (J.₁ (is-above₂ _ _) ∘ T-g.p')  ]

        open HomReasoning
        case1 = begin
          [f,g] ∘ i₁                             ≡⟨⟩
          f                                               ≈⟨ T-f.commutes ⟩
          J-colim.proj T-f.x ∘ T-f.p' ≈˘⟨ J-colim.colimit-commute _ ⟩∘⟨refl ⟩
          (J-colim.proj Bo ∘ J.₁ (is-above₁ _ _)) ∘ T-f.p' ≈⟨ assoc ⟩
          J-colim.proj Bo ∘ (J.₁ (is-above₁ _ _) ∘ T-f.p') ≈˘⟨ refl⟩∘⟨ inject₁ ⟩
          J-colim.proj Bo ∘ p' ∘ i₁ ≈⟨ sym-assoc ⟩
          (J-colim.proj Bo ∘ p') ∘ i₁
          ∎
        case2 = begin
          [f,g] ∘ i₂                            ≈⟨ T-g.commutes ⟩
          J-colim.proj T-g.x ∘ T-g.p' ≈˘⟨ J-colim.colimit-commute _ ⟩∘⟨refl ⟩
          (J-colim.proj Bo ∘ J.₁ (is-above₂ _ _)) ∘ T-g.p' ≈⟨ assoc ⟩
          J-colim.proj Bo ∘ (J.₁ (is-above₂ _ _) ∘ T-g.p') ≈˘⟨ refl⟩∘⟨ inject₂ ⟩
          J-colim.proj Bo ∘ p' ∘ i₂ ≈⟨ sym-assoc ⟩
          (J-colim.proj Bo ∘ p') ∘ i₂
          ∎
        goal : Triangle J-colim [f,g]
        goal = record {
          x = Bo ;
          p' = p' ;
          commutes = coproduct-jointly-epic coprod (record {
            case-precompose-i₁ = case1 ;
            case-precompose-i₂ = case2 })
          }
    module Part2 (i : 𝒟.Obj) ([f,g] [f',g'] : A+B ⇒ J.F₀ i)
                  (pr∘fg≈pr∘fg' : J-colim.proj i ∘ [f,g] ≈ J-colim.proj i ∘ [f',g']) where
      module fil = filtered (P⇒filtered 𝒟-has-P)
      open HomReasoning

      f = [f,g] ∘ i₁
      g = [f,g] ∘ i₂
      f' = [f',g'] ∘ i₁
      g' = [f',g'] ∘ i₂
      pr∘f≈pr∘f' : J-colim.proj i ∘ ([f,g] ∘ i₁) ≈ J-colim.proj i ∘ ([f',g'] ∘ i₁)
      pr∘f≈pr∘f' = extendʳ pr∘fg≈pr∘fg'
      i-u-f-f'-prop =
        hom-colim-unique-factor J-colim (P⇒filtered 𝒟-has-P)
              A A-preserves-J _ _ pr∘f≈pr∘f'
      i-f = proj₁ i-u-f-f'-prop
      u-f = proj₁ (proj₂ i-u-f-f'-prop)
      u-f' = proj₁ (proj₂(proj₂ i-u-f-f'-prop))
      u-f∘f≈u-f'∘f' = (proj₂(proj₂(proj₂ i-u-f-f'-prop)))

      Mf = fil.merge-all u-f u-f'
      module Mf = MergedMorphisms Mf
      v-f = Mf.merge 𝒟.∘ u-f
      v-f-prop : J.₁ v-f ∘ f ≈ J.₁ v-f ∘ f'
      v-f-prop =
        begin
        J.₁ v-f ∘ f         ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
        (J.₁ Mf.merge ∘ J.₁ u-f) ∘ f    ≈⟨ extendˡ u-f∘f≈u-f'∘f' ⟩
        (J.₁ Mf.merge ∘ J.₁ u-f') ∘ f'  ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
        J.₁ (Mf.merge 𝒟.∘ u-f') ∘ f'      ≈˘⟨ J.F-resp-≈ Mf.prop ⟩∘⟨refl ⟩
        J.₁ v-f ∘ f'
        ∎

      -- same for g:
      g-unique-factor =
        hom-colim-unique-factor J-colim (P⇒filtered 𝒟-has-P)
              B B-preserves-J g g' (extendʳ pr∘fg≈pr∘fg')
      i-g = proj₁ g-unique-factor
      u-g = proj₁ (proj₂ g-unique-factor)
      u-g' = proj₁ (proj₂(proj₂ g-unique-factor))
      u-g∘g≈u-g'∘g' = (proj₂(proj₂(proj₂ g-unique-factor)))
      Mg = fil.merge-all u-g u-g'
      module Mg = MergedMorphisms Mg
      v-g = Mg.merge 𝒟.∘ u-g
      v-g-prop : J.₁ v-g ∘ g ≈ J.₁ v-g ∘ g'
      v-g-prop =
        begin
        J.₁ v-g ∘ g         ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
        (J.₁ Mg.merge ∘ J.₁ u-g) ∘ g    ≈⟨ extendˡ u-g∘g≈u-g'∘g' ⟩
        (J.₁ Mg.merge ∘ J.₁ u-g') ∘ g'  ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
        J.₁ (Mg.merge 𝒟.∘ u-g') ∘ g'      ≈˘⟨ J.F-resp-≈ Mg.prop ⟩∘⟨refl ⟩
        J.₁ v-g ∘ g'
        ∎

      -- we then merge the span v-f and v-g to one commuting square
      closed = fil.close-span v-f v-g
      module closed = ClosedSpan closed
      i' = closed.tip
      e-f = closed.close-fst
      e-g = closed.close-snd
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
        J.₁ m ∘ g          ≈⟨ J.F-resp-≈ closed.commutes ⟩∘⟨refl ⟩
        J.₁ (e-g 𝒟.∘ v-g) ∘ g          ≈⟨ J.homomorphism ⟩∘⟨refl ⟩
        (J.₁ e-g ∘ J.₁ v-g) ∘ g        ≈⟨ assoc ⟩
        J.₁ e-g ∘ (J.₁ v-g ∘ g)        ≈⟨ refl⟩∘⟨ v-g-prop ⟩ -- refl⟩∘⟨ v-g-prop ⟩
        J.₁ e-g ∘ (J.₁ v-g ∘ g')        ≈⟨ sym-assoc ⟩
        (J.₁ e-g ∘ J.₁ v-g) ∘ g'        ≈˘⟨ J.homomorphism ⟩∘⟨refl ⟩
        J.₁ (e-g 𝒟.∘ v-g) ∘ [f',g'] ∘ i₂        ≈˘⟨ J.F-resp-≈ closed.commutes ⟩∘⟨refl ⟩
        J.₁ m ∘ [f',g'] ∘ i₂        ≈⟨ sym-assoc ⟩
        (J.₁ m ∘ [f',g']) ∘ i₂
        ∎

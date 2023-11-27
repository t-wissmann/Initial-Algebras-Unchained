{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Data.Product

open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Functor.Construction.LiftSetoids
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone.Properties

open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

import Setoids-Choice as Setoids
import Setoids-Colimit
open import Setoids-Colimit using (KernelPairs)
open import Unchained-Utils
open import Filtered

module Hom-Colimit-Choice
  {o ℓ e} (𝒞 : Category o ℓ e)
  where

private
    module 𝒞 = Category 𝒞

open import Categories.Morphism.Reasoning.Core 𝒞

module LiftHom (o' ℓ' e' : Level) where
  -- in the definition of presented object, we lift the hom setoids to a higher
  -- level such that setoids are cocomplete:
  LiftHom[_,-] : 𝒞.Obj → Functor 𝒞 (Setoids (ℓ ⊔ o') (o' ⊔ ℓ' ⊔ e ⊔ ℓ))
  LiftHom[_,-] X = LiftSetoids (ℓ ⊔ o') (o' ⊔ ℓ' ⊔ e ⊔ ℓ) ∘F Hom[ 𝒞 ][ X ,-]

module _
  {o' ℓ' e' : Level}
  {𝒟 : Category o' ℓ' e'}
  {D : Functor 𝒟 𝒞}
  (colim : Colimit D)
  where

  open Hom 𝒞
  open LiftHom o' ℓ' e'

  private
      module colim = Colimit colim
      module 𝒟 = Category 𝒟
      module D = Functor D

      open Category 𝒞

  record Triangle {P : 𝒞.Obj} (p : P ⇒ colim.coapex) : Set (o' ⊔ ℓ ⊔ e) where
    -- a factorization of a morphism through the diagram.
    constructor triangle
    field
      x : 𝒟.Obj
      p' : P ⇒ D.₀ x
      commutes : p ≈ colim.proj x ∘ p'

  -- If a hom-functor 𝒞(P,-) preserves a colimit C, this gives rise to a
  -- factorization of morphisms P ⇒ C through the diagram:
  hom-colim-choice : (P : 𝒞.Obj) →
      preserves-colimit D LiftHom[ P ,-] →
      (p : P ⇒ colim.coapex) →
      Triangle p
  hom-colim-choice P hom-preserves-colim p =
    let
      homset-colimit = Colimit-from-prop (hom-preserves-colim colim)
      module homset-colimit = Colimit homset-colimit

      x , p' = Setoids.colimit-choice {o'} {ℓ'} {e'} {ℓ ⊔ o'} {o' ⊔ ℓ' ⊔ e ⊔ ℓ} homset-colimit (lift p)

      open Setoid renaming (_≈_ to _[[_≈_]])
      commutes : homset-colimit.coapex [[ (lift p) ≈ homset-colimit.proj x ⟨$⟩ p' ]]
      commutes =
        (Setoids.colimit-choice-correct {o'} {ℓ'} {e'} {ℓ ⊔ o'} {o' ⊔ ℓ' ⊔ e ⊔ ℓ} homset-colimit {lift p})

      -- since hom functors are defined as bi-functor, we have an ∘id on the right:
      commutes-in-𝒞 : p ≈ colim.proj x ∘ (lower p') ∘ id
      commutes-in-𝒞 = lower commutes

      open HomReasoning
    in
    record { x = x ; p' = lower p' ;
      commutes =
        begin
        p                            ≈⟨ commutes-in-𝒞 ⟩
        colim.proj x ∘ (lower p') ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
        colim.proj x ∘ (lower p')
        ∎
      }

  -- The property that morphisms from a given object factorize (at most) uniquely
  -- through the diagram D:
  UniqueColimitFactorization : 𝒞.Obj → Set _
  UniqueColimitFactorization P =
      ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → colim.proj i ∘ f ≈ colim.proj i ∘ g →
        Σ[ i' ∈ 𝒟.Obj ] Σ[ f' ∈ i 𝒟.⇒ i' ] Σ[ g' ∈ i 𝒟.⇒ i' ] (D.₁ f' ∘ f ≈ D.₁ g' ∘ g)

  -- The same property, but with a single identifying morphism:
  UniqueColimitFactorization₁ : 𝒞.Obj → Set _
  UniqueColimitFactorization₁ P =
      ∀ {i : 𝒟.Obj} (f g : P ⇒ D.₀ i) → colim.proj i ∘ f ≈ colim.proj i ∘ g →
        Σ[ i' ∈ 𝒟.Obj ] Σ[ h ∈ i 𝒟.⇒ i' ] (D.₁ h ∘ f ≈ D.₁ h ∘ g)

  -- If the diagram is filtered, then the above two properties are equivalent:
  coequalize-colimit-factorization : (P : 𝒞.Obj) → filtered 𝒟 →
    UniqueColimitFactorization P →
    UniqueColimitFactorization₁ P
  coequalize-colimit-factorization P fil factor2 {i} f g eq-proj =
    let
      -- We take the factorization with the two injections:
      j , f' , (g' , binary-prop) = factor2 {i} f g eq-proj
      -- and the merge f' and g'
      module fil = fuse-parallel-morphisms (filtered.fuse-parallel fil)
      i' = fil.fuse-obj f' g'
      k = fil.fuse-morph f' g'
      open HomReasoning
    in
    i' , ((k 𝒟.∘ f') , (begin
      D.₁ (k 𝒟.∘ f') ∘ f ≈⟨ D.homomorphism ⟩∘⟨refl ⟩
      (D.₁ k ∘ D.₁ f') ∘ f ≈⟨ assoc ⟩
      D.₁ k ∘ (D.₁ f' ∘ f) ≈⟨ refl⟩∘⟨ binary-prop ⟩
      D.₁ k ∘ (D.₁ g' ∘ g) ≈⟨ sym-assoc ⟩
      (D.₁ k ∘ D.₁ g') ∘ g ≈˘⟨ D.homomorphism ⟩∘⟨refl ⟩
      D.₁ (k 𝒟.∘ g') ∘ g ≈˘⟨ D.F-resp-≈ (fil.fuse-prop f' g') ⟩∘⟨refl ⟩
      D.₁ (k 𝒟.∘ f') ∘ g
    ∎))

  hom-colim-unique-factor :
      filtered 𝒟 →
      (P : 𝒞.Obj) →
      IsLimitting (F-map-Coconeˡ (LiftHom[ P ,-]) (Colimit.colimit colim)) →
      UniqueColimitFactorization P
  hom-colim-unique-factor fil P is-colim {i} f g pr∘f≈pr∘g =
    I.B , I.inj₁ , (I.inj₂ , (begin
      D.₁ I.inj₁ ∘ f ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
      D.₁ I.inj₁ ∘ f ∘ id ≈⟨ Level.lower I.identifies ⟩
      D.₁ I.inj₂ ∘ g ∘ id ≈⟨ refl⟩∘⟨ identityʳ ⟩
      D.₁ I.inj₂ ∘ g
      ∎))
    where
      open HomReasoning

      ident-f-g : Setoids-Colimit.identified-in-diagram (LiftHom[ P ,-] ∘F D) (Level.lift f) (Level.lift g)
      ident-f-g =
        Setoids-Colimit.filtered-identification-colim
          {c = ℓ ⊔ o'} {ℓ' = o' ⊔ ℓ' ⊔ e ⊔ ℓ} -- TODO: why can't the levels be inferred from LiftHom[_,-]?
          (LiftHom[ P ,-] ∘F D)
          (Colimit-from-prop is-colim)
          fil
          (lift (begin
           colim.proj i ∘ f ∘ id  ≈⟨ refl⟩∘⟨ identityʳ ⟩
           colim.proj i ∘ f  ≈⟨ pr∘f≈pr∘g ⟩
           colim.proj i ∘ g  ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
           colim.proj i ∘ g ∘ id
           ∎))

      module I = Setoids-Colimit.identified-in-diagram ident-f-g

  -- a variant of hom-colim-unique-factor with only one
  -- connecting morphism within the diagram:
  hom-colim-unique-factor₁ :
      filtered 𝒟 →
      (P : 𝒞.Obj) →
      IsLimitting (F-map-Coconeˡ (LiftHom[ P ,-]) (Colimit.colimit colim)) →
      UniqueColimitFactorization₁ P
  hom-colim-unique-factor₁ fil P is-colim =
    coequalize-colimit-factorization P fil
      (hom-colim-unique-factor fil P is-colim)


  -- A hom-functor 𝒞(P,-) preserves a colimit C given that
  -- 1. all morphisms P ⇒ C factor through the diagram.
  -- 2. the factorization is unique in the sense that
  --    if there are f g : P ⇒ D.₀ i which are identified in the colimit,
  --    then there is some morphism in the diagram which identifies f and g
  hom-colim-construct :
      has-upper-bounds 𝒟 →
      (P : 𝒞.Obj) →
      (∀ (f : P ⇒ colim.coapex) → Triangle f) →
      UniqueColimitFactorization P →
      IsLimitting (F-map-Coconeˡ (LiftHom[ P ,-]) (Colimit.colimit colim))
  hom-colim-construct bounds P all-factor uniq-factor =
    Setoids-Colimit.bounded-colimiting
      {c = ℓ ⊔ o'} {ℓ' = o' ⊔ ℓ' ⊔ e ⊔ ℓ} -- TODO: why can't the levels be inferred from LiftHom[_,-]?
      (LiftHom[ P ,-] ∘F D)
      (F-map-Coconeˡ (LiftHom[ P ,-]) (Colimit.colimit colim))
      bounds
      -- Part 1: show that every element in the colimit comes from
      -- somewhere in the diagram
      (λ (lift f) →
        let
          module T = Triangle (all-factor f)
          open HomReasoning
        in
        record {
          i = T.x ;
          preimage = lift T.p' ;
          x-sent-to-c = lift (begin
            colim.proj T.x ∘ T.p' ∘ id
              ≈⟨ sym-assoc ⟩
            (colim.proj T.x ∘ T.p') ∘ id
              ≈⟨ identityʳ  ⟩
            colim.proj T.x ∘ T.p'
              ≈˘⟨ T.commutes  ⟩
            f
            ∎)
          }
        )
      -- Part 2: if two elements from the diagram are identified
      -- in the colimit, then they are identified already
      -- somewhere in the diagram
      λ {i} kp →
        let
          module kp = KernelPairs kp
          open HomReasoning
          f = Level.lower kp.pr₁
          g = Level.lower kp.pr₂
          f-g-ident : colim.proj i ∘ f ≈ colim.proj i ∘ g
          f-g-ident = begin
            (colim.proj i ∘ f)           ≈˘⟨ (refl⟩∘⟨ identityʳ) ⟩
            (colim.proj i ∘ f ∘ id)      ≈⟨ Level.lower kp.identified ⟩
            (colim.proj i ∘ g ∘ id)      ≈⟨ (refl⟩∘⟨ identityʳ) ⟩
            (colim.proj i ∘ g)
            ∎
          i' , f' , g' , Df'∘f≈Dg'∘g = uniq-factor f g f-g-ident
        in
        record {
          B = i' ; inj₁ = f' ; inj₂ = g' ; identifies =
            Level.lift (begin
              D.₁ f' ∘ f ∘ id        ≈⟨ refl⟩∘⟨ identityʳ ⟩
              D.₁ f' ∘ f             ≈⟨ Df'∘f≈Dg'∘g ⟩
              D.₁ g' ∘ g             ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
              D.₁ g' ∘ g ∘ id
            ∎)
          }

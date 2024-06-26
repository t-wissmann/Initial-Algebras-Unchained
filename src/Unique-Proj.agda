{-# OPTIONS --without-K --safe #-}
open import Level

-- Aim of this file: sufficient conditions such that
-- a coalgebra colimit has unique projection/injection homorphisms.

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Diagram.Colimit

open import Filtered
open import CoalgColim
open import F-Coalgebra-Colimit
open import Iterate.Assumptions
open import Data.Product
open import Categories.Functor.Properties using (Full)

module Unique-Proj {o ℓ fil-level}
  (𝒞 : Category o ℓ ℓ)
  (F : Endofunctor 𝒞)
  (Fil : Category (o ⊔ ℓ) ℓ ℓ → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category (o ⊔ ℓ) ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (A,α : CoalgColim 𝒞 F (FiniteRecursive {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil) {o ⊔ ℓ} {ℓ} {ℓ})
  where

open import Categories.Morphism.Reasoning.Core 𝒞
open import Presentable 𝒞 (o ⊔ ℓ) ℓ ℓ Fil
open import Colimit-Lemmas
open import Helper-Definitions

-- given a coalgebra colimit A,α, its projection homomorphisms
-- are the unique homomorphisms from the diagram elements to the colimit.
--
private
  module A,α = CoalgColim.CoalgColim A,α
  open import Hom-Colimit-Choice
  open Hom-Colimit-Choice.LiftHom 𝒞 ℓ ℓ ℓ


hom-to-coalg-colim-triangle : ∀ {B,β : F-Coalgebra F} →
  presentable (F-Coalgebra.A B,β) →
  preserves-colimit (forget-Coalgebra ∘F A,α.D) F →
  -- ^- F preserves the colimit 'coalg'
  (h : F-Coalgebras F [ B,β , A,α.to-Coalgebra ]) →
  Fil (CoalgColim.𝒟 A,α) →
  Triangle (F-Coalgebras F) A,α.colim h
hom-to-coalg-colim-triangle {B,β} B-presentable F-finitary h 𝒟-Fil =
  triangle i g∘p' g∘p'-equation
  where
    module F = Functor F
    -- we denote the forgetful functor by U:
    U = forget-Coalgebra
    module U = Functor U
    open Category 𝒞
    open F-Coalgebra A,α.to-Coalgebra
    open F-Coalgebra B,β renaming (A to B; α to β)
    module h = F-Coalgebra-Morphism h
    -- Since B is presentable, we obtain a Triangle in 𝒞:
    t : Triangle 𝒞 A,α.carrier-colim h.f
    t = hom-colim-choice 𝒞 A,α.carrier-colim B
      (B-presentable A,α.𝒟 𝒟-Fil (forget-Coalgebra ∘F A,α.D))
      h.f
    module t = Triangle t
    -- denote the intermediate coalgebra by:
    X = A,α.D.₀ t.x
    module X = F-Coalgebra X
    -- Even though t.p' : B → D t.x is a factorization through the diagram,
    -- t.p' is not necessarily a coalgebra homomorphism from B,β to X. The
    -- homomorphism square for t.p' would have these two paths:
    p₁ : B ⇒ F.₀ (A,α.U∘D.₀ t.x)
    p₁ = X.α ∘ t.p'
    p₂ : B ⇒ F.₀ (A,α.U∘D.₀ t.x)
    p₂ = F.₁ t.p' ∘ β
    -- We will use that p₁ and p₂ are competing factorizations for the colimit
    -- obtained after applying F.
    -- For this, we let the functor F preserve the colimit:
    F-colim : Colimit (F ∘F forget-Coalgebra ∘F A,α.D)
    F-colim = Colimit-from-prop (F-finitary A,α.carrier-colim)
    module F-colim = Colimit F-colim

    p₁-vs-p₂ : F-colim.proj t.x ∘ p₁ ≈ F-colim.proj t.x ∘ p₂
    p₁-vs-p₂ =
      -- We use the following diagram:
      --     .------ h --------.
      --    /                  V
      --   B -t.p'-> X -proj-> A
      --   |         |         |
      --  β|    ?    |   hom   |α
      --   V         V         V
      --   FB ----> FX -----> FA
      begin
      F-colim.proj t.x ∘ p₁ ≡⟨⟩
      F.₁ (U.₁ (A,α.colim.proj t.x)) ∘ X.α ∘ t.p'
        ≈˘⟨ extendʳ (F-Coalgebra-Morphism.commutes (A,α.colim.proj t.x)) ⟩
      α ∘ U.₁ (A,α.colim.proj t.x) ∘ t.p'
        ≈˘⟨ refl⟩∘⟨ t.commutes ⟩
      α ∘ h.f
        ≈⟨ h.commutes ⟩
      F.₁ h.f ∘ β
        ≈⟨ pushˡ (F.F-resp-≈ t.commutes ○ F.homomorphism) ⟩
      F.₁ (U.₁ (A,α.colim.proj t.x)) ∘ F.₁ t.p' ∘ β ≡⟨⟩
      F-colim.proj t.x ∘ p₂
      ∎
      where open HomReasoning

    -- Since the diagram scheme is filtered, p₁ and p₂ are merged somewhere
    -- within the diagram, as the following Σ-type witnesses:
    dia-merge =
      hom-colim-unique-factor₁
          -- Basic facts about the colimit:
          𝒞 F-colim (Fil-to-filtered 𝒟-Fil) B
          -- Using that hom(B,-) preserves it:
          (B-presentable A,α.𝒟 𝒟-Fil (F ∘F A,α.U∘D) F-colim)
          -- the competing factorizations:
          p₁ p₂ p₁-vs-p₂

    i : A,α.𝒟.Obj
    i = proj₁ dia-merge
    -- call the coalgebra Y:
    Y = A,α.D.₀ i
    module Y = F-Coalgebra Y
    -- The connecting morphism in the diagram:
    g : F-Coalgebra-Morphism X Y
    g = A,α.D.₁ (proj₁ (proj₂ dia-merge))
    module g = F-Coalgebra-Morphism g
    -- which has the property that it merges p₁ and p₂:
    g-merges : F.₁ g.f ∘ p₁ ≈ F.₁ g.f ∘ p₂
    g-merges = proj₂ (proj₂ dia-merge)


    -- Its composition with t.p' is the desired factorization:
    g∘p' : F-Coalgebra-Morphism B,β Y
    g∘p' = record {
      f = g.f ∘ t.p' ;
      commutes =
        let open HomReasoning in
        begin
        Y.α ∘ g.f ∘ t.p' ≈⟨ extendʳ g.commutes ⟩
        F.₁ g.f ∘ X.α ∘ t.p' ≈⟨ g-merges ⟩
        F.₁ g.f ∘ F.₁ t.p' ∘ β ≈˘⟨ pushˡ F.homomorphism ⟩
        F.₁ (g.f ∘ t.p') ∘ β
        ∎
      }
    module g∘p' = F-Coalgebra-Morphism g∘p'

    g∘p'-equation : h.f ≈ A,α.carrier-colim.proj i ∘ g∘p'.f
    g∘p'-equation =
      let open HomReasoning in
      begin
      h.f ≈⟨ t.commutes ⟩
      A,α.carrier-colim.proj t.x ∘ t.p' ≈˘⟨ pullˡ (A,α.colim.colimit-commute _) ⟩
      A,α.carrier-colim.proj i ∘ g.f ∘ t.p' ≡⟨⟩
      A,α.carrier-colim.proj i ∘ g∘p'.f
      ∎

-- if a coalgebra morphism h factors through a full diagram,
-- then h must match the projection
unique-proj-if-triangle : ∀ {i : A,α.𝒟.Obj} →
  Full-≈ A,α.D →
  (h : F-Coalgebras F [ A,α.D.₀ i , A,α.to-Coalgebra ]) →
  Triangle (F-Coalgebras F) A,α.colim h →
  F-Coalgebras F [ h ≈ A,α.colim.proj i ]
unique-proj-if-triangle {i} D-Full h t =
  -- we can reason on the level of 𝒞:
  begin
  h.f ≈⟨ t.commutes ⟩
  A,α.carrier-colim.proj t.x ∘ p'.f
   ≈˘⟨ refl⟩∘⟨ Dp≈p' ⟩
  A,α.carrier-colim.proj t.x ∘ (A,α.U∘D.₁ p)
   ≈⟨ A,α.carrier-colim.colimit-commute p ⟩
  A,α.carrier-colim.proj i
  ∎
  where
    module D-Full = Full-≈ D-Full
    module t = Triangle t
    B : F-Coalgebra F
    B = A,α.D.₀ i
    module B = F-Coalgebra B
    X : F-Coalgebra F
    X = A,α.D.₀ t.x
    module X = F-Coalgebra X
    p : A,α.𝒟 [ i , t.x ]
    p = D-Full.preimage i t.x t.p'
    p' : F-Coalgebra-Morphism B X
    p' = t.p'
    module p' = F-Coalgebra-Morphism p'
    module h = F-Coalgebra-Morphism h
    Dp≈p' : F-Coalgebras F [ A,α.D.₁ p ≈ p' ]
    Dp≈p' = D-Full.preimage-prop i t.x t.p'
    open Category 𝒞
    open HomReasoning

-- Given a coalgebra in the diagram of A,α , the injection/projection
-- is the unique coalgebra homomorphism to A,α if everything is finitary
-- and if the diagram is full:
unique-proj : ∀ {i : A,α.𝒟.Obj} →
  preserves-colimit (forget-Coalgebra ∘F A,α.D) F →
  Fil (CoalgColim.𝒟 A,α) →
  Full-≈ A,α.D →
  (h : F-Coalgebras F [ A,α.D.₀ i , A,α.to-Coalgebra ]) →
  F-Coalgebras F [ h ≈ A,α.colim.proj i ]
unique-proj {i} F-finitary 𝒟-Fil D-Full h =
  unique-proj-if-triangle D-Full h
    (hom-to-coalg-colim-triangle
      (FiniteRecursive.finite-carrier (A,α.all-have-prop {i}))
      F-finitary h 𝒟-Fil)

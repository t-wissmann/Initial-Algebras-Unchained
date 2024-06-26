{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Category.SubCategory
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Category.Slice
open import Categories.Functor.Slice as Sl
open import Categories.Functor.Construction.SubCategory
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Categories.Category.Construction.F-Coalgebras
open import Data.Product

open import Categories.Functor.Coalgebra

open import Filtered
open import Colimit-Lemmas
open import Iterate.ProofGlobals

-- Let (A,α) be locally finite. For every P → FA, we construct
-- a finite subcoalgebra of (FA,Fα).
module Iterate.DiagramScheme {o ℓ} {fil-level}
  {o' ℓ' : Level } -- Level for diagram schemes
  (Fil : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)  → Set fil-level) -- some variant of 'filtered'
  (proof-globals : ProofGlobals {o' = o'} {ℓ' = ℓ'} o ℓ Fil)
  where

open import Iterate.FiniteSubcoalgebra Fil proof-globals
open ProofGlobals proof-globals

-- the diagram scheme for the constructed CoalgColim
ℰ : Category _ _ _
ℰ = -- it is the full subcategory
    FullSubCategory
    -- of the slicecategory for FA, Fα
    (Slice (F-Coalgebras F) (iterate A,α))
    -- containing all commuting triangles ℰ₀ as objects
    {I = ℰ₀}
    λ t → sliceobj (CC.hom-to-FA t)
    -- Unfortunately, ℰ is not quite of the shape
    -- of Cat[_↓_] (from Canonical-Cocone), because:
    -- * Cat[_↓_] keeps the slice-arrow to F(A,α) as a separate member in
    --   the indes set
    -- * but for ℰ, the slice-arrow to F(A,α) is derived from
    --   the triangle 't'
module ℰ = Category ℰ

E : Functor ℰ (F-Coalgebras F)
E = Sl.Forgetful (F-Coalgebras F) ∘F FullSub (Slice (F-Coalgebras F) (iterate A,α))
module E = Functor E

FA,Fα-Cocone : Cocone E
FA,Fα-Cocone = record { coapex =
    record {
    ψ = CC.hom-to-FA ;
    commute = λ f → Slice⇒.△ f } }
module FA,Fα-Cocone = Cocone FA,Fα-Cocone

--
-- For triangles t1 t2, we can build an ℰ-hom t1 -> t2 provided that:
-- h1 : P₁ -> P₂+X₂ in 𝒞
-- h2 : i₁ -> i₂ in coalg-colim.𝒟 (i.e. the diagram of A,α)
-- satisfying:
--         P₁ --h1--> P₂+X₂
--         |            |
--         | p'         | [p',x]
--         v            v
--         FX₁--F h2-->FX₂
-- and
--         P₁  ---- p₁ ---> FA
--          |                ^
--          | h1             |
--          v                |
--         P₂+X₂  -----------'
--
build-ℰ-hom : (t1 t2 : ℰ₀)
                (h1 : CC.P t1 ⇒ CC.P+X.obj t2)
                (h2 : coalg-colim.𝒟 [ CC.X,x-dia t1 , CC.X,x-dia t2 ])
                → (CC.[p',x] t2 ∘ h1 ≈ F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ CC.p' t1)
                → (CC.p t1 ≈ CC.hom-to-FA.f t2 ∘ h1)
                → ℰ [ t1 , t2 ]
build-ℰ-hom t1 t2 h1 h2 h1-coalg-hom h1-slice =
    slicearr {h = record {
    f = f ;
    commutes = begin
        t2.Fi₂[p',x] ∘ t1.P+X.[ h1 , t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2) ]
            ≈⟨ assoc ○ (refl⟩∘⟨ first-square) ○ sym-assoc ⟩
        (F.₁ t2.P+X.i₂ ∘ F.₁ (V.₁ (coalg-colim.D.₁ h2))) ∘ t1.[p',x]
            ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩
        F.₁ (t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2)) ∘ t1.[p',x]
            ≈˘⟨ F.F-resp-≈ t1.P+X.inject₂ ⟩∘⟨refl ⟩
        F.₁ (f ∘ t1.P+X.i₂) ∘ t1.[p',x]
            ≈⟨ ((F.homomorphism ⟩∘⟨refl) ○ assoc) ⟩
        F.₁ f ∘ t1.Fi₂[p',x]
        ∎
    }} (coproduct-jointly-epic t1.P+X (record {
        case-precompose-i₁ =
        begin
        (t2.hom-to-FA.f ∘ f) ∘ t1.P+X.i₁
            ≈⟨ assoc ○ (refl⟩∘⟨ t1.P+X.inject₁) ⟩
        t2.hom-to-FA.f ∘ h1
            ≈˘⟨ h1-slice ⟩
        t1.p
            ≈⟨ t1.hom-to-FA-i₁ ⟩
        t1.hom-to-FA.f ∘ t1.P+X.i₁
        ∎
        ;
        case-precompose-i₂ =
        begin
        (t2.hom-to-FA.f ∘ f) ∘ t1.P+X.i₂
            ≈⟨ assoc ○ (refl⟩∘⟨ t1.P+X.inject₂) ⟩
        t2.hom-to-FA.f ∘ t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2)
            ≈⟨ sym-assoc ⟩
        (t2.hom-to-FA.f ∘ t2.P+X.i₂) ∘ V.₁ (coalg-colim.D.₁ h2)
            ≈˘⟨ sym-assoc ○ t2.hom-to-FA-i₂ ⟩∘⟨refl ⟩
        α ∘ t2.proj-X,x.f ∘ V.₁ (coalg-colim.D.₁ h2)
            ≈⟨ refl⟩∘⟨ coalg-colim.carrier-colim.colimit-commute h2 ⟩
        α ∘ t1.proj-X,x.f
            ≈⟨ t1.hom-to-FA-i₂ ⟩
        t1.hom-to-FA.f ∘ t1.P+X.i₂
        ∎
        }))
    where
    open HomReasoning
    module t1 = CC t1
    module t2 = CC t2
    f = t1.P+X.[ h1 , t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2) ]
    first-square : t2.[p',x] ∘ t1.P+X.[ h1 , t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2) ] ≈ F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ t1.[p',x]
    first-square = coproduct-jointly-epic t1.P+X
        (record {
        case-precompose-i₁ = begin
            (t2.[p',x] ∘ t1.P+X.[ h1 , t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2) ]) ∘ t1.P+X.i₁
            ≈⟨ assoc ○ (refl⟩∘⟨ t1.P+X.inject₁) ⟩
            t2.[p',x] ∘ h1
            ≈⟨ h1-coalg-hom ⟩
            F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ CC.p' t1
            ≈⟨ (refl⟩∘⟨ (⟺ t1.P+X.inject₁)) ○ sym-assoc ⟩
            (F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ t1.[p',x]) ∘ t1.P+X.i₁
            ∎ ;
        case-precompose-i₂ = begin
            (t2.[p',x] ∘ t1.P+X.[ h1 , t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2) ]) ∘ t1.P+X.i₂
            ≈⟨ assoc ○ (refl⟩∘⟨ t1.P+X.inject₂) ⟩
            t2.[p',x] ∘ t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ h2)
            ≈⟨ sym-assoc ○ (t2.P+X.inject₂ ⟩∘⟨refl ) ⟩
            t2.x ∘ V.₁ (coalg-colim.D.₁ h2)
            ≈⟨ F-Coalgebra-Morphism.commutes (coalg-colim.D.₁ h2) ⟩
            F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ t1.x
            ≈˘⟨ assoc ○ (refl⟩∘⟨ t1.P+X.inject₂) ⟩
            (F.₁ (V.₁ (coalg-colim.D.₁ h2)) ∘ t1.[p',x]) ∘ t1.P+X.i₂
            ∎
        })

-- build an ℰ-hom of shape id_P + h where h: i → j is a coalgebra morphism from the diagram 𝒟
coalg-hom-to-ℰ-hom : ∀ (P : 𝒞p/FA.Obj) (i j : Triangle F-coalg-colim (FA-colim.proj P))
                    (h : coalg-colim.𝒟 [ CC.X,x-dia (P , i) , CC.X,x-dia (P , j) ])
                    → CC.p' (P , j) ≈ F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ CC.p' (P , i)
                    → ℰ [ (P , i) , (P , j) ]
coalg-hom-to-ℰ-hom P i j h hom-preserves-p' =
    build-ℰ-hom (P , i) (P , j)
    t2.P+X.i₁ h hom-prop t2.hom-to-FA-i₁
    where
    module t1 = CC (P , i)
    module t2 = CC (P , j)
    open HomReasoning
    hom-prop = begin
        t2.[p',x] ∘ t2.P+X.i₁ ≈⟨ t2.P+X.inject₁ ⟩
        t2.p' ≈⟨ hom-preserves-p' ⟩
        F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ t1.p'
        ∎

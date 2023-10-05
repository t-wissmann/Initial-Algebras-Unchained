{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Category.Product
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory using (FullSub)
open import Categories.Functor using (Functor; Endofunctor)
open import Data.Product

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP
open import Filtered
open import Setoids-Choice
open import Unchained-Utils

-- intuitively:
-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ e fil-level}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (Fil : ∀ {o' ℓ' e' : Level} → Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category ℓ ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ Fil)
  where

module 𝒞 = Category 𝒞
open import recursive-coalgebra 𝒞 F
open import Hom-Colimit-Choice 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞

module F-Coalgebras = Category (F-Coalgebras F)

record FinitaryRecursive (coalg : F-Coalgebra F) : Set (o ⊔ suc ℓ ⊔ suc e ⊔ fil-level) where
  -- the property that a coalgebra
  field
    -- 1. has finite carrier
    finite-carrier : presented 𝒞 ℓ ℓ ℓ Fil (F-Coalgebra.A coalg)
    -- 2. is recursive
    is-recursive : IsRecursive coalg


module 𝒞-lfp = WeaklyLFP 𝒞-lfp
open import Prop-Coalgebra 𝒞 F FinitaryRecursive

-- Proof: whenever (A,α) is locally finite, then so is (FA,Fα).
-- We structure the proof as a module because it makes it easier
-- to globally fix a certian parameters along the way.
module IterationProof (coalg-colim : LProp-Coalgebra)
                      (𝒟-filtered : Fil (LProp-Coalgebra.𝒟 coalg-colim))
                      -- ^- coalg is a colimit of a filtered diagram
                      (F-preserves-colim : preserves-colimit (LProp-Coalgebra.carrier-diagram coalg-colim) F)
                      -- ^- F preserves the colimit 'coalg'
                      (has-coprod : HasCoproductOfPresentedObjects 𝒞 ℓ ℓ ℓ Fil)
                      -- we have sufficiently many coproducts
                      where
    Fil-presented = presented 𝒞 ℓ ℓ ℓ Fil
    -- the provided coalgebra:
    module coalg-colim = LProp-Coalgebra coalg-colim
    A,α = coalg-colim.to-Coalgebra
    open F-Coalgebra A,α
    -- ^- this brings A and α into scope
    open Functor F
    open Category 𝒞
    -- ^ we only reason in 𝒞

    module F = Functor F

    -- We show that (FA,Fα) is a colimit by taking the
    -- diagram scheme from the fact that FA is a colimit of
    -- finite objects. These finite objects form the following
    -- slice category:

    𝒟 = 𝒞-lfp.canonical-diagram-scheme (F₀ A)
    module 𝒟 = Category 𝒟
    D = 𝒞-lfp.canonical-diagram (F₀ A)
    module D = Functor D
    FA-colim : Colimit D
    FA-colim = 𝒞-lfp.canonical-colimit (F₀ A)
    module FA-colim = Colimit FA-colim


    -- -- At the same time, F(A,α) is a colimit of coalgebras, which
    -- -- is preserved by F:
    F-coalg-colim = Colimit-from-prop (F-preserves-colim coalg-colim.carrier-colim)
    module F-coalg-colim = Colimit F-coalg-colim

    -- the new diagram: commuting triangles of objects P in the colimit
    -- of FA such that P factors through some coalgebra-colimit injection:
    --
    --          P  -----> Carrier( F(A,α) )
    --          |                     ^
    --          |                     |
    --          |                     |
    --          '-------> Carrier( F(X,x) )
    all-triangles =
      Σ[ P ∈ 𝒟.Obj ]
      Triangle F-coalg-colim (FA-colim.proj P)

    -- in fact, every P can be extended to such a triangle:
    P-to-triangle : 𝒟.Obj → all-triangles
    P-to-triangle P =
      let
        (idx , _) = P
        DP-preserves-colim =
          𝒞-lfp.fin-presented
            idx
            coalg-colim.𝒟 -- the diagram scheme
            𝒟-filtered    -- ... which is filtered
            (F ∘F coalg-colim.carrier-diagram)
      in
      P ,
      hom-colim-choice F-coalg-colim (D.₀ P)
        DP-preserves-colim
        (FA-colim.proj P)

    -- In the following, we construct a presented coalgebra
    -- "below" (FA,Fα).
    -- The construction uses multiple components, all parametric
    -- in such a triangle, whihc we now fix globally:
    module ConstructionComponents (t : all-triangles) where
      -- The first ingredient is the 'intermediate' coalgebra through which
      -- the triangle factors:
      X,x : F-Coalgebra F
      X,x = coalg-colim.D.₀ (Triangle.x (proj₂ t))

      proj-X,x : F-Coalgebra-Morphism X,x A,α
      proj-X,x = coalg-colim.colim.proj (Triangle.x (proj₂ t))
      module proj-X,x = F-Coalgebra-Morphism proj-X,x

      -- We also introduce names for the carrier and the structure:
      X = F-Coalgebra.A X,x
      x = F-Coalgebra.α X,x

      P : 𝒞.Obj
      P = D.₀ (proj₁ t)

      p : P ⇒ F.₀ A
      p = FA-colim.proj (proj₁ t)

      P-is-presented : Fil-presented P
      P-is-presented =
        -- here, we need to unfold the definition of P as a sliceobj
        -- from the index of a presented object
        let (idx , _) = (proj₁ t) in
        𝒞-lfp.fin-presented idx

      X-is-presented : Fil-presented X
      X-is-presented = FinitaryRecursive.finite-carrier coalg-colim.all-have-prop

      X,x-is-recursive : IsRecursive X,x
      X,x-is-recursive = FinitaryRecursive.is-recursive coalg-colim.all-have-prop

      -- the constructed coalgebra has a coproduct as its carrier
      P+X : Coproduct P X
      P+X = has-coprod P X P-is-presented X-is-presented
      module P+X = Coproduct P+X renaming (A+B to obj)

      p' : P ⇒ F.₀ X
      p' = Triangle.p' (proj₂ t)


      -- the structure of the constructed coalgebra:
      Fi₂[p',x] : P+X.obj ⇒ F.₀ P+X.obj
      Fi₂[p',x] = F.₁ P+X.i₂ ∘ P+X.[ p' , x ]

      -- the combined constructed coalgebra
      P+X-coalg : F-Coalgebra F
      P+X-coalg = record { A = P+X.obj ; α = Fi₂[p',x] }

      -- The constructed coalgebra sits nicely between X,x and FX,Fx
      -- as we will see now:
      hom-from-X : F-Coalgebra-Morphism X,x P+X-coalg
      hom-from-X =
        let open HomReasoning in
        record { f = P+X.i₂ ;
        commutes = begin
          Fi₂[p',x] ∘ P+X.i₂ ≈⟨ assoc ⟩
          F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ refl⟩∘⟨ P+X.inject₂ ⟩
          F.₁ P+X.i₂ ∘ x
          ∎}
      module hom-from-X = F-Coalgebra-Morphism hom-from-X

      hom-to-FX : F-Coalgebra-Morphism P+X-coalg (iterate X,x)
      hom-to-FX =
        let open HomReasoning in
        record { f = P+X.[ p' , x ] ;
        commutes = begin
          F.₁ x ∘ P+X.[ p' , x ] ≈˘⟨ F.F-resp-≈ P+X.inject₂ ⟩∘⟨refl ⟩
          F.₁ (P+X.[ p' , x ] ∘ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
          (F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ assoc ⟩
          F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ≡⟨⟩
          F.₁ P+X.[ p' , x ] ∘ Fi₂[p',x]
          ∎}
      module hom-to-FX = F-Coalgebra-Morphism hom-to-FX

      hom-to-FA : F-Coalgebra-Morphism P+X-coalg (iterate A,α)
      hom-to-FA = (iterate-F-Coalgebra-Morphism proj-X,x) F-Coalgebras.∘ hom-to-FX
      module hom-to-FA = F-Coalgebra-Morphism hom-to-FA

      --   The property that all objects in the diagram ...
      P+X-coalg-is-FinitaryRecursive : FinitaryRecursive P+X-coalg
      P+X-coalg-is-FinitaryRecursive =
        record {
          -- 1. .. have presented carrier
          finite-carrier =
            presented-coproduct 𝒞 ℓ ℓ ℓ Fil
              Fil-to-filtered
              P+X P-is-presented X-is-presented ;
          -- 2. .. are recursive:
          is-recursive =
            -- for recursiveness, we use our formalization of ([CUV06, Prop. 5])
            sandwich-recursive _ _ X,x-is-recursive hom-from-X hom-to-FX
              (let open HomReasoning in begin
              Fi₂[p',x] ≡⟨⟩ F.₁ hom-from-X.f ∘ hom-to-FX.f
              ∎)
          }


    -- the triangles form a subcategory of coalgebras:
    tri-subcat : SubCat (F-Coalgebras F) all-triangles
    tri-subcat =
      let
        open ConstructionComponents
        open HomReasoning
        morph t1 t2 s h =
           P+X.[_,_] t1
             (P+X.i₁ t2 ∘ D.₁ s)
             (P+X.i₂ t2 ∘ F-Coalgebra-Morphism.f (coalg-colim.D.₁ h))
      in
      record {
        U = P+X-coalg ;
        R = λ {t1} {t2} s+h →
          let
            module s+h = F-Coalgebra-Morphism s+h
            P1 , T1 = t1
            module T1 = Triangle T1
            P2 , T2 = t2
            module T2 = Triangle T2
          in
          Σ[ s ∈ (P1 𝒟.⇒ P2) ]
          Σ[ h ∈ (T1.x coalg-colim.𝒟.⇒ T2.x) ]
            (s+h.f ≈ morph t1 t2 s h)
            ;
          Rid = λ {t} → 𝒟.id , coalg-colim.𝒟.id , (
            coproduct-jointly-epic {p = P+X t}
              (begin
              id ∘ P+X.i₁ t ≈˘⟨ id-comm ⟩
              (P+X.i₁ t ∘ id)
                ≈˘⟨ refl⟩∘⟨ D.identity {proj₁ t}⟩
              (P+X.i₁ t ∘ D.₁ (𝒟.id {proj₁ t}))
                ≈˘⟨ P+X.inject₁ t ⟩
              _ -- morph t t 𝒟.id coalg-colim.𝒟.id ∘ P+X.i₁ t
              ∎)
              (begin
              id ∘ P+X.i₂ t ≈˘⟨ id-comm ⟩
              P+X.i₂ t ∘ id ≈˘⟨ refl⟩∘⟨ coalg-colim.D.identity ⟩
              P+X.i₂ t ∘ F-Coalgebra-Morphism.f (coalg-colim.D.₁ coalg-colim.𝒟.id) ≈˘⟨ P+X.inject₂ t ⟩
              morph t t 𝒟.id coalg-colim.𝒟.id ∘ P+X.i₂ t
              ∎)
            -- (begin
            -- id ≈˘⟨ {!P+X.η t!} ⟩
            --   P+X.[_,_] t
            -- ≈˘⟨ ? t!} ⟩
            --   P+X.[_,_] t
            --     (P+X.i₁ t ∘ D.₁ 𝒟.id)
            --     (P+X.i₂ t ∘ F-Coalgebra-Morphism.f (coalg-colim.D.₁ coalg-colim.𝒟.id))
            -- ∎)
            -- (begin
            -- id ∘ (P+X.i₁ t) ≈⟨ id-comm-sym ⟩
            -- (P+X.i₁ t) ∘ id ≈˘⟨ refl⟩∘⟨ D.identity ⟩
            -- (P+X.i₁ t) ∘ D.₁ 𝒟.id
            -- ∎)
            -- ,
            -- (begin
            -- id ∘ (P+X.i₂ t) ≈⟨ id-comm-sym ⟩
            -- (P+X.i₂ t) ∘ id ≈˘⟨ refl⟩∘⟨ coalg-colim.D.identity ⟩
            -- (P+X.i₂ t) ∘ (F-Coalgebra-Morphism.f (coalg-colim.D.₁ coalg-colim.𝒟.id))
            -- ∎)
            )
            ;
          _∘R_ = {!!} }

    -- 𝒮 = coalg-colim.𝒟
    -- S : Functor 𝒮 (F-Coalgebras F)
    -- S = coalg-colim.D
    -- 𝒟×𝒮 = (Product 𝒟 𝒮)
    -- module 𝒟×𝒮 = Category 𝒟×𝒮
    -- -- The diagram scheme is essentially
    -- ℰ : Category _ _ _
    -- ℰ = FullSubCategory 𝒟×𝒮 fam
    --     where
    --       fam : all-triangles → 𝒟×𝒮.Obj
    --       fam = (λ (P , T) → P , (Triangle.x T)) -- {!λ {P , T} → P , Triangle.x T!} -- ConstructionComponents.P+X-coalg
    -- E : Functor ℰ (F-Coalgebras F)
    -- E = ∘F FullSub 𝒟×𝒮
    -- module E = Functor F

    -- -- since we have 'P' as one of the ingredients, we have a cocone:
    -- FA,Fα-Cocone : Cocone E
    -- FA,Fα-Cocone =
    --   record {
    --     N = iterate A,α ;
    --     coapex = record {
    --       ψ = ConstructionComponents.hom-to-FA ;
    --       commute = λ {t} {t'} h →
    --         let
    --           open HomReasoning
    --           open ConstructionComponents
    --           module h = F-Coalgebra-Morphism h
    --         in
    --         begin
    --         hom-to-FA.f t' ∘ h.f ≈⟨ {!!} ⟩
    --         hom-to-FA.f t
    --         ∎
    --       }
    --   }
    -- module FA,Fα-Cocone = Cocone FA,Fα-Cocone

    -- iterated-LProp-Coalgebra : LProp-Coalgebra
    -- iterated-LProp-Coalgebra = record {
    --   -- the diagram for (FA,Fα)
    --   𝒟 = ℰ ;
    --   D = E ;
    --   all-have-prop = λ {t} →
    --     ConstructionComponents.P+X-coalg-is-FinitaryRecursive t;
    --   carrier-colim = ?
    --   }

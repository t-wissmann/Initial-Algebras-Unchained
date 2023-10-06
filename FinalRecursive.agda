{-# OPTIONS --without-K  --lossy-unification --allow-unsolved-metas #-}
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
open import Categories.Functor.Construction.SubCategory
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
open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F}

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
    -- in the proof, let V be the forgetful functor from coalgebras to 𝒞
    module V = Functor forget-Coalgebra
    Fil-presented = presented 𝒞 ℓ ℓ ℓ Fil
    open LiftHom ℓ ℓ ℓ
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

    -- In fact, every P can be extended to such a triangle, because
    -- D P is presented and so it preserves the filtered colimit of the
    -- coalgebra-colimit under (the postcomposition of) F:
    DP-preserves-coalg-colim : ∀ (P : 𝒟.Obj) →
      preserves-colimit
        (F ∘F coalg-colim.carrier-diagram)
        LiftHom[ D.₀ P ,-]
    DP-preserves-coalg-colim P =
      let (idx , _) = P in
          𝒞-lfp.fin-presented
            idx
            coalg-colim.𝒟 -- the diagram scheme
            𝒟-filtered    -- ... which is filtered
            (F ∘F coalg-colim.carrier-diagram)

    -- And so we obtain a triangle for each P:
    P-to-triangle : 𝒟.Obj → all-triangles
    P-to-triangle P = P ,
      hom-colim-choice F-coalg-colim (D.₀ P)
        (DP-preserves-coalg-colim P)
        (FA-colim.proj P)

    -- In the following, we construct a presented coalgebra
    -- "below" (FA,Fα).
    -- The construction uses multiple components, all parametric
    -- in such a triangle, which we now fix globally:
    module ConstructionComponents (t : all-triangles) where
      -- The first ingredient is the 'intermediate' coalgebra through which
      -- the triangle factors:
      X,x-dia : coalg-colim.𝒟.Obj -- the underlying object in the diagram scheme
      X,x-dia = Triangle.x (proj₂ t)
      X,x : F-Coalgebra F
      X,x = coalg-colim.D.₀ X,x-dia

      proj-X,x : F-Coalgebra-Morphism X,x A,α
      proj-X,x = coalg-colim.colim.proj (Triangle.x (proj₂ t))
      module proj-X,x = F-Coalgebra-Morphism proj-X,x

      -- We also introduce names for the carrier and the structure:
      open F-Coalgebra X,x renaming (A to X; α to x) public

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

      triangle-commutes : p ≈ F.₁ proj-X,x.f ∘ p'
      triangle-commutes = Triangle.commutes (proj₂ t)

      -- This p' is essentially unique in the sense that if there is another
      -- suitable p'', then p' and p'' are identified somewhere in the diagram
      p'-unique : ∀ (p'' : P ⇒ F.₀ X) → p ≈ F.₁ proj-X,x.f ∘ p'' →
        Σ[ Y,y-dia ∈ coalg-colim.𝒟.Obj ]
        Σ[ h ∈ coalg-colim.𝒟 [ X,x-dia , Y,y-dia ] ]
        F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ p' ≈ F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ p''
      p'-unique p'' p''-commutes =
        let open HomReasoning in
        coequalize-colimit-factorization
          F-coalg-colim
          P
          (Fil-to-filtered 𝒟-filtered)
          (hom-colim-unique-factor
              F-coalg-colim
              (Fil-to-filtered 𝒟-filtered)
              P
              (DP-preserves-coalg-colim
                (proj₁ t) F-coalg-colim))
          p' p''
          (begin
            F.₁ proj-X,x.f ∘ p'   ≈˘⟨ triangle-commutes ⟩
            p                     ≈⟨ p''-commutes ⟩
            F.₁ proj-X,x.f ∘ p''
            ∎)


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

      hom-to-FA-i₁ : p ≈ hom-to-FA.f ∘ P+X.i₁
      hom-to-FA-i₁ =
        let open HomReasoning in
        begin
        p ≈⟨ triangle-commutes ⟩
        F.₁ proj-X,x.f ∘ p' ≈˘⟨ refl⟩∘⟨ P+X.inject₁ ⟩
        F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₁ ≈⟨ sym-assoc ⟩
        (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₁ ≡⟨⟩
        hom-to-FA.f ∘ P+X.i₁
        ∎

      hom-to-FA-i₂ : α ∘ proj-X,x.f ≈ hom-to-FA.f ∘ P+X.i₂
      hom-to-FA-i₂ =
        let open HomReasoning in
        begin
        α ∘ proj-X,x.f ≈⟨ proj-X,x.commutes ⟩
        F.₁ proj-X,x.f ∘ x ≈˘⟨ refl⟩∘⟨ P+X.inject₂ ⟩
        F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ sym-assoc ⟩
        (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₂ ≡⟨⟩
        hom-to-FA.f ∘ P+X.i₂
        ∎

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


    tri-subcat : SubCat (Product 𝒟 coalg-colim.𝒟) all-triangles
    tri-subcat =
      let
        open ConstructionComponents
        open HomReasoning
      in
      record {
        U = λ {(P , T) → P , Triangle.x T };
        R = λ {t1} {t2} → λ {(s , h) →
          -- morphisms are commuting squares:
          let
            module t1 = Triangle (proj₂ t1)
            module t2 = Triangle (proj₂ t2)
          in
          t2.p' ∘ D.₁ s ≈ F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ t1.p'
        };
        Rid = λ {t} → begin
          Triangle.p' (proj₂ t) ∘ D.₁ (𝒟.id {proj₁ t}) ≈⟨ refl⟩∘⟨ D.identity {proj₁ t} ⟩
          Triangle.p' (proj₂ t) ∘ id ≈⟨ id-comm ⟩
          id ∘ Triangle.p' (proj₂ t) ≈˘⟨ F.identity ⟩∘⟨refl ⟩
          F.₁ id ∘ Triangle.p' (proj₂ t) ≈˘⟨ F.F-resp-≈ coalg-colim.D.identity ⟩∘⟨refl  ⟩
          F.₁ (V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id)) ∘ Triangle.p' (proj₂ t)
        ∎;
        _∘R_ = λ {t1} {t2} {t3} {r,g} {s,h} →
               λ r,g-prop s,h-prop →
               let
                 r , g = r,g
                 s , h = s,h
                 module t1 = Triangle (proj₂ t1)
                 module t2 = Triangle (proj₂ t2)
                 module t3 = Triangle (proj₂ t3)
               in
               begin
               t3.p' ∘ D.₁ (r 𝒟.∘ s) ≈⟨ refl⟩∘⟨ D.homomorphism {_} {_} {_} {s} {r} ⟩
               t3.p' ∘ D.₁ r ∘ D.₁ s ≈⟨ sym-assoc ⟩
               (t3.p' ∘ D.₁ r) ∘ D.₁ s ≈⟨ r,g-prop ⟩∘⟨refl ⟩
               (F.₁ (V.₁ (coalg-colim.D.₁ g)) ∘ t2.p') ∘ D.₁ s ≈⟨ assoc ⟩
               F.₁ (V.₁ (coalg-colim.D.₁ g)) ∘ (t2.p' ∘ D.₁ s) ≈⟨ refl⟩∘⟨ s,h-prop ⟩
               F.₁ (V.₁ (coalg-colim.D.₁ g)) ∘ (F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ t1.p')
                 ≈⟨ sym-assoc ⟩
               (F.₁ (V.₁ (coalg-colim.D.₁ g)) ∘ F.₁ (V.₁ (coalg-colim.D.₁ h))) ∘ t1.p'
                 ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩
               F.₁ (V.₁ (coalg-colim.D.₁ g) ∘ (V.₁ (coalg-colim.D.₁ h))) ∘ t1.p'
                 ≈˘⟨ F.F-resp-≈ (coalg-colim.D.homomorphism {_} {_} {_} {h} {g}) ⟩∘⟨refl ⟩
               F.₁ (V.₁ (coalg-colim.D.₁ (g coalg-colim.𝒟.∘ h))) ∘ t1.p'
               ∎
      }
    -- so we have the following diagram:
    𝒮 : Category _ _ _
    𝒮 = SubCategory (Product 𝒟 coalg-colim.𝒟) tri-subcat
    module 𝒮 = Category 𝒮

    S : Functor 𝒮 (F-Coalgebras F)
    S =
      let
        open ConstructionComponents
        open HomReasoning
        -- we turn the following mapping to a functor:
        S₁ t1 t2 s h = P+X.[_,_] t1 (P+X.i₁ t2 ∘ D.₁ s) (P+X.i₂ t2 ∘ (V.₁ (coalg-colim.D.₁ h)))
      in
      record
         { F₀ = λ t → P+X-coalg t
         ; F₁ = λ {t1} {t2} → λ {((s , h), s,h-prop) →
           let
             Ds =(D.₁ s)
             Vh = (V.₁ (coalg-colim.D.₁ h))
             FVh = F.₁ Vh
             -- s+h = P+X.[_,_] t1 (P+X.i₁ t2 ∘ Ds) (P+X.i₂ t2 ∘ Vh)
             s+h = S₁ t1 t2 s h
           in
           record {
             f = s+h ;
             commutes = coproduct-jointly-epic (P+X t1) record {
               case-precompose-i₁ =
                      begin
                      (Fi₂[p',x] t2 ∘ s+h) ∘ P+X.i₁ t1 ≈⟨ assoc ⟩
                      Fi₂[p',x] t2 ∘ s+h ∘ P+X.i₁ t1 ≈⟨ refl⟩∘⟨ P+X.inject₁ t1 ⟩
                      (F.₁ (P+X.i₂ t2) ∘ P+X.[_,_] t2 (p' t2) (x t2)) ∘ P+X.i₁ t2 ∘ Ds ≈⟨ assoc ○ (refl⟩∘⟨ sym-assoc) ⟩
                      F.₁ (P+X.i₂ t2) ∘ (P+X.[_,_] t2 (p' t2) (x t2) ∘ P+X.i₁ t2) ∘ Ds ≈⟨ refl⟩∘⟨ P+X.inject₁ t2 ⟩∘⟨refl ⟩
                      F.₁ (P+X.i₂ t2) ∘ (p' t2) ∘ Ds ≈⟨ refl⟩∘⟨ s,h-prop ⟩
                      F.₁ (P+X.i₂ t2) ∘ (F.₁ Vh) ∘ (p' t1)  ≈˘⟨ (F.homomorphism ⟩∘⟨refl) ○ assoc ⟩
                      (F.₁ (P+X.i₂ t2 ∘ Vh)) ∘ (p' t1)  ≈˘⟨ F.F-resp-≈ (P+X.inject₂ t1)  ⟩∘⟨refl ⟩
                      (F.₁ (s+h ∘ P+X.i₂ t1)) ∘ (p' t1)  ≈⟨ F.homomorphism ⟩∘⟨ (⟺ (P+X.inject₁ t1)) ⟩
                      (F.₁ s+h ∘ F.₁ (P+X.i₂ t1)) ∘ (P+X.[_,_] t1 (p' t1) (x t1) ∘ P+X.i₁ t1) ≈⟨ sym-assoc ○ (assoc ⟩∘⟨refl) ⟩
                      (F.₁ s+h ∘ (F.₁ (P+X.i₂ t1) ∘ P+X.[_,_] t1 (p' t1) (x t1) )) ∘ P+X.i₁ t1 ≡⟨⟩
                      (F.₁ s+h ∘ Fi₂[p',x] t1) ∘ P+X.i₁ t1
                      ∎
               ;
               case-precompose-i₂ =
                      begin
                      (Fi₂[p',x] t2 ∘ s+h) ∘ P+X.i₂ t1 ≈⟨ assoc ○ (refl⟩∘⟨ P+X.inject₂ t1) ⟩
                      Fi₂[p',x] t2 ∘ (P+X.i₂ t2 ∘ Vh) ≈⟨ sym-assoc ⟩
                      (Fi₂[p',x] t2 ∘ P+X.i₂ t2) ∘ Vh ≈⟨ assoc ⟩∘⟨refl ⟩
                      (F.₁ (P+X.i₂ t2) ∘ (_ ∘ P+X.i₂ t2)) ∘ Vh ≈⟨ (refl⟩∘⟨ P+X.inject₂ t2) ⟩∘⟨refl ⟩
                      (F.₁ (P+X.i₂ t2) ∘ x t2) ∘ Vh ≈⟨ assoc ⟩
                      F.₁ (P+X.i₂ t2) ∘ (x t2 ∘ Vh) ≈⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (coalg-colim.D.₁ h) ⟩
                      F.₁ (P+X.i₂ t2) ∘ (F.₁ Vh ∘ x t1) ≈⟨ sym-assoc ⟩
                      (F.₁ (P+X.i₂ t2) ∘ F.₁ Vh) ∘ x t1 ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩
                      (F.₁ (P+X.i₂ t2 ∘ Vh)) ∘ x t1 ≈˘⟨ F.F-resp-≈ (P+X.inject₂ t1) ⟩∘⟨refl ⟩
                      (F.₁ (s+h ∘ _)) ∘ x t1 ≈⟨ F.homomorphism ⟩∘⟨ (⟺ (P+X.inject₂ t1)) ⟩
                      (F.₁ s+h ∘ _) ∘ (_ ∘ P+X.i₂ t1) ≈⟨ sym-assoc ○ (assoc ⟩∘⟨refl) ⟩
                      (F.₁ s+h ∘ Fi₂[p',x] t1) ∘ P+X.i₂ t1
                      ∎
               }
           }}
         ; identity = λ {t} →
                coproduct-jointly-epic (P+X t)
                  record {
                    case-precompose-i₁ =
                      begin
                      S₁ t t 𝒟.id coalg-colim.𝒟.id ∘ P+X.i₁ t
                        ≈⟨ P+X.inject₁ t ⟩
                      (P+X.i₁ t ∘ D.₁ (𝒟.id {proj₁ t}))
                        ≈⟨ refl⟩∘⟨ D.identity {proj₁ t}⟩
                      (P+X.i₁ t ∘ id)
                        ≈⟨ id-comm ⟩
                      id ∘ P+X.i₁ t
                      ∎ ;
                    case-precompose-i₂ =
                      begin
                      S₁ t t 𝒟.id coalg-colim.𝒟.id ∘ P+X.i₂ t
                        ≈⟨ P+X.inject₂ t ⟩
                      P+X.i₂ t ∘ V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id)
                        ≈⟨ refl⟩∘⟨ coalg-colim.D.identity ⟩
                      P+X.i₂ t ∘ id
                        ≈⟨ id-comm ⟩
                      id ∘ P+X.i₂ t
                      ∎
                  }
         ; homomorphism = λ {t1} {t2} {t3} {s,h-triple} {r,g-triple} →
                let
                  ((s , h), s,h-prop) = s,h-triple
                  ((r , g), r,g-prop) = r,g-triple
                  s+h = S₁ t1 t2 s h
                  r+g = S₁ t2 t3 r g
                in
                ⟺ (coproduct-jointly-epic (P+X t1) (record {
                  case-precompose-i₁ =
                    begin
                    (r+g ∘ s+h) ∘ P+X.i₁ t1        ≈⟨ assoc ⟩
                    r+g ∘ (s+h ∘ P+X.i₁ t1)         ≈⟨ refl⟩∘⟨ P+X.inject₁ t1 ⟩
                    r+g ∘ (P+X.i₁ t2 ∘ D.₁ s)        ≈˘⟨ assoc ⟩
                    (r+g ∘ P+X.i₁ t2) ∘ D.₁ s         ≈⟨ P+X.inject₁ t2 ⟩∘⟨refl ⟩
                    (P+X.i₁ t3 ∘ D.₁ r) ∘ D.₁ s        ≈⟨ assoc ⟩
                    P+X.i₁ t3 ∘ (D.₁ r ∘ D.₁ s)
                      ≈˘⟨ refl⟩∘⟨ D.homomorphism {_} {_} {_} {s} {r} ⟩
                      -- ^-- TODO: why can't r and s be inferred?
                    P+X.i₁ t3 ∘ D.₁ (r 𝒟.∘  s)        ≈˘⟨ P+X.inject₁ t1 ⟩
                    _ ∘ P+X.i₁ t1
                    ∎
                  ;
                  case-precompose-i₂ =
                    begin
                    -- the second case has the same pattern:
                    (r+g ∘ s+h) ∘ P+X.i₂ t1        ≈⟨ assoc ⟩
                    r+g ∘ (s+h ∘ P+X.i₂ t1)         ≈⟨ refl⟩∘⟨ P+X.inject₂ t1 ⟩
                    r+g ∘ (P+X.i₂ t2 ∘ _)        ≈˘⟨ assoc ⟩
                    (r+g ∘ P+X.i₂ t2) ∘ _         ≈⟨ P+X.inject₂ t2 ⟩∘⟨refl ⟩
                    (P+X.i₂ t3 ∘ _) ∘ _        ≈⟨ assoc ⟩
                    -- and from here on, it differs a bit in one step:
                    P+X.i₂ t3 ∘ (V.₁ (coalg-colim.D.₁ g) ∘ V.₁ (coalg-colim.D.₁ h)) ≈˘⟨ refl⟩∘⟨ coalg-colim.D.homomorphism ⟩
                    P+X.i₂ t3 ∘ (V.₁ (coalg-colim.D.₁ (g coalg-colim.𝒟.∘ h)))    ≈˘⟨ P+X.inject₂ t1 ⟩
                    _ ∘ P+X.i₂ t1
                    ∎
                  }))
         ; F-resp-≈ = λ { {P1 , T1} {P2 , T2} {(s , h), s,h-prop} {(r , g), r,g-prop} (s≈r , h≈g) →
           let
             module T1 = Triangle T1
             module T2 = Triangle T2
           in
           P+X.[]-cong₂ (P1 , T1)
             (refl⟩∘⟨ D.F-resp-≈ {P1} {P2} {s} {r} s≈r)
             (refl⟩∘⟨ V.F-resp-≈ {_} {_} {coalg-colim.D.₁ h} {coalg-colim.D.₁ g}
               (coalg-colim.D.F-resp-≈ {T1.x} {T2.x} {h} {g} h≈g))
           }
         }
    module S = Functor S

    -- since we have 'P' as one of the ingredients, we have a cocone:
    FA,Fα-Cocone : Cocone S
    FA,Fα-Cocone =
      let
        open ConstructionComponents
        open HomReasoning
      in
      record {
        N = iterate A,α ;
        coapex = record {
          ψ = hom-to-FA ;
          commute = λ {t1} {t2} ((s , h) , s+h-prop) →
             let
               open HomReasoning
               open ConstructionComponents

               s+h = P+X.[_,_] t1 (P+X.i₁ t2 ∘ D.₁ s) (P+X.i₂ t2 ∘ (V.₁ (coalg-colim.D.₁ h)))
             in
             coproduct-jointly-epic (P+X t1) record {
               case-precompose-i₁ =
                 begin
                 (hom-to-FA.f t2 ∘ s+h) ∘ P+X.i₁ t1 ≈⟨ assoc ⟩
                 hom-to-FA.f t2 ∘ (s+h ∘ P+X.i₁ t1) ≈⟨ refl⟩∘⟨ P+X.inject₁ t1 ⟩
                 hom-to-FA.f t2 ∘ (P+X.i₁ t2 ∘ D.₁ s) ≈⟨ sym-assoc ⟩
                 (hom-to-FA.f t2 ∘ P+X.i₁ t2) ∘ D.₁ s ≈˘⟨ hom-to-FA-i₁ t2 ⟩∘⟨refl ⟩
                 p t2 ∘ D.₁ s ≈⟨ FA-colim.colimit-commute s ⟩
                 p t1 ≈⟨ hom-to-FA-i₁ t1 ⟩
                 hom-to-FA.f t1 ∘ P+X.i₁ t1
                 ∎
                 ;
               case-precompose-i₂ =
                 begin
                 (hom-to-FA.f t2 ∘ s+h) ∘ P+X.i₂ t1 ≈⟨ assoc ⟩
                 hom-to-FA.f t2 ∘ (s+h ∘ P+X.i₂ t1) ≈⟨ refl⟩∘⟨ P+X.inject₂ t1 ⟩
                 hom-to-FA.f t2 ∘ (P+X.i₂ t2 ∘ V.₁ (coalg-colim.D.₁ h)) ≈˘⟨ assoc ⟩
                 (hom-to-FA.f t2 ∘ P+X.i₂ t2) ∘ V.₁ (coalg-colim.D.₁ h) ≈˘⟨ hom-to-FA-i₂ t2 ⟩∘⟨refl  ⟩
                 (α ∘ proj-X,x.f t2) ∘ V.₁ (coalg-colim.D.₁ h) ≈⟨ assoc ⟩
                 α ∘ (proj-X,x.f t2 ∘ V.₁ (coalg-colim.D.₁ h)) ≈⟨ refl⟩∘⟨ coalg-colim.colim.colimit-commute h ⟩
                 α ∘ proj-X,x.f t1 ≈⟨ hom-to-FA-i₂ t1 ⟩
                 hom-to-FA.f t1 ∘ P+X.i₂ t1
                 ∎
               }
          }
      }
    module FA,Fα-Cocone = Cocone FA,Fα-Cocone

    -- every cocone for the diagram S of coalgebras induces
    -- are cocone for the canonical diagram of F.₀ A
    Coalg-Cocone-to-Object-Cocone : Cocone S → Cocone D
    Coalg-Cocone-to-Object-Cocone B =
      let
        module B = Cocone B
        module bounds = has-upper-bounds (filtered.bounds (Fil-to-filtered 𝒟-filtered))
        open ConstructionComponents
        open HomReasoning
        V₁ = F-Coalgebra-Morphism.f {C = 𝒞} {F = F}
      in
      record {
        -- The tip of the cocone is just the carrier of the tip of B:
        N = F-Coalgebra.A B.N ;
        coapex =
          record {
            ψ = λ P →
              let t = P-to-triangle P in
              V.₁ (B.ψ t) ∘ P+X.i₁ t ;
            commute = λ {P1} {P2} s →
              let
                -- We get triangles for both P1 and P2
                t1 = P-to-triangle P1
                t2 = P-to-triangle P2
                module t1 = Triangle (proj₂ t1)
                module t2 = Triangle (proj₂ t2)
                -- by s : P1 ⇒ P2, P1 also factors through P2
                from-P1-through-t2 = begin
                    FA-colim.proj P1 ≈˘⟨ FA-colim.colimit-commute s ⟩
                    FA-colim.proj P2 ∘ D.₁ s    ≈⟨ t2.commutes ⟩∘⟨refl ⟩
                    (F-coalg-colim.proj t2.x ∘ t2.p') ∘ D.₁ s    ≈⟨ assoc ⟩
                    F-coalg-colim.proj t2.x ∘ t2.p' ∘ D.₁ s
                  ∎
                -- We can take the upper bounds of the two triangles:
                y = bounds.construct-upper-bound t1.x t2.x
                module y = UpperBound y
                t12 : all-triangles
                t12 = P1 , record {
                  x = y.obj ;
                  p' = F.₁ (V.₁ (coalg-colim.D.₁ y.i₁)) ∘ t1.p' ;
                  commutes = begin
                      FA-colim.proj P1 ≈⟨ t1.commutes ⟩
                      F-coalg-colim.proj t1.x ∘ t1.p' ≈˘⟨ F-coalg-colim.colimit-commute _ ⟩∘⟨refl ⟩
                      (F-coalg-colim.proj y.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁ y.i₁))) ∘ t1.p' ≈⟨ assoc ⟩
                      F-coalg-colim.proj y.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁ y.i₁)) ∘ t1.p'
                      ∎
                  }
                module t12 = Triangle (proj₂ t12)
                -- But there is a pointing other than t12.p', namely via t2.p'!
                p'' = F.₁ (V.₁ (coalg-colim.D.₁ y.i₂)) ∘ t2.p' ∘ D.₁ s
                p''-through-t12 : FA-colim.proj P1 ≈ F-coalg-colim.proj y.obj ∘ p''
                p''-through-t12 = begin
                  FA-colim.proj P1 ≈⟨ from-P1-through-t2 ⟩
                  F-coalg-colim.proj t2.x ∘ (t2.p' ∘ D.₁ s)    ≈˘⟨ F-coalg-colim.colimit-commute _ ⟩∘⟨refl ⟩
                  (F-coalg-colim.proj y.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁ y.i₂))) ∘ (t2.p' ∘ D.₁ s)    ≈⟨ assoc ⟩
                  F-coalg-colim.proj y.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁ y.i₂)) ∘ t2.p' ∘ D.₁ s
                  ∎
                -- By the (essential) uniqueness of t12.p', we get another
                -- coalgebra more upward in the diagram identifying p' and p'':
                z , h , h-prop = p'-unique t12 p'' p''-through-t12
                t3 : all-triangles
                t3 = P2 , record {
                   x = z ;
                   p' = F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ y.i₂))) ∘ t2.p' ;
                   commutes = begin
                      FA-colim.proj P2 ≈⟨ t2.commutes ⟩
                      F-coalg-colim.proj t2.x ∘ t2.p' ≈˘⟨ F-coalg-colim.colimit-commute _ ⟩∘⟨refl ⟩
                      _ ∘ t2.p' ≈⟨ assoc ⟩
                      -- F-coalg-colim.proj t12.x ∘ t12.p' ≈˘⟨ F-coalg-colim.colimit-commute _ ⟩∘⟨refl ⟩
                      -- (F-coalg-colim.proj z ∘ F.₁ (V.₁ (coalg-colim.D.₁ h))) ∘ t12.p' ≈⟨ assoc ⟩
                      F-coalg-colim.proj z ∘ F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ y.i₂))) ∘ t2.p'
                      ∎
                  }
                module t3 = Triangle (proj₂ t3)
                -- The following definition takes forever in agda:
                -- This triangle then provides an upper bound for t1 and t2 in 𝒮:
                t1⇒t3 : 𝒮 [ t1 , t3 ]
                t1⇒t3 = (s , (h coalg-colim.𝒟.∘ y.i₁)) ,
                   (begin
                   t3.p' ∘ D.₁ s  ≡⟨⟩
                   (F.₁ (V₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ y.i₂))) ∘ t2.p') ∘ D.₁ s
                     ≈⟨ ((F.F-resp-≈ (coalg-colim.D.homomorphism) ○ F.homomorphism) ⟩∘⟨refl) ⟩∘⟨refl ⟩
                   ((F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V₁ (coalg-colim.D.₁ y.i₂))) ∘ t2.p') ∘ D.₁ s
                     ≈⟨ assoc² ⟩
                   F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V₁ (coalg-colim.D.₁ y.i₂)) ∘ t2.p' ∘ D.₁ s
                     ≡⟨⟩
                   F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ p''
                     ≈˘⟨ h-prop ⟩
                   F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ t12.p'
                     ≡⟨⟩
                   F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V₁ (coalg-colim.D.₁ y.i₁)) ∘ t1.p'
                     ≈⟨ sym-assoc ⟩
                   (F.₁ (V₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V₁ (coalg-colim.D.₁ y.i₁))) ∘ t1.p'
                     ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩
                   F.₁ (V₁ (coalg-colim.D.₁ h) ∘ V₁ (coalg-colim.D.₁ y.i₁)) ∘ t1.p'
                     ≈˘⟨ F.F-resp-≈ coalg-colim.D.homomorphism ⟩∘⟨refl ⟩
                   F.₁ (V₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ y.i₁))) ∘ t1.p'
                   ∎)
                t2⇒t3 : 𝒮 [ t2 , t3 ]
                t2⇒t3 = (𝒟.id , (h coalg-colim.𝒟.∘ y.i₂)) ,
                  (begin
                  t3.p' ∘ D.₁ 𝒟.id
                     ≈⟨ identityʳ ⟩
                  t3.p'
                    ≡⟨⟩
                  F.₁ (V₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ y.i₂))) ∘ t2.p'
                  ∎)
              in
              begin
              (V₁ (B.ψ t2) ∘ P+X.i₁ t2) ∘ D.₁ s
              --  ≈˘⟨ B.commute {t2} {t3} t2⇒t3 ⟩∘⟨refl ⟩∘⟨refl ⟩
              --((V₁ (B.ψ t3) ∘ V₁ (S.₁ t2⇒t3) ) ∘ P+X.i₁ t2) ∘ D.₁ s
              -- ≈⟨ ? ⟩
              -- (V₁ (B.ψ t3) ∘ V₁ (S.₁ t1⇒t3) ) ∘ P+X.i₁ t1
                ≈⟨ {!!} ⟩
              (V₁ (B.ψ t1) ∘ P+X.i₁ t1)
              ∎
          }
      }

    -- FA,Fα-Cocone-is-Colimit : IsLimitting FA,Fα-Cocone
    -- FA,Fα-Cocone-is-Colimit =
    --   record { ! = λ {B} → {!!} ; !-unique = {!!} }

    -- iterated-LProp-Coalgebra : LProp-Coalgebra
    -- iterated-LProp-Coalgebra = record {
    --   -- the diagram for (FA,Fα)
    --   𝒟 = ℰ ;
    --   D = E ;
    --   all-have-prop = λ {t} →
    --     ConstructionComponents.P+X-coalg-is-FinitaryRecursive t;
    --   carrier-colim = ?
    --   }

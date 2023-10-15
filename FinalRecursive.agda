{-# OPTIONS --without-K  --lossy-unification --allow-unsolved-metas #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Category.Slice
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Categories.Category.Product
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.SubCategory
open import Categories.Category.Construction.Comma
open import Categories.Category.Slice
open import Categories.Functor.Construction.SubCategory
open import Categories.Functor using (Functor; Endofunctor)
open import Data.Product

open import Categories.Functor.Coalgebra

open import Data.Product
open import LFP using (WeaklyLFP)
open import Filtered
open import Cofinal
open import Setoids-Choice
open import Unchained-Utils

-- intuitively:
-- o : level of 'classes'
-- ℓ : level of 'sets'
module FinalRecursive {o ℓ fil-level}
  (𝒞 : Category o ℓ ℓ)
  (F : Endofunctor 𝒞)
  (Fil : ∀ {o' ℓ' e' : Level} → Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category ℓ ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 Fil)
  where

open import LFP 𝒞 hiding (WeaklyLFP)
module 𝒞 = Category 𝒞
open import recursive-coalgebra 𝒞 F
open import Hom-Colimit-Choice 𝒞
open import Categories.Morphism 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞
open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F}

module F-Coalgebras = Category (F-Coalgebras F)

record FinitaryRecursive (coalg : F-Coalgebra F) : Set (o ⊔ suc ℓ ⊔ fil-level) where
  -- the property that a coalgebra
  field
    -- 1. has finite carrier
    finite-carrier : presented Fil (F-Coalgebra.A coalg)
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
                      (has-coprod : HasCoproductOfPresentedObjects Fil)
                      -- we have sufficiently many coproducts
                      where
    -- in the proof, let V be the forgetful functor from coalgebras to 𝒞
    module V = Functor forget-Coalgebra
    Fil-presented = presented Fil
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
    module CC (t : all-triangles) where
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
        record { f = P+X.i₂ ;
        commutes = begin
          Fi₂[p',x] ∘ P+X.i₂ ≈⟨ assoc ⟩
          F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ refl⟩∘⟨ P+X.inject₂ ⟩
          F.₁ P+X.i₂ ∘ x
          ∎}
        where
          open HomReasoning
      module hom-from-X = F-Coalgebra-Morphism hom-from-X

      hom-to-FX : F-Coalgebra-Morphism P+X-coalg (iterate X,x)
      hom-to-FX =
        record { f = P+X.[ p' , x ] ;
        commutes = begin
          F.₁ x ∘ P+X.[ p' , x ] ≈˘⟨ F.F-resp-≈ P+X.inject₂ ⟩∘⟨refl ⟩
          F.₁ (P+X.[ p' , x ] ∘ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
          (F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ assoc ⟩
          F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ≡⟨⟩
          F.₁ P+X.[ p' , x ] ∘ Fi₂[p',x]
          ∎}
        where
          open HomReasoning
      module hom-to-FX = F-Coalgebra-Morphism hom-to-FX

      hom-to-FA : F-Coalgebra-Morphism P+X-coalg (iterate A,α)
      hom-to-FA = (iterate-F-Coalgebra-Morphism proj-X,x) F-Coalgebras.∘ hom-to-FX
      module hom-to-FA = F-Coalgebra-Morphism hom-to-FA

      hom-to-FA-i₁ : p ≈ hom-to-FA.f ∘ P+X.i₁
      hom-to-FA-i₁ =
        begin
        p ≈⟨ triangle-commutes ⟩
        F.₁ proj-X,x.f ∘ p' ≈˘⟨ refl⟩∘⟨ P+X.inject₁ ⟩
        F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₁ ≈⟨ sym-assoc ⟩
        (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₁ ≡⟨⟩
        hom-to-FA.f ∘ P+X.i₁
        ∎
        where
          open HomReasoning

      hom-to-FA-i₂ : α ∘ proj-X,x.f ≈ hom-to-FA.f ∘ P+X.i₂
      hom-to-FA-i₂ =
        begin
        α ∘ proj-X,x.f ≈⟨ proj-X,x.commutes ⟩
        F.₁ proj-X,x.f ∘ x ≈˘⟨ refl⟩∘⟨ P+X.inject₂ ⟩
        F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ sym-assoc ⟩
        (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₂ ≡⟨⟩
        hom-to-FA.f ∘ P+X.i₂
        ∎
        where
          open HomReasoning

      P+X-is-presented : presented Fil P+X.obj
      P+X-is-presented =
            presented-coproduct Fil
              Fil-to-filtered
              P+X P-is-presented X-is-presented

      --   The property that all objects in the diagram ...
      P+X-coalg-is-FinitaryRecursive : FinitaryRecursive P+X-coalg
      P+X-coalg-is-FinitaryRecursive =
        record {
          -- 1. .. have presented carrier
          finite-carrier = P+X-is-presented ;
          -- 2. .. are recursive:
          is-recursive =
            -- for recursiveness, we use our formalization of ([CUV06, Prop. 5])
            sandwich-recursive _ _ X,x-is-recursive hom-from-X hom-to-FX
              (let open HomReasoning in begin
              Fi₂[p',x] ≡⟨⟩ F.₁ hom-from-X.f ∘ hom-to-FX.f
              ∎)
          }

      -- -- from an old proof attempt:
      -- P+X-fin-idx : 𝒞-lfp.Idx
      -- P+X-fin-idx = proj₁ (𝒞-lfp.presentable-split-in-fin P+X.obj P+X-is-presented)
      -- -- P+X.obj is a split subobject of one from the fin family:
      -- P+X-fin : Retract P+X.obj (𝒞-lfp.fin P+X-fin-idx)
      -- P+X-fin = proj₂ (𝒞-lfp.presentable-split-in-fin P+X.obj P+X-is-presented)
      -- module P+X-fin = Retract P+X-fin

    -- the diagram scheme for the constructed LProp-Coalgebra
    ℰ : Category _ _ _
    ℰ = -- it is the full subcategory
        FullSubCategory
        -- of the slicecategory for FA, Fα
        (Slice (F-Coalgebras F) (iterate A,α))
        -- containing the constructed P+X coalgebras
        λ t → sliceobj (CC.hom-to-FA t)
    module ℰ = Category ℰ

    -- In order to show that FA is the colimit of ℰ,
    -- we construct a final functor to the following category:
    𝒮 : Category _ _ _
    𝒮 = Cat[ 𝒞-lfp.presented-obj ↓ (F.₀ A) ]
    module 𝒮 = Category 𝒮

    S-colim : Colimit Functor[ 𝒞-lfp.presented-obj ↓ (F.₀ A) ]
    S-colim = Colimit-from-prop (𝒞-lfp.presented-colimit (F.₀ A))
    module S-colim = Colimit S-colim

    E : Functor ℰ 𝒮
    E = record
         { F₀ = λ t → ((CC.P+X.obj t) , (CC.P+X-is-presented t)) , (CC.hom-to-FA.f t)
         ; F₁ = λ { f → slicearr (Slice⇒.△ f) }
         ; identity = 𝒞.Equiv.refl
         ; homomorphism = λ {X} {Y} {Z} {f} {g} → 𝒞.Equiv.refl
         ; F-resp-≈ = λ {X} {Y} {f} {g} eq → eq
         }
    module E = Functor E

    module reflect-𝒮 (s : 𝒮.Obj) where

    reflect-𝒮-to-ℰ : (s : 𝒮.Obj) → Σ[ t ∈ all-triangles ](s 𝒮.⇒ E.₀ t)
    reflect-𝒮-to-ℰ ((A , A-pres) , f) =
      let
        k , r = 𝒞-lfp.presentable-split-in-fin A A-pres
        module r = Retract r
        t = P-to-triangle (k , (f ∘ r.retract))
        open CC t
        open HomReasoning
      in
      t , slicearr {h = P+X.i₁ ∘ r.section} (
        begin
        hom-to-FA.f ∘ P+X.i₁ ∘ r.section ≈⟨ sym-assoc ⟩
        (hom-to-FA.f ∘ P+X.i₁) ∘ r.section ≈˘⟨ hom-to-FA-i₁ ⟩∘⟨refl ⟩
        (f ∘ r.retract) ∘ r.section ≈⟨ assoc ○ elimʳ r.is-retract ⟩
        f
        ∎)

    -- Next:
    E-is-final : Final E
    E-is-final = record {
      non-empty = λ s →
        let t , f = reflect-𝒮-to-ℰ s in
        record { β = t ; f = f } ;
      every-slice-connected = λ { S → record { connect =
        λ comma-obj1 comma-obj2 →
        let
          ((A , A-pres) , p) = S
          t1 : all-triangles
          t1 = CommaObj.β comma-obj1
          s1 : 𝒮 [ S , E.₀ t1 ]
          s1 = CommaObj.f comma-obj1
          t2 : all-triangles
          t2 = CommaObj.β comma-obj2
          s2 : 𝒮 [ S , E.₀ t2 ]
          s2 = CommaObj.f comma-obj2

          Union : Coproduct (CC.P+X.obj t1) (CC.P+X.obj t2)
          Union = has-coprod (CC.P+X.obj t1) (CC.P+X.obj t2) (CC.P+X-is-presented t1) (CC.P+X-is-presented t2)
          module Union = Coproduct Union renaming (A+B to obj)

          open CC

          Union-presentable = presented-coproduct Fil Fil-to-filtered Union (CC.P+X-is-presented t1) (CC.P+X-is-presented t2)
          k , r = 𝒞-lfp.presentable-split-in-fin Union.obj Union-presentable
          module r = Retract r
          t3 = P-to-triangle (k , (Union.[ hom-to-FA.f t1 , hom-to-FA.f t2 ] ∘ r.retract))

          open HomReasoning
          e1-hom : F-Coalgebra-Morphism (CC.P+X-coalg t1) (CC.P+X-coalg t3)
          e1-hom = record { f = P+X.i₁ t3 ∘ r.section ∘ Union.i₁ ;
            commutes = begin
            Fi₂[p',x] t3 ∘ (P+X.i₁ t3 ∘ r.section ∘ Union.i₁) ≈⟨ {!!} ⟩
            F.₁ (P+X.i₂ t3) ∘ (P+X.[_,_] t3 (p' t3) (x t3) ∘ P+X.i₁ t3) ∘ r.section ∘ Union.i₁ ≈⟨ {!!} ⟩
            (F.₁ (P+X.i₁ t3 ∘ r.section ∘ Union.i₁) ∘ Fi₂[p',x] t1)
            ∎
            }
          -- e1 : ℰ [ t1 , t3 ]
          -- e1 = slicearr {h = e1-hom} {!!}
        in
        -- we need to show that the two coalgebras for triangles t1 and t2
        -- are connected
        {!!}
      } } }


    -- 𝒮-to-𝒟 : Functor 𝒮 𝒟
    -- 𝒮-to-𝒟 =
    --   record
    --   { F₀ = λ t → (CC.P+X-fin-idx t) , (CC.hom-to-FA.f t ∘ CC.P+X-fin.retract t)
    --   ; F₁ = λ {t1} {t2} h →
    --        let module f = F-Coalgebra-Morphism (Slice⇒.h h) in
    --        slicearr
    --        {h = CC.P+X-fin.section t2 ∘ f.f ∘ CC.P+X-fin.retract t1}
    --        (begin
    --        (CC.hom-to-FA.f t2 ∘ CC.P+X-fin.retract t2) ∘ (CC.P+X-fin.section t2 ∘ f.f ∘ CC.P+X-fin.retract t1)
    --          ≈⟨ assoc ○ (refl⟩∘⟨ sym-assoc) ⟩
    --        CC.hom-to-FA.f t2 ∘ (CC.P+X-fin.retract t2 ∘ CC.P+X-fin.section t2) ∘ f.f ∘ CC.P+X-fin.retract t1
    --          ≈⟨ elim-center (CC.P+X-fin.is-retract t2) ⟩
    --        CC.hom-to-FA.f t2 ∘ f.f ∘ CC.P+X-fin.retract t1
    --          ≈⟨ sym-assoc ⟩
    --        (CC.hom-to-FA.f t2 ∘ f.f) ∘ CC.P+X-fin.retract t1
    --          ≈⟨ Slice⇒.△ h ⟩∘⟨refl ⟩
    --        (CC.hom-to-FA.f t1 ∘ CC.P+X-fin.retract t1)
    --        ∎)
    --   ; identity = λ {t} →
    --     begin
    --     CC.P+X-fin.section t ∘ id ∘ CC.P+X-fin.retract t
    --          ≈⟨ ? ⟩
    --     id
    --     ∎
    --   ; homomorphism = {!!}
    --   ; F-resp-≈ = λ eq → refl⟩∘⟨ eq ⟩∘⟨refl
    --   }
    --   where
    --     open HomReasoning

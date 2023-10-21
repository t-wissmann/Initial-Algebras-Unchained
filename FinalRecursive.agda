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
open import Categories.Functor.Slice as Sl
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
  (𝒞-lfp : WeaklyLFP 𝒞 Fil Fil-to-filtered)
  where


open import LFP 𝒞 Fil Fil-to-filtered hiding (WeaklyLFP)

module 𝒞 = Category 𝒞
open import recursive-coalgebra 𝒞 F
open import LFP-slices 𝒞
open import Hom-Colimit-Choice 𝒞
open import Categories.Diagram.Pushout 𝒞
open import Categories.Morphism 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞
open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F}

module F-Coalgebras = Category (F-Coalgebras F)

record FinitaryRecursive (coalg : F-Coalgebra F) : Set (o ⊔ suc ℓ ⊔ fil-level) where
  -- the property that a coalgebra
  field
    -- 1. has finite carrier
    finite-carrier : presented (F-Coalgebra.A coalg)
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
                      where
    -- in the proof, let V be the forgetful functor from coalgebras to 𝒞
    V = forget-Coalgebra
    module V = Functor forget-Coalgebra
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

      P-is-presented : presented P
      P-is-presented =
        -- here, we need to unfold the definition of P as a sliceobj
        -- from the index of a presented object
        let (idx , _) = (proj₁ t) in
        𝒞-lfp.fin-presented idx

      X-is-presented : presented X
      X-is-presented = FinitaryRecursive.finite-carrier coalg-colim.all-have-prop

      X,x-is-recursive : IsRecursive X,x
      X,x-is-recursive = FinitaryRecursive.is-recursive coalg-colim.all-have-prop

      -- the constructed coalgebra has a coproduct as its carrier
      P+X : Coproduct P X
      P+X = 𝒞-lfp.coproduct P X P-is-presented X-is-presented
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

      P+X-is-presented : presented P+X.obj
      P+X-is-presented =
            presented-coproduct
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
        λ t → sliceobj (CC.hom-to-FA t)
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

    data ⊥ : Set where

    exp : ∀ {n} {x : Set n} → ⊥ → x
    exp ()

    TODO-later : ∀ {n} {x : Set n} → x
    TODO-later = exp _

    coalg-hom-to-ℰ-hom : ∀ (P : 𝒟.Obj) (t1 t2 : Triangle F-coalg-colim (FA-colim.proj P))
                       → coalg-colim.𝒟 [ CC.X,x-dia (P , t1) , CC.X,x-dia (P , t2) ]
                       → ℰ [ (P , t1) , (P , t2) ]
    coalg-hom-to-ℰ-hom P t1 t2 coalg-hom =
      slicearr {h = record {
        f = t1.P+X.[ t2.P+X.i₁ , t2.P+X.i₂ ∘ coalg-hom.f ] ;
        commutes = TODO-later }}
      TODO-later
      where
        Pt1 : all-triangles
        Pt1 = (P , t1)
        module t1 = CC Pt1
        Pt2 : all-triangles
        Pt2 = (P , t2)
        module t2 = CC Pt2
        module coalg-hom = F-Coalgebra-Morphism (coalg-colim.D.₁ coalg-hom)

    cocone-is-triangle-independent : ∀ (K : Cocone (V ∘F E)) (P : 𝒟.Obj) (t1 t2 : Triangle F-coalg-colim (FA-colim.proj P))
                       → Cocone.ψ K (P , t1) ∘ CC.P+X.i₁ (P , t1) ≈ Cocone.ψ K (P , t2) ∘ CC.P+X.i₁ (P , t2)
    cocone-is-triangle-independent K P t1 t2 = ?

    E-Cocone-to-D : Cocone (V ∘F E) → Cocone D
    E-Cocone-to-D E-Cocone =
      record { coapex = record {
        ψ = λ { d →
          let
            t = P-to-triangle d
          in
          E-Cocone.ψ t ∘ CC.P+X.i₁ t} ;
        commute = λ {d1} {d2} h →
          let
            module h = Slice⇒ h
            t1 = P-to-triangle d1
            t2 = P-to-triangle d2
            Y,y-dia , g , g-eq = CC.p'-unique t2 {!!} {!!}
          in
          begin
          (E-Cocone.ψ t2 ∘ CC.P+X.i₁ t2) ∘ h.h
          ≈⟨ assoc ⟩
          E-Cocone.ψ t2 ∘ CC.P+X.i₁ t2 ∘ h.h
          ≈⟨ TODO-later ⟩
          (E-Cocone.ψ t1 ∘ CC.P+X.i₁ t1)
          ∎
        } }
      where
        module E-Cocone = Cocone E-Cocone
        open HomReasoning

    E-Cocone-to-D-choice : ∀ (K : Cocone (V ∘F E)) → (t : all-triangles) →
                         Cocone.ψ (E-Cocone-to-D K) (proj₁ t) ≈ Cocone.ψ K t ∘ CC.P+X.i₁ t
    E-Cocone-to-D-choice K t1 =
      begin
      Cocone.ψ (E-Cocone-to-D K) (proj₁ t1) ≡⟨⟩
      K.ψ t2 ∘ CC.P+X.i₁ t2 ≈⟨ TODO-later ⟩ -- Take upper bound of t1 and t2
      K.ψ t1 ∘ CC.P+X.i₁ t1
      ∎
      where
        t2 = P-to-triangle (proj₁ t1)
        open HomReasoning
        module K = Cocone K

    induced : ∀ (K : Cocone (V ∘F E)) → Cocone⇒ D FA-colim.colimit (E-Cocone-to-D K)
    induced K = FA-colim.rep-cocone (E-Cocone-to-D K)

    -- The definition of LProp-Coalgebra requires that the cocone on the level
    -- of carriers is colimitting:
    FA,Fα-Cocone-on-carriers : Cocone (V ∘F E)
    FA,Fα-Cocone-on-carriers = F-map-Coconeˡ V FA,Fα-Cocone
    module FA,Fα-Cocone-on-carriers = Cocone FA,Fα-Cocone-on-carriers

    lift-Cocone⇒ : ∀ (K : Cocone (V ∘F E)) → Cocone⇒ D FA-colim.colimit (E-Cocone-to-D K)
                   → Cocone⇒ (V ∘F E) FA,Fα-Cocone-on-carriers K
    lift-Cocone⇒ K v =
      record { arr = v.arr ; commute = λ {t} →
        let
          open CC t
          open HomReasoning
          t' = P-to-triangle (proj₁ t)
        in
        coproduct-jointly-epic P+X (record {
          case-precompose-i₁ = begin
            (v.arr ∘ hom-to-FA.f) ∘ P+X.i₁ ≈⟨ assoc ⟩
            v.arr ∘ (hom-to-FA.f ∘ P+X.i₁) ≈˘⟨ refl⟩∘⟨ hom-to-FA-i₁ ⟩
            v.arr ∘ p       ≈⟨  v.commute {proj₁ t}   ⟩
            Cocone.ψ (E-Cocone-to-D K) (proj₁ t)
              ≈⟨  E-Cocone-to-D-choice K t ⟩
            K.ψ t ∘ P+X.i₁
            ∎ ;
          case-precompose-i₂ =
            let
              open case2-defs t
              t' = P-to-triangle (proj₁ t-X)
            in
            begin
            (v.arr ∘ hom-to-FA.f) ∘ P+X.i₂ ≈⟨ assoc ⟩
            v.arr ∘ hom-to-FA.f ∘ P+X.i₂ ≈˘⟨ refl⟩∘⟨ hom-to-FA-i₂ ⟩
            v.arr ∘ α ∘ proj-X,x.f
              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ r.is-retract ⟩
            v.arr ∘ α ∘ t.proj-X,x.f ∘ r.retract ∘ r.section
              ≈˘⟨ refl⟩∘⟨ assoc²' ⟩
            v.arr ∘ FA-colim.proj α∘proj-x ∘ r.section
              ≈⟨ extendʳ v.commute ⟩
            K.ψ t' ∘ CC.P+X.i₁ t' ∘ r.section
              ≈⟨ sym-assoc ⟩
            Cocone.ψ (E-Cocone-to-D K) (proj₁ t-X) ∘ r.section
              ≈⟨ pushˡ (E-Cocone-to-D-choice K t-X) ⟩
            K.ψ t-X ∘ t-X.P+X.i₁ ∘ r.section
              ≈˘⟨ pullˡ (K.commute ∇)  ⟩
            K.ψ t ∘ ∇-f ∘ t-X.P+X.i₁ ∘ r.section
              ≈⟨ refl⟩∘⟨ extendʳ t-X.P+X.inject₁ ⟩
            K.ψ t ∘ t.P+X.i₂ ∘ r.retract ∘ r.section
              ≈⟨ refl⟩∘⟨ elimʳ r.is-retract ⟩
            K.ψ t ∘ P+X.i₂
            ∎
        })
      }
      where
        module v = Cocone⇒ v
        open HomReasoning
        module K = Cocone K
        module case2-defs (t : all-triangles) where
          module t = CC t
          m,r = 𝒞-lfp.presentable-split-in-fin t.X t.X-is-presented
          m : 𝒞-lfp.Idx
          m = proj₁ m,r
          r = proj₂ m,r
          module r = Retract r
          -- X ⇒ FA canonically factors through the diagram:
          α∘proj-x : 𝒟.Obj
          α∘proj-x = (m , (α ∘ t.proj-X,x.f ∘ r.retract))
          t-X : all-triangles
          t-X = α∘proj-x , triangle t.X,x-dia (t.x ∘ r.retract) (extendʳ t.proj-X,x.commutes)
          module t-X = CC t-X

          -- this morphism is an ℰ-morphism from t-X to t:
          ∇-f = t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ]
          ∇ : ℰ [ t-X , t ]
          ∇ =
            let
              open HomReasoning
              helper = begin
                F.F₁ t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ] ∘ t-X.Fi₂[p',x]
                      ≈⟨ sym-assoc ⟩
                (F.F₁ t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ] ∘ F.₁ t-X.P+X.i₂) ∘ t-X.P+X.[ t-X.p' , t-X.x ]
                      ≈˘⟨ (F.homomorphism ⟩∘⟨refl) ⟩
                F.F₁ (t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ] ∘ t-X.P+X.i₂) ∘ t-X.P+X.[ t-X.p' , t-X.x ]
                      ≈⟨ (F.F-resp-≈ t-X.P+X.inject₂ ⟩∘⟨refl) ⟩
                F.F₁ t.P+X.i₂ ∘ t-X.P+X.[ t-X.p' , t-X.x ]
                ∎
            in
            slicearr {h = record {
                -- the coalgebra morphism:
                f = ∇-f ;
                commutes = coproduct-jointly-epic t-X.P+X
                  (record {
                    case-precompose-i₁ = begin
                    (t.Fi₂[p',x] ∘ t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ]) ∘ t-X.P+X.i₁
                      ≈⟨ (assoc ○ (refl⟩∘⟨ t-X.P+X.inject₁)) ⟩
                    t.Fi₂[p',x] ∘ t.P+X.i₂ ∘ r.retract
                      ≈˘⟨ TODO-later ⟩
                    (F.F₁ t.P+X.i₂ ∘ t-X.P+X.[ t-X.p' , t-X.x ]) ∘ t-X.P+X.i₁
                      ≈˘⟨ helper ⟩∘⟨refl ⟩
                    (F.F₁ t-X.P+X.[ t.P+X.i₂ ∘ r.retract , t.P+X.i₂ ] ∘ t-X.Fi₂[p',x]) ∘ t-X.P+X.i₁
                    ∎
                    ;
                    case-precompose-i₂ = TODO-later
                  })
                }} (begin
                t.hom-to-FA.f ∘ ∇-f ≈⟨ TODO-later ⟩
                t-X.hom-to-FA.f
                ∎)

    reflect-Cocone⇒ : ∀ (K : Cocone (V ∘F E))
                   → Cocone⇒ (V ∘F E) FA,Fα-Cocone-on-carriers K
                   → Cocone⇒ D FA-colim.colimit (E-Cocone-to-D K)
    reflect-Cocone⇒ K other =
      record {
        arr = other.arr ;
        commute = λ {d} →
          let t = P-to-triangle d in
          begin
          other.arr ∘ FA-colim.proj d ≈⟨ refl⟩∘⟨ CC.hom-to-FA-i₁ t ⟩
          other.arr ∘ (CC.hom-to-FA.f t ∘ CC.P+X.i₁ t) ≈⟨ sym-assoc ⟩
          (other.arr ∘ CC.hom-to-FA.f t) ∘ CC.P+X.i₁ t ≈⟨ other.commute {t} ⟩∘⟨refl ⟩
          K.ψ t ∘ CC.P+X.i₁ t ≡⟨⟩
          Cocone.ψ (E-Cocone-to-D K) d
          ∎}
      where
        module other = Cocone⇒ other
        module K = Cocone K
        open HomReasoning

    FA,Fα-Colimit-on-carriers : IsLimitting FA,Fα-Cocone-on-carriers
    FA,Fα-Colimit-on-carriers =
      record {
        ! = λ {K} → lift-Cocone⇒ K (induced K) ;
        !-unique = λ {K} other →
          FA-colim.initial.!-unique (reflect-Cocone⇒ K other)
      }

    FA,Fα-locally-finite : LProp-Coalgebra
    FA,Fα-locally-finite = record {
      𝒟 = ℰ ; D = E ;
      all-have-prop = λ {t} → CC.P+X-coalg-is-FinitaryRecursive t ;
      carrier-colim = Colimit-from-prop FA,Fα-Colimit-on-carriers
      }


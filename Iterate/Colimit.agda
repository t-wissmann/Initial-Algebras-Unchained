{-# OPTIONS --without-K --lossy-unification --safe #-}
--    ^- the --lossy-unification flag speeds up compilation significantly
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Category.SubCategory
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Category.Slice
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Categories.Category.Construction.F-Coalgebras
open import Data.Product

open import Categories.Functor.Coalgebra

open import LFP using (WeaklyLFP)
open import Filtered
open import Unchained-Utils
open import Iterate.ProofGlobals

-- Let (A,α) be locally finite. For every P → FA, we construct
-- a finite subcoalgebra of (FA,Fα).
module Iterate.Colimit {o ℓ} {fil-level}
  {o' ℓ' : Level } -- Level for diagram schemes
  (Fil : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)  → Set fil-level) -- some variant of 'filtered'
  (proof-globals : ProofGlobals {o' = o'} {ℓ' = ℓ'} o ℓ Fil)
  where

open import Iterate.FiniteSubcoalgebra Fil proof-globals
open import Iterate.DiagramScheme Fil proof-globals
open ProofGlobals proof-globals
open import CoalgColim 𝒞 F FinitaryRecursive


cocone-is-triangle-independent : ∀ (K : Cocone (V ∘F E)) (P : 𝒟.Obj) (t1 t2 : Triangle F-coalg-colim (FA-colim.proj P))
                    → Cocone.ψ K (P , t1) ∘ CC.P+X.i₁ (P , t1) ≈ Cocone.ψ K (P , t2) ∘ CC.P+X.i₁ (P , t2)
cocone-is-triangle-independent K P t1 t2 = begin
    K.ψ Pt1 ∘ CC.P+X.i₁ Pt1
    ≈˘⟨ K.commute t1⇒t3 ⟩∘⟨refl ⟩
    (K.ψ Pt3 ∘ (V.₁ (E.₁ t1⇒t3))) ∘ CC.P+X.i₁ Pt1
    ≈˘⟨ ((K.commute t3⇒t4 ⟩∘⟨refl) ⟩∘⟨refl) ⟩
    ((K.ψ Pt4 ∘ (V.₁ (E.₁ t3⇒t4))) ∘ V.₁ (E.₁ t1⇒t3)) ∘ CC.P+X.i₁ Pt1
    ≈⟨ (assoc² ○ (refl⟩∘⟨ first-component-always-P) ○ sym-assoc) ⟩
    (K.ψ Pt4 ∘ (V.₁ (E.₁ t2⇒t4))) ∘ CC.P+X.i₁ Pt2
    ≈⟨ K.commute t2⇒t4 ⟩∘⟨refl ⟩
    K.ψ Pt2 ∘ CC.P+X.i₁ Pt2
    ∎
    where
    ℰ-hom : (t t' : Triangle F-coalg-colim (FA-colim.proj P))
                    (h : coalg-colim.𝒟 [ CC.X,x-dia (P , t) , CC.X,x-dia (P , t') ])
                    → CC.p' (P , t') ≈ F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ CC.p' (P , t)
                    → ℰ [ (P , t) , (P , t') ]
    ℰ-hom t t' 𝒟-mor preserves-p' = coalg-hom-to-ℰ-hom P t t' 𝒟-mor preserves-p'
    module t1 = CC (P , t1)
    module t2 = CC (P , t2)
    module K = Cocone K
    fil : filtered coalg-colim.𝒟
    fil = Fil-to-filtered 𝒟-filtered
    module fil = filtered fil
    X,x-bound : UpperBound _ t1.X,x-dia t2.X,x-dia
    X,x-bound = fil.construct-upper-bound t1.X,x-dia t2.X,x-dia
    module X,x-bound = UpperBound X,x-bound

    open HomReasoning
    -- we construct the following morphisms in ℰ:
    --   t1 ----> t3 ----> t4
    --                     ^
    --                     |
    --   t2 ---------------'

    -- take the upper bound of t1 and t2 in coalg-colim.𝒟
    t3 : Triangle F-coalg-colim (FA-colim.proj P)
    t3 = triangle X,x-bound.obj
        (F.₁ (V.₁ (coalg-colim.D.₁ X,x-bound.i₁))  ∘ t1.p' )
        (begin
        FA-colim.proj P ≈⟨ t1.triangle-commutes ⟩
        F.₁ t1.proj-X,x.f ∘ t1.p' ≈˘⟨ (F-coalg-colim.colimit-commute X,x-bound.i₁ ⟩∘⟨refl) ⟩
        (F-coalg-colim.proj X,x-bound.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₁))) ∘ t1.p'
            ≈⟨ assoc ⟩
        F-coalg-colim.proj X,x-bound.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₁)) ∘ t1.p'
        ∎)
    module t3 = CC (P , t3)
    t1⇒t3 : ℰ [ (P , t1) , (P , t3) ]
    t1⇒t3 = coalg-hom-to-ℰ-hom P _ _ X,x-bound.i₁ 𝒞.Equiv.refl
    -- However, there is no ℰ morphism from t2 to t3 because
    -- the coalgebra structure in t3 uses the pointing t1.p'.
    -- Using the pointing t2.p' yields another factorization for t3:
    to-t3-via-t2 = begin
        FA-colim.proj P ≈⟨ t2.triangle-commutes ⟩
        F.₁ t2.proj-X,x.f ∘ t2.p' ≈˘⟨ (F-coalg-colim.colimit-commute X,x-bound.i₂ ⟩∘⟨refl) ⟩
        (F-coalg-colim.proj X,x-bound.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₂))) ∘ t2.p'
            ≈⟨ assoc ⟩
        F-coalg-colim.proj X,x-bound.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₂)) ∘ t2.p'
        ∎
    -- By essential uniqueness, those two factorizations
    -- are identified somewhere in the diagram, say t4:
    tripl = t3.p'-unique _ to-t3-via-t2
    Y,y-dia = proj₁ tripl
    h : coalg-colim.𝒟 [ t3.X,x-dia , Y,y-dia ]
    h = proj₁ (proj₂ tripl)
    h-equalizes = proj₂ (proj₂ tripl)
    t4 : Triangle F-coalg-colim (FA-colim.proj P)
    t4 = triangle Y,y-dia
        (F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ X,x-bound.i₁)))  ∘ t1.p' )
        (begin
        FA-colim.proj P ≈⟨ t3.triangle-commutes ⟩
        F-coalg-colim.proj X,x-bound.obj ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₁)) ∘ t1.p'
        ≈˘⟨ F-coalg-colim.colimit-commute h ⟩∘⟨refl ⟩
        (F-coalg-colim.proj Y,y-dia ∘ F.₁ (V.₁ (coalg-colim.D.₁ h)))
        ∘ F.₁ (V.₁ (coalg-colim.D.₁  X,x-bound.i₁)) ∘ t1.p'
        ≈⟨ (assoc ○ (refl⟩∘⟨ pullˡ (⟺ (F.F-resp-≈ coalg-colim.D.homomorphism ○ F.homomorphism)))) ⟩
        F-coalg-colim.proj Y,y-dia
        ∘ F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘  X,x-bound.i₁)))
        ∘ t1.p'
        ∎)
    module t4 = CC (P , t4)
    t3⇒t4 : ℰ [ (P , t3) , (P , t4) ]
    t3⇒t4 = coalg-hom-to-ℰ-hom P _ _ h (begin
        F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ X,x-bound.i₁)))  ∘ t1.p'
        ≈⟨ (Functor.homomorphism (F ∘F V ∘F coalg-colim.D) ⟩∘⟨refl) ○ assoc ⟩
        F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V.₁ (coalg-colim.D.₁ X,x-bound.i₁))  ∘ t1.p'
        ∎)
    t2⇒t4 : ℰ [ (P , t2) , (P , t4) ]
    t2⇒t4 = coalg-hom-to-ℰ-hom P _ _ (h coalg-colim.𝒟.∘ X,x-bound.i₂) (begin
        F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ X,x-bound.i₁)))  ∘ t1.p'
        ≈⟨ ((Functor.homomorphism (F ∘F V ∘F coalg-colim.D) ⟩∘⟨refl) ○ assoc) ⟩
        F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V.₁ (coalg-colim.D.₁ X,x-bound.i₁))  ∘ t1.p'
        ≈⟨ h-equalizes ⟩
        F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ F.₁ (V.₁ (coalg-colim.D.₁ X,x-bound.i₂))  ∘ t2.p'
        ≈˘⟨ ((Functor.homomorphism (F ∘F V ∘F coalg-colim.D) ⟩∘⟨refl) ○ assoc) ⟩
        F.₁ (V.₁ (coalg-colim.D.₁ (h coalg-colim.𝒟.∘ X,x-bound.i₂))) ∘ t2.p'
        ∎)

    Pt1 = (P , t1)
    Pt2 = (P , t2)
    Pt3 : all-triangles
    Pt3 = (P , t3)
    Pt4 : all-triangles
    Pt4 = (P , t4)

    first-component-always-P =
        begin
        V.₁ (E.₁ t3⇒t4) ∘ V.₁ (E.₁ t1⇒t3) ∘ t1.P+X.i₁
        ≈⟨ refl⟩∘⟨ t1.P+X.inject₁ ⟩
        V.₁ (E.₁ t3⇒t4) ∘ t3.P+X.i₁
        ≈⟨ t3.P+X.inject₁ ⟩
        t4.P+X.i₁
        ≈˘⟨ t2.P+X.inject₁ ⟩
        V.₁ (E.₁ t2⇒t4) ∘ t2.P+X.i₁
        ∎

E-Cocone-to-D : Cocone (V ∘F E) → Cocone D
E-Cocone-to-D E-Cocone =
    record { coapex = record {
    ψ = λ { d →
        let
        t = P-to-triangle d
        in
        E-Cocone.ψ t ∘ CC.P+X.i₁ t} ;
    commute = λ {P} {Q} h →
        let
        open commute-defs h
        in
        begin
        (E-Cocone.ψ t2 ∘ CC.P+X.i₁ t2) ∘ h.h
        ≈⟨ assoc ⟩
        E-Cocone.ψ t2 ∘ CC.P+X.i₁ t2 ∘ h.h
        ≈˘⟨ refl⟩∘⟨ h+id∘i₁ ⟩
        E-Cocone.ψ t2 ∘ (V.₁ (E.₁ h+id-in-ℰ)) ∘ t2∘h.P+X.i₁
        ≈⟨ sym-assoc ○ (E-Cocone.commute h+id-in-ℰ ⟩∘⟨refl) ⟩
        E-Cocone.ψ (P , t2∘h) ∘ t2∘h.P+X.i₁
        ≈⟨ cocone-is-triangle-independent E-Cocone P t2∘h (proj₂ t1) ⟩
        (E-Cocone.ψ t1 ∘ CC.P+X.i₁ t1)
        ∎
    } }
    where
    module E-Cocone = Cocone E-Cocone
    open HomReasoning
    module commute-defs {P Q : 𝒟.Obj} (h : 𝒟 [ P , Q ]) where
        module h = Slice⇒ h
        t1 = P-to-triangle P
        t2 = P-to-triangle Q
        module t1 = CC t1
        module t2 = CC t2
        t2∘h : Triangle F-coalg-colim (FA-colim.proj P)
        t2∘h = triangle t2.X,x-dia (t2.p' ∘ h.h) (begin
            FA-colim.proj P ≈˘⟨ h.△  ⟩
            FA-colim.proj Q ∘ h.h ≈⟨ pushˡ t2.triangle-commutes  ⟩
            F-coalg-colim.proj t2.X,x-dia ∘ t2.p' ∘ h.h
            ∎)
        module t2∘h = CC (P , t2∘h)
        h+id : t2∘h.P+X.obj ⇒ t2.P+X.obj
        h+id = t2∘h.P+X.[
                    t2.P+X.i₁ ∘ h.h ,
                    t2.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id) ]
                    -- ^-- here, we need to postcompose with 'id' because
                    --     this is what build-ℰ-hom returns.
        h+id∘i₁ = begin
            h+id ∘ t2∘h.P+X.i₁
            ≈⟨ t2∘h.P+X.inject₁ ⟩
            t2.P+X.i₁ ∘ h.h
            ∎
        h+id-in-ℰ : ℰ [ (P , t2∘h) , t2 ]
        h+id-in-ℰ = build-ℰ-hom (P , t2∘h) t2
            (t2.P+X.i₁ ∘ h.h) coalg-colim.𝒟.id
            (begin
                t2.[p',x] ∘ t2.P+X.i₁ ∘ h.h ≈⟨ pullˡ t2.P+X.inject₁ ⟩
                t2.p' ∘ h.h ≡⟨⟩
                t2∘h.p' ≈˘⟨ elimˡ (Functor.identity (F ∘F V ∘F coalg-colim.D)) ⟩
                F.₁ (V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id)) ∘ t2∘h.p'
                ∎)
            (begin
            t2∘h.p       ≈˘⟨ h.△ ⟩
            t2.p ∘ h.h   ≈⟨ pushˡ t2.hom-to-FA-i₁ ⟩
            t2.hom-to-FA.f ∘ t2.P+X.i₁ ∘ h.h
            ∎)


E-Cocone-to-D-choice : ∀ (K : Cocone (V ∘F E)) → (t : all-triangles) →
                        Cocone.ψ (E-Cocone-to-D K) (proj₁ t) ≈ Cocone.ψ K t ∘ CC.P+X.i₁ t
E-Cocone-to-D-choice K t1 =
    begin
    Cocone.ψ (E-Cocone-to-D K) (proj₁ t1) ≡⟨⟩
    K.ψ t2 ∘ CC.P+X.i₁ t2 ≈⟨ cocone-is-triangle-independent K (proj₁ t1) (proj₂ t2) (proj₂ t1)  ⟩
    K.ψ t1 ∘ CC.P+X.i₁ t1
    ∎
    where
    t2 = P-to-triangle (proj₁ t1)
    open HomReasoning
    module K = Cocone K

induced : ∀ (K : Cocone (V ∘F E)) → Cocone⇒ D FA-colim.colimit (E-Cocone-to-D K)
induced K = FA-colim.rep-cocone (E-Cocone-to-D K)

-- The definition of CoalgColim requires that the cocone on the level
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
            ≈˘⟨ pullˡ (K.commute ∇) ⟩
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

        -- This morphism is an ℰ-morphism from t-X to t:
        ∇-f = t-X.P+X.[
                t.P+X.i₂ ∘ r.retract ,
                t.P+X.i₂ ∘ V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id)
                ]  --     ^-- we have the 'id' because it's returned this way
                    --         by build-ℰ-hom
        ∇ : ℰ [ t-X , t ]
        ∇ = let open HomReasoning in
            build-ℰ-hom t-X t (t.P+X.i₂ ∘ r.retract) coalg-colim.𝒟.id
            (begin
            t.[p',x] ∘ t.P+X.i₂ ∘ r.retract ≈⟨ pullˡ t.P+X.inject₂ ⟩
            t.x ∘ r.retract ≡⟨⟩
            t-X.p' ≈˘⟨ elimˡ (Functor.identity (F ∘F V ∘F coalg-colim.D)) ⟩
            F.₁ (V.₁ (coalg-colim.D.₁ coalg-colim.𝒟.id)) ∘ t-X.p'
            ∎)
            (begin
            t-X.p
                ≡⟨⟩
            α ∘ t.proj-X,x.f ∘ r.retract
                ≈⟨ extendʳ t.hom-to-FA-i₂ ⟩
            t.hom-to-FA.f ∘ t.P+X.i₂ ∘ r.retract
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

FA,Fα-locally-finite : CoalgColim
FA,Fα-locally-finite =
  record
  { 𝒟 = ℰ
  ; D = E
  ; all-have-prop = λ {t} → CC.P+X-coalg-is-FinitaryRecursive t 
  ; cocone = FA,Fα-Cocone
  ; carrier-colimitting = FA,Fα-Colimit-on-carriers
  }

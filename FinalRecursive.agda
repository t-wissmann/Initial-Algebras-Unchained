{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
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
open import Unchained-Utils
open import Setoids-Choice

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

record FinitaryRecursive (coalg : F-Coalgebra F) : Set (o ⊔ suc ℓ ⊔ suc e ⊔ fil-level) where
  -- the property that a coalgebra
  field
    -- 1. has finite carrier
    finite-carrier : presented 𝒞 ℓ ℓ ℓ Fil (F-Coalgebra.A coalg)
    -- 2. is recursive
    is-recursive : IsRecursive coalg


module 𝒞-lfp = WeaklyLFP 𝒞-lfp
open import Prop-Coalgebra 𝒞 F FinitaryRecursive

-- -- whenever (A,α) is locally finite, then so is (FA,Fα)
iterate-LProp-Coalgebra : (coalg : LProp-Coalgebra)
                      → Fil (LProp-Coalgebra.𝒟 coalg)
                      -- ^- coalg is a colimit of a filtered diagram
                      → preserves-colimit (LProp-Coalgebra.carrier-diagram coalg) F
                      -- ^- F preserves the colimit 'coalg'
                      → HasCoproductOfPresentedObjects 𝒞 ℓ ℓ ℓ Fil
                      → LProp-Coalgebra
iterate-LProp-Coalgebra coalg-colim 𝒟-filtered F-preserves-colim has-coprod =
  let
    Fil-presented = presented 𝒞 ℓ ℓ ℓ Fil
    -- the provided coalgebra:
    module coalg-colim = LProp-Coalgebra coalg-colim
    open F-Coalgebra coalg-colim.to-Coalgebra
    -- ^- this brings A and α into scope
    open Functor F
    open Category 𝒞
    -- ^ we only reason in 𝒞

    module F = Functor F

    -- We show that (FA,Fα) is a colimit by taking the
    -- diagram scheme from the fact that FA is a colimit of
    -- finite objects:
    FA-colim = 𝒞-lfp.canonical-colimit (F₀ A)
    module FA-colim = Colimit FA-colim

    𝒟 = 𝒞-lfp.canonical-diagram-scheme (F₀ A)
    module 𝒟 = Category 𝒟
    D = 𝒞-lfp.canonical-diagram (F₀ A)
    module D = Functor D

    -- -- At the same time, F(A,α) is a colimit of coalgebras, which
    -- -- is preserved by F:
    F-coalg-colim = Colimit-from-prop (F-preserves-colim coalg-colim.carrier-colim)

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

    -- The first ingredient is the 'intermediate' coalgebra through which
    -- the triangle factors:
    X,x : ∀ ((P , T) : all-triangles) → F-Coalgebra F
    X,x = λ {(P , T) → coalg-colim.D.₀ (Triangle.x T)}
    -- We also introduce names for the carrier and the structure, all
    -- parametrized by the triangle:
    X : all-triangles → 𝒞.Obj
    X t = F-Coalgebra.A (X,x t)
    x : ∀ (t : all-triangles) → (X t ⇒ F.₀ (X t))
    x t = F-Coalgebra.α (X,x t)

    P : all-triangles → 𝒞.Obj
    P t = D.₀ (proj₁ t)

    P-is-presented : ∀ (t : all-triangles) → (Fil-presented (P t))
    P-is-presented t =
      -- here, we need to unfold the definition of P as a sliceobj
      -- from the index of a presented object
      let (idx , _) = (proj₁ t) in
      𝒞-lfp.fin-presented idx

    X-is-presented : ∀ (t : all-triangles) → (Fil-presented (X t))
    X-is-presented t = FinitaryRecursive.finite-carrier coalg-colim.all-have-prop

    -- the constructed coalgebra has a coproduct as its carrier
    P+X : ∀ (t : all-triangles) → Coproduct (P t) (X t)
    P+X t = has-coprod (P t) (X t) (P-is-presented t) (X-is-presented t)
    module P+X t = Coproduct (P+X t) renaming (A+B to obj; [_,_] to ump_[_,_])

    -- and this carrier is presented:
    P+X-is-presented : ∀ (t : all-triangles) → Fil-presented (P+X.obj t)
    P+X-is-presented t =
          presented-coproduct 𝒞 ℓ ℓ ℓ Fil
            Fil-to-filtered
            (P+X t) (P-is-presented t) (X-is-presented t)

    p' : ∀ (t : all-triangles) → (P t ⇒ F.₀ (X t))
    p' t = Triangle.p' (proj₂ t)


    -- the structure of the constructed coalgebra:
    [p',x] : ∀ (t : all-triangles) → (P+X.obj t ⇒ F.₀ (P+X.obj t))
    [p',x] t = F.₁ (P+X.i₂ t) ∘ (P+X.ump t [ p' t , x t ])

    -- the combined constructed coalgebra
    P+X-coalg : all-triangles → F-Coalgebra F
    P+X-coalg t = record { A = P+X.obj t ; α = [p',x] t }

    -- The constructed coalgebra sits nicely between X,x and FX,Fx
    -- as we will see now:
    hom-from-X : ∀ (t : all-triangles) → F-Coalgebra-Morphism (X,x t) (P+X-coalg t)
    hom-from-X t =
      let open HomReasoning in
      record { f = P+X.i₂ t ;
      commutes = begin
        [p',x] t ∘ P+X.i₂ t  ≈⟨ ? ⟩
        F.₁ (P+X.i₂ t) ∘ x t
        ∎}

    -- the map from triangles to coalgebras gives rise to a functor
    -- from the full subcategory ℰ of such built coalgebras:
    ℰ : Category _ _ _
    ℰ = FullSubCategory (F-Coalgebras F) P+X-coalg
    E : Functor ℰ (F-Coalgebras F)
    E = FullSub (F-Coalgebras F)
  in
  record {
    -- the diagram for (FA,Fα)
    𝒟 = ℰ ;
    D = E ;
    -- the property that all objects in the diagram ...
    all-have-prop = λ {t} →
      record {
        -- 1. .. have presented carrier
        finite-carrier = P+X-is-presented t ;
        -- 2. .. are recursive:
        is-recursive = {!!} } ;
    carrier-colim = {!!}
    }
-- module _
--   (P : Category ℓ ℓ ℓ → Set prop-level)
--   (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
--   (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ P)
--   (𝒞-cocomplete : Cocomplete ℓ ℓ ℓ 𝒞)
--   where
--
--   module 𝒞-lfp = WeaklyLFP 𝒞-lfp
--   module F = Functor F

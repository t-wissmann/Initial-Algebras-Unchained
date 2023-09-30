{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
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
  (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ Fil)
  where

module 𝒞 = Category 𝒞
open import recursive-coalgebra 𝒞 F
open import Hom-Colimit-Choice

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
                      → LProp-Coalgebra
iterate-LProp-Coalgebra coalg-colim 𝒟-filtered F-preserves-colim =
  let
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
    -- triangles =
    --   Σ[ P ∈ 𝒟.Obj ]
    --   Σ[ X ∈ (Category.Obj coalg-colim.𝒟) ]
    --   Σ[ p ∈ (D.₀ P ⇒ (F.₀ (F-Coalgebra.A (Functor.₀ coalg-colim.D X)))) ]
    --     (FA-colim.proj P ≈ F.₁ (coalg-colim.carrier-colim.proj X) ∘ p)

    -- -- -- in fact, every P can be extended to such a triangle:
    -- P-to-triangle : 𝒟.Obj → triangles
    -- P-to-triangle P =
    --   let
    --     (idx , _) = P
    --     -- the hom functor 𝒞(i, -) preserves the above colimit F(A,α)
    --     hom-colim : Colimit (Hom[ 𝒞 ][ (𝒞-lfp.fin idx) ,-] ∘F (F ∘F coalg-colim.carrier-diagram))
    --     hom-colim = Colimit-from-prop
    --       (𝒞-lfp.fin-presented idx
    --         coalg-colim.𝒟 -- the diagram scheme
    --         𝒟-filtered    -- the fact that the diagram scheme is filtered
    --         (F ∘F coalg-colim.carrier-diagram)
    --         F-coalg-colim)
    --     module hom-colim = Colimit hom-colim
    --     -- the 'preservation' means that they have the same carrier:
    --     _ : hom-colim.coapex ≡ 𝒞.hom-setoid {𝒞-lfp.fin idx} {F₀ A}
    --     _ = refl
    --     -- so we can now find out where above pointing i⇒FA comes from
    --     X,x , P⇒FX = colimit-choice hom-colim (FA-colim.proj P)

    --     X = F-Coalgebra.A (Functor.₀ coalg-colim.D X,x)
    --     x = F-Coalgebra.α (Functor.₀ coalg-colim.D X,x)

    --     _ : (𝒞-lfp.fin idx) ⇒ (F₀ X)
    --     _ = P⇒FX

    --   in
    --   P , (X,x , (P⇒FX , colimit-choice-correct {!!} )) -- !{!colimit-choice-correct hom-colim {FA-colim.proj P}!})) -- colimit-choice-correct hom-colim )) -- use: colimit-choice-correct
    all-triangles =
      Σ[ P ∈ 𝒟.Obj ]
      Triangle F-coalg-colim (FA-colim.proj P)
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
  in
  {!!}
-- module _
--   (P : Category ℓ ℓ ℓ → Set prop-level)
--   (P-implies-filtered : ∀ (𝒟 : _) → P 𝒟 → filtered 𝒟)
--   (𝒞-lfp : WeaklyLFP 𝒞 ℓ ℓ ℓ P)
--   (𝒞-cocomplete : Cocomplete ℓ ℓ ℓ 𝒞)
--   where
--
--   module 𝒞-lfp = WeaklyLFP 𝒞-lfp
--   module F = Functor F

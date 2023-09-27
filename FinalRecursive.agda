{-# OPTIONS --without-K #-}
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

    -- -- the object assignment of new the diagram:
    D₀' : 𝒟.Obj → F-Coalgebra F
    D₀' = λ (P , P⇒FA) →
      let
        -- the hom functor 𝒞(i, -) preserves the above colimit F(A,α)
        hom-colim : Colimit (Hom[ 𝒞 ][ (𝒞-lfp.fin P) ,-] ∘F (F ∘F coalg-colim.carrier-diagram))
        hom-colim = Colimit-from-prop
          (𝒞-lfp.fin-presented P
            coalg-colim.𝒟 -- the diagram scheme
            𝒟-filtered    -- the fact that the diagram scheme is filtered
            (F ∘F coalg-colim.carrier-diagram)
            F-coalg-colim)
        module hom-colim = Colimit hom-colim
        -- the 'preservation' means that they have the same carrier:
        _ : hom-colim.coapex ≡ 𝒞.hom-setoid {𝒞-lfp.fin P} {F₀ A}
        _ = refl
        -- so we can now find out where above pointing i⇒FA comes from
        --X,x , pointing = colimit-choice

      in
      {!!}
  in
  record {
    𝒟 = 𝒟 ; -- maybe we can use the same diagram
    D = {!!} ;
    all-have-prop = {!!} ;
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

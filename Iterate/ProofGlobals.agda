{-# OPTIONS --without-K #-}
open import Level
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
open import Data.Product

open import Categories.Functor.Coalgebra

open import LFP using (WeaklyLFP)
open import Filtered
open import Unchained-Utils

-- Here, we fix some modules/helper definitions
-- for the iteration proof.
module Iterate.ProofGlobals {fil-level}
  {o' ℓ' e' : Level } -- Level for diagram schemes
  (Fil : ∀ {o' ℓ' e' : Level} → Category o' ℓ' e' → Set fil-level) -- some variant of 'filtered'
  where

open import CoalgColim
import Iterate.Assumptions as Assumption

record ProofGlobals (o ℓ : Level) : Set (suc (o' ⊔ ℓ' ⊔ e') ⊔ suc fil-level ⊔ suc (o ⊔ ℓ)) where
  -- o' ℓ' e' are the levels of the diagram of the input coalgebra colimit
  field
    𝒞 : Category o ℓ ℓ
    F : Endofunctor 𝒞
    -- The notion 'Fil' implies filtered:
    Fil-to-filtered : ∀ {𝒟 : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (e' ⊔ ℓ)} → Fil 𝒟 → filtered 𝒟
    𝒞-lfp : WeaklyLFP 𝒞 o' ℓ' e' Fil Fil-to-filtered
    -- A coalgebra colimit:
    coalg-colim : CoalgColim 𝒞 F (Assumption.FinitaryRecursive {o' = o'} {ℓ' = ℓ'} {e' = e'} 𝒞 F Fil) {o' ⊔ ℓ} {ℓ' ⊔ ℓ} {e' ⊔ ℓ}
    𝒟-filtered : Fil (CoalgColim.𝒟 coalg-colim)
    -- ^- coalg is a colimit of a filtered diagram
    F-preserves-colim : preserves-colimit (CoalgColim.carrier-diagram coalg-colim) F
    -- ^- F preserves the colimit 'coalg'


  open import LFP 𝒞 o' ℓ' e' Fil Fil-to-filtered hiding (WeaklyLFP) public

  module 𝒞 = Category 𝒞
  open import Hom-Colimit-Choice 𝒞 public
  open import Categories.Diagram.Pushout 𝒞 public
  open import Categories.Morphism 𝒞 public
  open import Categories.Object.Coproduct 𝒞 public
  open import Categories.Morphism.Reasoning.Core 𝒞 public
  open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F} public

  module F-Coalgebras = Category (F-Coalgebras F)

  module 𝒞-lfp = WeaklyLFP 𝒞-lfp

  open LiftHom (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (e' ⊔ ℓ) public

  -- in the proof, let V be the forgetful functor from coalgebras to 𝒞
  V = forget-Coalgebra
  module V = Functor forget-Coalgebra
  -- the provided coalgebra:
  module coalg-colim = CoalgColim.CoalgColim coalg-colim
  A,α = coalg-colim.to-Coalgebra
  open F-Coalgebra A,α public
  -- ^- this brings A and α into scope
  open Functor F public
  open Category 𝒞 hiding (op) public
  -- ^ we only reason in 𝒞

  module F = Functor F

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

  open import Presented 𝒞 (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (e' ⊔ ℓ) Fil public
  open import recursive-coalgebra 𝒞 F public
  open import Iterate.Assumptions {o' = o'} {ℓ' = ℓ'} {e' = e'} 𝒞 F Fil public

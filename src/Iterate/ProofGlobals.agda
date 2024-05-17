{-# OPTIONS --without-K --safe #-}
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

open import Accessible-Category using (Accessible)
open import Filtered
open import Colimit-Lemmas

-- Here, we fix some modules/helper definitions
-- for the iteration proof.
module Iterate.ProofGlobals {fil-level}
  {o' ℓ' : Level } -- Level for diagram schemes
  (o ℓ : Level) -- Level of the category 𝒞
  (Fil : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ) → Set fil-level) -- some variant of 'filtered'
  where

open import CoalgColim
import Iterate.Assumptions as Assumption

record ProofGlobals : Set (suc (o' ⊔ ℓ') ⊔ suc fil-level ⊔ suc (o ⊔ ℓ)) where
  -- o' ℓ' e' are the levels of the diagram of the input coalgebra colimit
  field
    𝒞 : Category o ℓ ℓ
    F : Endofunctor 𝒞
    -- The notion 'Fil' implies filtered:
    Fil-to-filtered : ∀ {𝒟 : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)} → Fil 𝒟 → filtered 𝒟
    𝒞-acc : Accessible 𝒞 o' ℓ' ℓ' Fil Fil-to-filtered -- TODO: rename
    -- A coalgebra colimit:
    coalg-colim : CoalgColim 𝒞 F (Assumption.FiniteRecursive {o' = o'} {ℓ' = ℓ'} 𝒞 F Fil) {o' ⊔ ℓ} {ℓ' ⊔ ℓ}
    𝒟-filtered : Fil (CoalgColim.𝒟 coalg-colim)
    -- ^- coalg is a colimit of a filtered diagram
    F-preserves-colim : preserves-colimit (CoalgColim.carrier-diagram coalg-colim) F
    -- ^- F preserves the colimit 'coalg'


  open import Accessible-Category 𝒞 o' ℓ' ℓ' Fil Fil-to-filtered hiding (Accessible) public

  module 𝒞 = Category 𝒞
  open import Hom-Colimit-Choice 𝒞 public
  open import Categories.Diagram.Pushout 𝒞 public
  open import Categories.Morphism 𝒞 public
  open import Categories.Object.Coproduct 𝒞 public
  open import Categories.Morphism.Reasoning.Core 𝒞 public
  open import F-Coalgebra-Colimit {_} {_} {_} {𝒞} {F} public

  module F-Coalgebras = Category (F-Coalgebras F)

  module 𝒞-acc = Accessible 𝒞-acc

  open LiftHom (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ) public

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

  𝒞p/FA = 𝒞-acc.canonical-diagram-scheme (F₀ A)
  module 𝒞p/FA = Category 𝒞p/FA
  U-𝒞p/FA = 𝒞-acc.canonical-diagram (F₀ A)
  module U-𝒞p/FA = Functor U-𝒞p/FA
  FA-colim : Colimit U-𝒞p/FA
  FA-colim = 𝒞-acc.canonical-colimit (F₀ A)
  module FA-colim = Colimit FA-colim

  -- -- At the same time, F(A,α) is a colimit of coalgebras, which
  -- -- is preserved by F:
  F-coalg-colim = Colimit-from-prop (F-preserves-colim coalg-colim.carrier-colim)
  module F-coalg-colim = Colimit F-coalg-colim

  open import Presentable 𝒞 (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ) Fil public
  open import Coalgebra.Recursive 𝒞 F public
  open import Iterate.Assumptions {o' = o'} {ℓ' = ℓ'} 𝒞 F Fil public

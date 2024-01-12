{-# OPTIONS --without-K #-}
open import Level

open import Categories.Category
open import Categories.Category.SubCategory
open import Categories.Functor using (Functor; Endofunctor; _∘F_)
open import Categories.Functor.Coalgebra hiding (to-Coalgebra)
open import Categories.Category.Construction.F-Coalgebras
import Categories.Functor.Coalgebra as Coalg
open import Categories.Functor.Construction.SubCategory
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)

open import F-Coalgebra-Colimit
open import Unchained-Utils
open import Notation

module CoalgColim {o ℓ e}
  {P-level : Level}
  (𝒞 : Category o ℓ e)
  (F : Endofunctor 𝒞)
  (Prop : F-Coalgebra F → Set P-level)  -- a property of coalgebras
  where

private
  module 𝒞 = Category 𝒞
  module F = Functor F

record CoalgColim {o' ℓ' e'} : Set (o ⊔ ℓ ⊔ e ⊔ P-level ⊔ suc (o' ⊔ ℓ' ⊔ e')) where
  -- A Coalg(ebra)Colim(it) is a colimit of coalgebras whose carriers
  -- all satisfies a fixed property.
  field
    -- So it consists of: 1. a diagram scheme
    𝒟 : Category o' ℓ' e'
    -- 2. a diagram in coalgebras:
    D : Functor 𝒟 (F-Coalgebras F)
    -- 3. whose all satisfiy a given property:
    all-have-prop : ∀ {i : Category.Obj 𝒟} → Prop (Functor.₀ D i)
    -- 4. and a cocone of D
    cocone : Cocone D
    -- 5. which is colimitting in 𝒞:
    carrier-colimitting : IsLimitting (F-map-Coconeˡ forget-Coalgebra cocone)

  module 𝒟 = Category 𝒟
  module D = Functor D

  -- composition with the forgetful functor
  U∘D : Functor 𝒟 𝒞
  U∘D = forget-Coalgebra ∘F D

  module U∘D = Functor U∘D

  carrier-colim : Colimit U∘D
  carrier-colim = Colimit-from-prop carrier-colimitting
  module carrier-colim = Colimit carrier-colim

  colim : Colimit D
  colim = Colimit-from-prop (F-Coalgebras-Limitting-Cocone D cocone carrier-colimitting)

  module colim = Colimit colim

  to-Coalgebra : F-Coalgebra F
  to-Coalgebra = colim.coapex

  -- the diagram 'D' restricted to the carriers / 𝒞-objects
  carrier-diagram : Functor 𝒟 𝒞
  carrier-diagram = forget-Coalgebra ∘F D

  unique-homomorphism : ∀ (B : F-Coalgebra F) →
    (∀ (i : 𝒟.Obj) → (F-Coalgebras F) [ D.₀ i =∃!=> B ]) →
    (F-Coalgebras F) [ colim.coapex =∃!=> B ]
  unique-homomorphism B uniq = colimit-unique-rep 𝒟 D colim B uniq

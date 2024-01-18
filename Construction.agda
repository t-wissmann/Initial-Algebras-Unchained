{-# OPTIONS --without-K --safe #-}
open import Level

-- The construction in its most general Form

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Coalgebra
open import Categories.Diagram.Cocone
open import Categories.Diagram.Colimit
open import Categories.Category.SubCategory
open import Categories.Object.Initial
open import Categories.Morphism

open import Filtered
open import LFP using (WeaklyLFP)
open import CoalgColim
open import F-Coalgebra-Colimit
open import Data.Product
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Coalgebra
open import Categories.Functor.Properties using (Full)
open import Function.Surjection using (Surjective)
open import Function.Equality hiding (_∘_)
open import Categories.Functor.Construction.SubCategory using (FullSub)
open import Categories.Functor.Construction.SubCategory.Properties using (FullSubFull)

open import Helper-Definitions
open import Colimit-Lemmas
open import Helper-Definitions

module Construction {o ℓ}
  (𝒞 : Category (o ⊔ ℓ) ℓ ℓ)
  (F : Endofunctor 𝒞)
  {fil-level : Level}
  (Fil : Category (o ⊔ ℓ) ℓ ℓ → Set fil-level) -- some variant of 'filtered'
  (Fil-to-filtered : ∀ {𝒟 : Category (o ⊔ ℓ) ℓ ℓ} → Fil 𝒟 → filtered 𝒟) -- .. which implies filtered
  (𝒞-lfp : WeaklyLFP 𝒞 (o ⊔ ℓ) ℓ ℓ Fil Fil-to-filtered)
  where

open import Coalgebra.Recursive 𝒞 F
open import Unique-Proj 𝒞 F Fil Fil-to-filtered 𝒞-lfp
open import Categories.Morphism.Reasoning 𝒞
open import Lambek 𝒞 F

private
    module 𝒞 = Category 𝒞
    module 𝒞-lfp = WeaklyLFP 𝒞-lfp
    module F = Functor F
    module U = Functor (forget-Coalgebra {C = 𝒞} {F = F})


open import Coalgebra.IdxProp 𝒞 F 𝒞-lfp.fin IsRecursive

module FinalRecursive
       (carrier-colimit : Colimit forget-IdxPropCoalgebra)
       (coalgebras-filtered : Fil IdxPropCoalgebras)
       (F-finitary : preserves-colimit forget-IdxPropCoalgebra F)
       where

  open import Iterate.Assumptions {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil
  open import Iterate {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil Fil-to-filtered 𝒞-lfp
  private
    module carrier-colimit = Colimit carrier-colimit

  -- if the finite recursive coalgebras have a colimit on the object level,
  -- then this lifts to the category of coalgebras:
  B,β : CoalgColim {o ⊔ ℓ} {ℓ} {ℓ} 𝒞 F FinitaryRecursive
  B,β = record
        { 𝒟 = IdxPropCoalgebras
        ; D = forget-IdxProp
        ; all-have-prop =
          λ {i} → record {
            finite-carrier = 𝒞-lfp.fin-presented (IdxPropCoalgebra.carrier i) ;
            is-recursive = IdxPropCoalgebra.has-prop i }
        ; cocone = F-Coalgebras-Lift-Cocone forget-IdxProp carrier-colimit
        ; carrier-colimitting = F-Coalgebras-Colimit-Carrier-Limitting forget-IdxProp carrier-colimit
        }
  module B,β = CoalgColim.CoalgColim B,β

  B,β-scheme-Full : Full-≈ forget-IdxProp
  B,β-scheme-Full = record {
    preimage = λ X Y f → f ;
    preimage-prop = λ X Y f →
      let
        open Category (F-Coalgebras F)
        open HomReasoning
      in
      begin f ≡⟨⟩ f ∎ -- I didn't manage to phrase it via 'Equiv.refl' directly...
    }

  FB,Fβ : CoalgColim 𝒞 F FinitaryRecursive
  FB,Fβ = iterate-CoalgColimit B,β coalgebras-filtered F-finitary
  module FB,Fβ = CoalgColim.CoalgColim FB,Fβ

  B,β-proj-uniq : (i : B,β.𝒟.Obj) → F-Coalgebras F [ B,β.D.₀ i =∃!=> B,β.to-Coalgebra ]
  B,β-proj-uniq i = record {
    arr = B,β.colim.proj i ;
    unique = λ h → let
        open Category (F-Coalgebras F)
        open HomReasoning
      in begin
        B,β.colim.proj i
          ≈˘⟨ unique-proj B,β F-finitary coalgebras-filtered (B,β-scheme-Full) h ⟩
        h
        ∎
      }

  unique-endo : F-Coalgebras F [ B,β.to-Coalgebra =∃!=> B,β.to-Coalgebra ]
  unique-endo = B,β.unique-homomorphism B,β.to-Coalgebra B,β-proj-uniq
  module unique-endo = singleton-hom unique-endo

  universal-property : ∀ (X : F-Coalgebra F) → FinitaryRecursive X →
                         F-Coalgebras F [ X =∃!=> B,β.to-Coalgebra ]
  universal-property X X-finrec = record
    { arr = proj-j.arr ∘ X→Dj
    ; unique = λ h →
      let open HomReasoning in
      begin
      proj-j.arr ∘ X→Dj ≈⟨ pushˡ (proj-j.unique (h ∘ Dj→X)) ⟩
      h ∘ Dj→X ∘ X→Dj ≈⟨ elimʳ r.is-retract ⟩
      h
      ∎
    }
    where
      -- all compositions are on the level of coalgebra homomorphisms
      open Category (F-Coalgebras F)
      module X = F-Coalgebra X
      -- there is a split-quotient to one of the lfp generators:
      quot : Σ[ idx ∈ 𝒞-lfp.Idx ] (Retract 𝒞 X.A (𝒞-lfp.fin idx))
      quot = 𝒞-lfp.presentable-split-in-fin X.A
        (FinitaryRecursive.finite-carrier X-finrec)
      j' = proj₁ quot
      r = proj₂ quot
      module r = Retract r
      -- and thus this gives us a coalgebra in the diagram of B,β:
      j : B,β.𝒟.Obj
      j = record {
        carrier = j' ;
        structure = F-Coalgebra.α (retract-coalgebra X r) ;
        has-prop = retract-coalgebra-recursive X r (FinitaryRecursive.is-recursive X-finrec) }

      proj-j : F-Coalgebras F [ B,β.D.₀ j =∃!=> B,β.to-Coalgebra ]
      proj-j = B,β-proj-uniq j
      module proj-j = singleton-hom proj-j

      X→Dj : F-Coalgebras F [ X , B,β.D.₀ j ]
      X→Dj = retract-coalgebra-hom X r

      Dj→X : F-Coalgebras F [ B,β.D.₀ j , X ]
      Dj→X = retract-coalgebra-hom⁻¹ X r


  inverse : F-Coalgebras F [ FB,Fβ.to-Coalgebra =∃!=> B,β.to-Coalgebra ]
  inverse = (FB,Fβ.unique-homomorphism
        B,β.to-Coalgebra
        λ i → universal-property (FB,Fβ.D.₀ i) (FB,Fβ.all-have-prop {i}))
  module inverse = singleton-hom inverse

  fixpoint : Iso 𝒞 B,β.structure (U.₁ inverse.arr)
  fixpoint = lambek B,β.to-Coalgebra
    (λ endo → unique-endo.unique₂ endo (Category.id (F-Coalgebras F) {B,β.to-Coalgebra}))
    inverse.arr

  B,β-recursive : IsRecursive B,β.to-Coalgebra
  B,β-recursive = Limitting-Cocone-IsRecursive B,β.D IdxPropCoalgebra.has-prop B,β.cocone B,β.carrier-colimitting

  initial-algebra : Initial (F-Algebras F)
  initial-algebra = record {
    ⊥ = record { A = B,β.carrier ; α = U.₁ inverse.arr } ;
    ⊥-is-initial =
      iso-recursive⇒initial
        B,β.to-Coalgebra
        B,β-recursive
        (record { inv = U.₁ inverse.arr ; iso = fixpoint }) }

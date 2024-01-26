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
open import Unique-Proj 𝒞 F Fil Fil-to-filtered
open import Categories.Morphism.Reasoning 𝒞
open import Lambek 𝒞 F

private
    module 𝒞 = Category 𝒞
    module 𝒞-lfp = WeaklyLFP 𝒞-lfp
    module F = Functor F
    module U = Functor (forget-Coalgebra {𝒞 = 𝒞} {F = F})


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
  A,α : CoalgColim {o ⊔ ℓ} {ℓ} {ℓ} 𝒞 F FiniteRecursive
  A,α = record
        { 𝒟 = IdxPropCoalgebras
        ; D = forget-IdxProp
        ; all-have-prop =
          λ {i} → record {
            finite-carrier = 𝒞-lfp.fin-presentable (IdxPropCoalgebra.carrier i) ;
            is-recursive = IdxPropCoalgebra.has-prop i }
        ; cocone = F-Coalgebras-Lift-Cocone forget-IdxProp carrier-colimit
        ; carrier-colimitting = F-Coalgebras-Colimit-Carrier-Limitting forget-IdxProp carrier-colimit
        }
  module A,α = CoalgColim.CoalgColim A,α

  A,α-scheme-Full : Full-≈ forget-IdxProp
  A,α-scheme-Full = record {
    preimage = λ X Y f → f ;
    preimage-prop = λ X Y f →
      let
        open Category (F-Coalgebras F)
        open HomReasoning
      in
      begin f ≡⟨⟩ f ∎ -- I didn't manage to phrase it via 'Equiv.refl' directly...
    }

  FA,Fα : CoalgColim 𝒞 F FiniteRecursive
  FA,Fα = iterate-CoalgColimit A,α coalgebras-filtered F-finitary
  module FA,Fα = CoalgColim.CoalgColim FA,Fα

  A,α-proj-uniq : (i : A,α.𝒟.Obj) → F-Coalgebras F [ A,α.D.₀ i =∃!=> A,α.to-Coalgebra ]
  A,α-proj-uniq i = record {
    arr = A,α.colim.proj i ;
    unique = λ h → let
        open Category (F-Coalgebras F)
        open HomReasoning
      in begin
        A,α.colim.proj i
          ≈˘⟨ unique-proj A,α F-finitary coalgebras-filtered (A,α-scheme-Full) h ⟩
        h
        ∎
      }

  unique-endo : F-Coalgebras F [ A,α.to-Coalgebra =∃!=> A,α.to-Coalgebra ]
  unique-endo = A,α.unique-homomorphism A,α.to-Coalgebra A,α-proj-uniq
  module unique-endo = singleton-hom unique-endo

  universal-property : ∀ (X : F-Coalgebra F) → FiniteRecursive X →
                         F-Coalgebras F [ X =∃!=> A,α.to-Coalgebra ]
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
        (FiniteRecursive.finite-carrier X-finrec)
      j' = proj₁ quot
      r = proj₂ quot
      module r = Retract r
      -- and thus this gives us a coalgebra in the diagram of B,β:
      j : A,α.𝒟.Obj
      j = record {
        carrier = j' ;
        structure = F-Coalgebra.α (retract-coalgebra X r) ;
        has-prop = retract-coalgebra-recursive X r (FiniteRecursive.is-recursive X-finrec) }

      proj-j : F-Coalgebras F [ A,α.D.₀ j =∃!=> A,α.to-Coalgebra ]
      proj-j = A,α-proj-uniq j
      module proj-j = singleton-hom proj-j

      X→Dj : F-Coalgebras F [ X , A,α.D.₀ j ]
      X→Dj = retract-coalgebra-hom X r

      Dj→X : F-Coalgebras F [ A,α.D.₀ j , X ]
      Dj→X = retract-coalgebra-hom⁻¹ X r


  inverse : F-Coalgebras F [ FA,Fα.to-Coalgebra =∃!=> A,α.to-Coalgebra ]
  inverse = (FA,Fα.unique-homomorphism
        A,α.to-Coalgebra
        λ i → universal-property (FA,Fα.D.₀ i) (FA,Fα.all-have-prop {i}))
  module inverse = singleton-hom inverse

  fixpoint : Iso 𝒞 A,α.structure (U.₁ inverse.arr)
  fixpoint = lambek A,α.to-Coalgebra
    (λ endo → unique-endo.unique₂ endo (Category.id (F-Coalgebras F) {A,α.to-Coalgebra}))
    inverse.arr

  A,α-recursive : IsRecursive A,α.to-Coalgebra
  A,α-recursive =
    Limitting-Cocone-IsRecursive A,α.D
      IdxPropCoalgebra.has-prop
      A,α.cocone A,α.carrier-colimitting

  initial-algebra : Initial (F-Algebras F)
  initial-algebra = record {
    ⊥ = record { A = A,α.carrier ; α = U.₁ inverse.arr } ;
    ⊥-is-initial =
      iso-recursive⇒initial
        A,α.to-Coalgebra
        A,α-recursive
        (record { inv = U.₁ inverse.arr ; iso = fixpoint }) }

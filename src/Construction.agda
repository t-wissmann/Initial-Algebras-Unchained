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
open import Accessible-Category using (Accessible)
open import CoalgColim
open import F-Coalgebra-Colimit
open import Data.Product
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Coalgebra
open import Categories.Functor.Properties using (Full)
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
  (𝒞-acc : Accessible 𝒞 (o ⊔ ℓ) ℓ ℓ Fil Fil-to-filtered)
  where

open import Coalgebra.Recursive 𝒞 F
open import Unique-Proj 𝒞 F Fil Fil-to-filtered
open import Categories.Morphism.Reasoning 𝒞
open import Lambek 𝒞 F

private
    module 𝒞 = Category 𝒞
    module 𝒞-acc = Accessible 𝒞-acc
    module F = Functor F
    module V = Functor (forget-Coalgebra {𝒞 = 𝒞} {F = F})


-- Here, we instantiate the diagram for the main colimit/construction:
-- We consider coalgebras whose carrier come from the family 𝒞-acc.fin
-- and which satisfy 'IsRecursive':
open import Coalgebra.IdxProp 𝒞 F 𝒞-acc.fin IsRecursive

module TerminalRecursive
       (carrier-colimit : Colimit forget-IdxPropCoalgebra)
       -- ^- the colimit of all recursive coalgebras with carrier in 𝒞-acc.fin
       (coalgebras-filtered : Fil IdxPropCoalgebras)
       -- ^- the assumption that above colimit is Fil(tered)
       (F-finitary : preserves-colimit forget-IdxPropCoalgebra F)
       where

  open import Iterate.Assumptions {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil
  open import Iterate {o' = o ⊔ ℓ} {ℓ' = ℓ} 𝒞 F Fil Fil-to-filtered 𝒞-acc
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
            finite-carrier = 𝒞-acc.fin-presentable (IdxPropCoalgebra.carrier i) ;
            is-recursive = IdxPropCoalgebra.has-prop i }
        ; cocone = F-Coalgebras-Lift-Cocone forget-IdxProp carrier-colimit
        ; carrier-colimitting = F-Coalgebras-Colimit-Carrier-Limitting forget-IdxProp carrier-colimit
        }
  module A,α = CoalgColim.CoalgColim A,α

  -- All coalgebras in the diagram for A,α are recursive, and so is A,α itself:
  A,α-recursive : IsRecursive A,α.to-Coalgebra
  A,α-recursive =
    Limitting-Cocone-IsRecursive A,α.D
      IdxPropCoalgebra.has-prop
      A,α.cocone A,α.carrier-colimitting

  -- Applying the Functor F to A,α again yields a locally finrec coalgebra:
  FA,Fα : CoalgColim 𝒞 F FiniteRecursive
  FA,Fα = iterate-CoalgColimit A,α coalgebras-filtered F-finitary
  module FA,Fα = CoalgColim.CoalgColim FA,Fα

  -- For the universal property of A,α , we use that the diagram
  -- scheme of A,α is full:
  A,α-scheme-Full : Full-≈ forget-IdxProp
  A,α-scheme-Full = record {
    preimage = λ X Y f → f ;
    preimage-prop = λ X Y f → Category.Equiv.refl 𝒞
    }

  -- Since the diagram scheme for A,α is full, we obtain that
  -- the colimit injections are the only coalgebra morphisms
  -- from coalgebras in the diagram to A,α:
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

  -- We can extend the above uniqueness property from the diagram scheme
  -- to all finrec coalgebras, so there is a unique coalgebra morphism from
  -- every finrec coalgebra to A,α:
  universal-property : ∀ (C : F-Coalgebra F) → FiniteRecursive C →
                         F-Coalgebras F [ C =∃!=> A,α.to-Coalgebra ]
  universal-property C C-finrec = record
    { arr = proj-j.arr ∘ C→Dj
    ; unique = λ h →
      let open HomReasoning in
      begin
      proj-j.arr ∘ C→Dj ≈⟨ pushˡ (proj-j.unique (h ∘ Dj→C)) ⟩
      h ∘ Dj→C ∘ C→Dj ≈⟨ elimʳ r.is-retract ⟩
      h
      ∎
    }
    where
      -- all compositions are on the level of coalgebra homomorphisms
      open Category (F-Coalgebras F)
      module C = F-Coalgebra C
      -- there is a split-mono to one of the presentable generators of 𝒞:
      split-mono : Σ[ idx ∈ 𝒞-acc.Idx ] (Retract 𝒞 C.A (𝒞-acc.fin idx))
      split-mono = 𝒞-acc.presentable-split-in-fin C.A
        (FiniteRecursive.finite-carrier C-finrec)
      j' = proj₁ split-mono
      r = proj₂ split-mono
      module r = Retract r
      -- and thus this gives us a coalgebra in the diagram of B,β:
      j : A,α.𝒟.Obj
      j = record {
        carrier = j' ;
        structure = F-Coalgebra.α (retract-coalgebra C r) ;
        has-prop = retract-coalgebra-recursive C r (FiniteRecursive.is-recursive C-finrec) }

      proj-j : F-Coalgebras F [ A,α.D.₀ j =∃!=> A,α.to-Coalgebra ]
      proj-j = A,α-proj-uniq j
      module proj-j = singleton-hom proj-j

      C→Dj : F-Coalgebras F [ C , A,α.D.₀ j ]
      C→Dj = retract-coalgebra-hom C r

      Dj→C : F-Coalgebras F [ A,α.D.₀ j , C ]
      Dj→C = retract-coalgebra-hom⁻¹ C r

  -- We furthermore lift this universal property from finrec to locally finrec coalgebras:
  -- There is a unique coalgebra morphism from every locally finrec coalgebra to A,α:
  universal-property-locally-finrec :
            ∀ {o' ℓ' e' : Level} (R : CoalgColim 𝒞 F FiniteRecursive {o'} {ℓ'} {e'}) →
            F-Coalgebras F [ CoalgColim.to-Coalgebra R =∃!=> A,α.to-Coalgebra ]
  universal-property-locally-finrec R =
    R.unique-homomorphism A,α.to-Coalgebra
      λ i → universal-property (R.D.₀ i) (R.all-have-prop {i})
    where module R = CoalgColim.CoalgColim R

  -- Applying this to A,α itself yields that there is only
  -- one endo-morphism on A,α:
  unique-endo : F-Coalgebras F [ A,α.to-Coalgebra =∃!=> A,α.to-Coalgebra ]
  unique-endo = A,α.unique-homomorphism A,α.to-Coalgebra A,α-proj-uniq
  module unique-endo = singleton-hom unique-endo

  -- From the locally finrec FA,Fα there is also a unique coalgebra
  -- morphism (for the fixpoint property, we only need existence)
  inverse : F-Coalgebras F [ FA,Fα.to-Coalgebra =∃!=> A,α.to-Coalgebra ]
  inverse = universal-property-locally-finrec FA,Fα
  module inverse = singleton-hom inverse

  -- By Lambek's Lemma, this yields that α is an isomorphism (in 𝒞):
  fixpoint : Iso 𝒞 A,α.structure (V.₁ inverse.arr)
  fixpoint = lambek A,α.to-Coalgebra
    (λ endo → unique-endo.unique₂ endo (Category.id (F-Coalgebras F) {A,α.to-Coalgebra}))
    inverse.arr

  -- A,α is recursive and has a structure that is an isomorphism,
  -- hence it is the initial F-Algebra:
  initial-algebra : Initial (F-Algebras F)
  initial-algebra = record {
    ⊥ = record { A = A,α.carrier ; α = V.₁ inverse.arr } ;
    ⊥-is-initial =
      iso-recursive⇒initial
        A,α.to-Coalgebra
        A,α-recursive
        (record { inv = V.₁ inverse.arr ; iso = fixpoint }) }

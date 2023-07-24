{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)

module recursive-coalgebra {o ℓ e} (C : Category o ℓ e) (F : Endofunctor C) where

open import Level

open import Categories.Functor.Coalgebra
open import Categories.Functor.Algebra hiding (iterate)
open import Categories.Category using (Category)
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Morphism using (IsIso; Iso; module ≅)
import Categories.Morphism
open import Categories.Object.Initial using (IsInitial)
open import Function.Equality using (cong)
open import Categories.Morphism.Reasoning

open import F-Coalgebra-Colimit
open import Unchained-Utils


-- We first recap some lemmas from:
--   [CUV06] Venanzio Capretta, Tarmo Uustalu, and Varmo Vene.
--           Recursive coalgebras from comonads.
--           Inf. Comput., 204(4):437–468, 2006.

record Solution {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C}
  (X : F-Coalgebra F)
  (Y : F-Algebra F) : Set (ℓ ⊔ e) where
  open Category C
  module X = F-Coalgebra X
  module Y = F-Algebra Y
  open Functor F
  field
    f : X.A ⇒ Y.A
    commutes : f ≈ Y.α ∘ F₁ f ∘ X.α

-- we can precompose solutions with coalgebra morphisms:
solution-precompose : {B D : F-Coalgebra F} → {A : F-Algebra F} →
  Solution D A → F-Coalgebra-Morphism B D → Solution B A
solution-precompose {B} {D} {A} sol mor =
  let
    open Category C
    module sol = Solution sol
    module mor = F-Coalgebra-Morphism mor
    module B = F-Coalgebra B
    module D = F-Coalgebra D
    module A = F-Algebra A
    open HomReasoning
    open Functor F
  in
  record
  { f = sol.f ∘ mor.f ;
  commutes = begin
    sol.f ∘ mor.f                     ≈⟨ sol.commutes ⟩∘⟨refl  ⟩
    (A.α ∘ F₁ sol.f ∘ D.α) ∘ mor.f     ≈⟨ assoc ⟩
    A.α ∘ (F₁ sol.f ∘ D.α) ∘ mor.f     ≈⟨ refl⟩∘⟨ assoc ⟩
    A.α ∘ F₁ sol.f ∘ D.α ∘ mor.f       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mor.commutes ⟩
    A.α ∘ F₁ sol.f ∘ F₁ mor.f ∘ B.α    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    A.α ∘ (F₁ sol.f ∘ F₁ mor.f) ∘ B.α  ≈˘⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
    A.α ∘ F₁ (sol.f ∘ mor.f) ∘ B.α
          ∎
  }

record IsRecursive (X : F-Coalgebra F) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  morph = Solution.f
  field
    -- there is at least one solution:
    recur : (B : F-Algebra F) → Solution X B
    -- there is at most one solution:
    unique : (B : F-Algebra F) → (g h : Solution X B) →
      morph g ≈ morph h

-- whenever a recursive coalgebra is an iso, it is the initial algebra:
-- [CUV06, Prop. 7(a)]
iso-recursive⇒initial :
  (R : F-Coalgebra F)
  → IsRecursive R
  → (r-iso : IsIso C (F-Coalgebra.α R))
  → IsInitial (F-Algebras F) (to-Algebra (IsIso.inv r-iso))
iso-recursive⇒initial R is-rec r-iso =
  let
    open Category C
    open HomReasoning
    r⁻¹ = IsIso.inv r-iso
    r = F-Coalgebra.α R
  in
  record
  { ! = λ {A : F-Algebra F} →
      let
        coalg2alg = IsRecursive.recur is-rec A
        a = F-Algebra.α A
        h : (F-Coalgebra.A R) ⇒ (F-Algebra.A A)
        h = Solution.f coalg2alg
        Fh = Functor.F₁ F h
      in
      record
        { f = h
        ; commutes = begin
          h ∘ r⁻¹
            ≈⟨  Solution.commutes coalg2alg ⟩∘⟨refl ⟩
          (a ∘ Fh ∘ r) ∘ r⁻¹   ≈⟨ assoc ⟩
          a ∘ ((Fh ∘ r) ∘ r⁻¹) ≈⟨ refl⟩∘⟨ assoc ⟩
          a ∘ Fh ∘ (r ∘ r⁻¹)
            ≈˘⟨ assoc ⟩
          (a ∘ Fh) ∘ (r ∘ r⁻¹)
            ≈⟨ refl⟩∘⟨ Iso.isoʳ (IsIso.iso r-iso) ⟩
          (a ∘ Fh) ∘ id
            ≈⟨ identityʳ ⟩
          a ∘ Fh
          ∎
        }
  ; !-unique = λ {A} g-hom →
    let
      g = (F-Algebra-Morphism.f g-hom)
      Fg = Functor.F₁ F g
      a = F-Algebra.α A
      -- we first show that 'g' is a coalg2algebra homomorphism
      g-coalg2alg : Solution R A
      g-coalg2alg = record {
        f = g ;
        commutes =
          begin
          g          ≈˘⟨ identityʳ ⟩
          g ∘ id      ≈˘⟨ refl⟩∘⟨ Iso.isoˡ (IsIso.iso r-iso) ⟩
          g ∘ (r⁻¹ ∘ r) ≈˘⟨ assoc ⟩
          (g ∘ r⁻¹) ∘ r ≈⟨ F-Algebra-Morphism.commutes g-hom ⟩∘⟨refl ⟩
          (a ∘ Fg) ∘ r ≈⟨ assoc ⟩
          a ∘ Fg ∘ r
          ∎
        }
      -- and thus, it has to be identical to h:
      h = IsRecursive.recur is-rec A
    in
    IsRecursive.unique is-rec A h g-coalg2alg
  }

-- Apply the functor F to the coalgebra carrier and structure:

module _ (R : F-Coalgebra F) (B : F-Coalgebra F) where
  -- ([CUV06, Prop. 5])
  open Category C
  private
    module R = F-Coalgebra R
    module B = F-Coalgebra B
    module F = Functor F

  sandwich-recursive :
    IsRecursive R
    → (h : F-Coalgebra-Morphism R B)
    → (g : F-Coalgebra-Morphism B (iterate R))
    → B.α ≈ F.F₁ (F-Coalgebra-Morphism.f h) ∘ (F-Coalgebra-Morphism.f g)
    → IsRecursive B
  sandwich-recursive R-is-rec h g equation =
    let
      module h = F-Coalgebra-Morphism h
      module g = F-Coalgebra-Morphism g
      open IsRecursive R-is-rec
    in
    record {
    recur = λ D →
      let
        -- for an F-algebra D, consider the induced solution by R:
        module D = F-Algebra D
        R2D = recur D
        module R2D = Solution R2D
        -- use this under the functor to get a solution from B to D:
        sol = D.α ∘ F.F₁ R2D.f ∘ g.f
        open HomReasoning
      in
      record {
      f = sol;
      commutes =
          -- in the following, the only non-trivial steps are R2D.commutes and g.commutes
          begin
          sol                        ≡⟨⟩
          D.α ∘ F.F₁ R2D.f ∘ g.f      ≈⟨ refl⟩∘⟨ F.F-resp-≈ R2D.commutes ⟩∘⟨refl ⟩
          D.α ∘ F.F₁ (D.α ∘ F.F₁ R2D.f ∘ R.α) ∘ g.f          ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ assoc ⟩∘⟨refl ⟩
          D.α ∘ F.F₁ ((D.α ∘ F.F₁ R2D.f) ∘ R.α) ∘ g.f        ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
          D.α ∘ (F.F₁ (D.α ∘ F.F₁ R2D.f) ∘ F.F₁ R.α) ∘ g.f   ≈⟨ refl⟩∘⟨ assoc ⟩
          D.α ∘ F.F₁ (D.α ∘ F.F₁ R2D.f) ∘ F.F₁ R.α ∘ g.f     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ g.commutes ⟩
          D.α ∘ F.F₁ (D.α ∘ F.F₁ R2D.f) ∘ F.F₁ g.f ∘ B.α     ≈˘⟨ refl⟩∘⟨ assoc ⟩
          D.α ∘ (F.F₁ (D.α ∘ F.F₁ R2D.f) ∘ F.F₁ g.f) ∘ B.α   ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
          D.α ∘ F.F₁ ((D.α ∘ F.F₁ R2D.f) ∘ g.f) ∘ B.α        ≈⟨ refl⟩∘⟨ F.F-resp-≈ assoc ⟩∘⟨refl ⟩
          D.α ∘ F.F₁ (D.α ∘ F.F₁ R2D.f ∘ g.f) ∘ B.α          ≡⟨⟩
          D.α ∘ F.F₁ sol ∘ B.α
          ∎
      } ;
    unique = λ D sol1 sol2 →
      let
        module D = F-Algebra D
        module sol1 = Solution sol1
        module sol2 = Solution sol2
        open HomReasoning
        -- first of all, the solutions are equal when precomposed with 'h: R -> B':
        sol1-h-is-sol2-h : sol1.f ∘ h.f ≈ sol2.f ∘ h.f
        sol1-h-is-sol2-h =
          IsRecursive.unique R-is-rec D
             (solution-precompose sol1 h)
             (solution-precompose sol2 h)

        -- this is essentially the reasoning: we do it forward for sol1 and
        -- backwards for sol2.
        sol-transformation sol =
          let
            module sol = Solution sol
          in
          begin
          sol.f            ≈⟨ sol.commutes ⟩
          D.α ∘ F.F₁ sol.f ∘ B.α  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ equation ⟩
          D.α ∘ F.F₁ sol.f ∘ F.F₁ h.f ∘ g.f  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          D.α ∘ (F.F₁ sol.f ∘ F.F₁ h.f) ∘ g.f  ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
          D.α ∘ F.F₁ (sol.f ∘ h.f) ∘ g.f
          ∎
      in
      begin
      sol1.f            ≈⟨ sol-transformation sol1 ⟩
      D.α ∘ F.F₁ (sol1.f ∘ h.f) ∘ g.f   ≈⟨ refl⟩∘⟨ F.F-resp-≈ sol1-h-is-sol2-h ⟩∘⟨refl ⟩
      D.α ∘ F.F₁ (sol2.f ∘ h.f) ∘ g.f  ≈˘⟨ sol-transformation sol2 ⟩
      sol2.f
      ∎
    }


-- Corollary: If (R,r) is recursive, then so is (FR,Fr) ([CUV06, Prop. 6]).
iterate-recursive : (R : F-Coalgebra F)
                    → IsRecursive R
                    → IsRecursive (iterate R)
iterate-recursive R is-rec =
  let
    module R = F-Coalgebra R
    g : F-Coalgebra-Morphism R (iterate R)
    g =
      let
        open Category C
        open Equiv
      in
      record { f = R.α ; commutes = refl }

    equation =
      let
        module FR = F-Coalgebra (iterate R)
        open Functor F
        open Category C
        open HomReasoning
      in
      begin
      FR.α ≈˘⟨ identityʳ ⟩
      F₁ R.α ∘ id
      ∎

    open Category (F-Coalgebras F)
  in
  sandwich-recursive R (iterate R) is-rec g id equation


record R-Coalgebra : Set (o ⊔ ℓ ⊔ e) where
  field
    coalg : F-Coalgebra F
    ump : IsRecursive coalg
  open F-Coalgebra coalg public
  open IsRecursive ump public

-- The recursive coalgebras form a full subcategory of F-Coalgebras:
R-Coalgebras : Category (ℓ ⊔ o ⊔ e) (e ⊔ ℓ) e
R-Coalgebras = FullSubCategory (F-Coalgebras F) R-Coalgebra.coalg
  where
    open import Categories.Category.SubCategory using (FullSubCategory)


module _ where

  open import Categories.Functor.Construction.SubCategory
  forget-rec : Functor (R-Coalgebras) (F-Coalgebras F)
  forget-rec = FullSub (F-Coalgebras F)

open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone
open import Categories.Functor using (_∘F_)

R-Coalgebras-Colimit : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D R-Coalgebras)
        → Colimit (forget-Coalgebra ∘F forget-rec ∘F  J) → Colimit J
R-Coalgebras-Colimit J C-colim =
  let
    module J = Functor J
    module C-colim = Colimit C-colim
    module F = Functor F
    Coalg-colim : Colimit (forget-rec ∘F J)
    Coalg-colim = F-Coalgebras-Colimit _ C-colim
    module Coalg-colim = Colimit Coalg-colim

    -- every F-Algebra induces a competing cocone for the above colimit:
    alg2cocone : F-Algebra F → Cocone (forget-Coalgebra ∘F forget-rec ∘F  J)
    alg2cocone B =
      let
            module B = F-Algebra B
      in
      record {
        N = B.A ;
        coapex = record {
          ψ = λ R →
            let
              module R = R-Coalgebra (J.F₀ R)
            in
            Solution.f (R.recur B) ;
          commute = λ {R} {R'} h →
            let
              -- h is a coalg-hom from R to R':
              module R = R-Coalgebra (J.F₀ R)
              module R' = R-Coalgebra (J.F₀ R')
              open Category C
              open HomReasoning
              open Equiv
              module h = F-Coalgebra-Morphism (J.F₁ h)
              module U = Functor (forget-Coalgebra ∘F forget-rec ∘F J)
              module U' = Functor (forget-rec ∘F J)
              -- we can use it to construct another solution from R to B:
              sol : Solution R.coalg B
              sol =
                let
                  module r' = Solution (R'.recur B)
                in
                record {
                f = r'.f ∘ U.F₁ h;
                commutes =
                begin
                r'.f ∘ U.F₁ h ≈⟨ r'.commutes ⟩∘⟨refl ⟩
                (B.α ∘ (F.F₁ r'.f ∘ R'.α)) ∘ U.F₁ h ≈⟨ assoc ⟩
                B.α ∘ ((F.F₁ r'.f ∘ R'.α) ∘ U.F₁ h) ≈⟨ refl⟩∘⟨ assoc ⟩
                B.α ∘ (F.F₁ r'.f ∘ (R'.α ∘ U.F₁ h)) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ h.commutes ⟩
                B.α ∘ (F.F₁ r'.f ∘ (F.F₁ (U.F₁ h) ∘ R.α)) ≈⟨ refl⟩∘⟨ sym-assoc ⟩
                B.α ∘ ((F.F₁ r'.f ∘ F.F₁ (U.F₁ h)) ∘ R.α) ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
                B.α ∘ F.F₁ (r'.f ∘ U.F₁ h) ∘ R.α
                ∎
                }
            in
            R.unique B sol (R.recur B)
        } }
    --
    -- the induced solution for an algebra
    alg2solution : (B : F-Algebra F) → Solution Coalg-colim.coapex B
    alg2solution B =
      let
        module B = F-Algebra B
        open Category C
        open HomReasoning

        sol : C [ F-Coalgebra.A Coalg-colim.coapex , B.A ]
        sol = C-colim.rep (alg2cocone B)
      in
      record { f = sol ;
        commutes = colimit-is-jointly-epic (forget-Coalgebra ∘F forget-rec ∘F  J) C-colim B.A sol (B.α ∘ F.F₁ sol ∘ F-Coalgebra.α Coalg-colim.coapex)
          λ A →
            begin
            sol ∘ C-colim.proj A ≈⟨ {!!} ⟩
            (B.α ∘ F.F₁ sol ∘ F-Coalgebra.α Coalg-colim.coapex) ∘ C-colim.proj A
            ∎
          }

    -- we can then show that the colimit coalgebra must be recursive:
    R : R-Coalgebra
    R = record {
      coalg = Coalg-colim.coapex ;
      ump = {!!} }
  in
  FullSub-Colimit R-Coalgebra.coalg J Coalg-colim R (≅.refl (F-Coalgebras F))
  -- record {initial = record {
  -- ⊥ = record {
  --   N = record {
  --     coalg = {!!} ;
  --     ump = {!!} } ;
  --   coapex = {!!} } ;
  -- ⊥-is-initial = {!!}
  -- }}

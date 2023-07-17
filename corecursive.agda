open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)

module corecursive {o ℓ e} (C : Category o ℓ e) (F : Endofunctor C) where

open import Level

open import Categories.Functor.Coalgebra
open import Categories.Functor.Algebra
open import Categories.Category using (Category)
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Morphism using (IsIso; Iso)
open import Categories.Object.Initial using (IsInitial)
open import Function.Equality using (cong)
open import Categories.Morphism.Reasoning

record Coalg-to-Alg-Morphism {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C}
  (X : F-Coalgebra F)
  (Y : F-Algebra F) : Set (ℓ ⊔ e) where
  open Category C
  module X = F-Coalgebra X
  module Y = F-Algebra Y
  open Functor F
  field
    f : X.A ⇒ Y.A
    commutes : f ≈ Y.α ∘ F₁ f ∘ X.α


record IsRecursive (X : F-Coalgebra F) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  morph = Coalg-to-Alg-Morphism.f
  field
    recur : (B : F-Algebra F) → Coalg-to-Alg-Morphism X B
    unique : (B : F-Algebra F) → (g h : Coalg-to-Alg-Morphism X B) →
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
        h = Coalg-to-Alg-Morphism.f coalg2alg
        Fh = Functor.F₁ F h
      in
      record
        { f = h
        ; commutes = begin
          h ∘ r⁻¹
            ≈⟨  Coalg-to-Alg-Morphism.commutes coalg2alg ⟩∘⟨refl ⟩
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
      g-coalg2alg : Coalg-to-Alg-Morphism R A
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
F-of-coalgebra : F-Coalgebra F → F-Coalgebra F
F-of-coalgebra Aα = record { A = F₀ A ; α = F₁ α }
  where
    open Functor F
    open F-Coalgebra Aα


module sandwhich-corecursive (R : F-Coalgebra F) (B : F-Coalgebra F) where
  -- ([CUV06, Prop. 5])
  open Category C
  private
    module R = F-Coalgebra R
    module B = F-Coalgebra B
    module F = Functor F

  sandwich-corecursive :
    IsRecursive R
    → (h : F-Coalgebra-Morphism R B)
    → (g : F-Coalgebra-Morphism B (F-of-coalgebra R))
    → B.α ≈ F.F₁ (F-Coalgebra-Morphism.f h) ∘ (F-Coalgebra-Morphism.f g)
    → IsRecursive B
  sandwich-corecursive R-is-rec h-morph g-morph equation =
    let
      module h = F-Coalgebra-Morphism h-morph
      module g = F-Coalgebra-Morphism g-morph
      open IsRecursive R-is-rec
    in
    record {
    recur = λ D →
      let
        -- for an F-algebra D, consider the induced solution by R:
        module D = F-Algebra D
        R2D = recur D
        module R2D = Coalg-to-Alg-Morphism R2D
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
    unique = λ D sol1 sol2 → {!!}
    }

-- The error message of agda:
-- ...agda/corecursive.agda:116,12-13
-- Not in scope:
--   ⇒
--   at ...agda/corecursive.agda:116,12-13
--     (did you mean
--        'Categories.Category.Category._⇒_' or
--        'Category._⇒_'?)
-- when scope checking ⇒

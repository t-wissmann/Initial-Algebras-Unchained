open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)

module corecursive {o ℓ e} (C : Category o ℓ e) (F : Endofunctor C) where

open import Level

open import Categories.Functor.Coalgebra
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.Morphism using (IsIso)
open import Categories.Object.Initial using (IsInitial)


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
--
iso-recursive⇒initial :
  (R : F-Coalgebra F)
  → IsRecursive R
  → (iso : IsIso C (F-Coalgebra.α R))
  → IsInitial (F-Algebras F) (to-Algebra (IsIso.inv iso))
iso-recursive⇒initial R is-rec iso =
  let
    open Category C
    open HomReasoning
    alg = IsIso.inv iso
  in
  record
  { ! = λ {A : F-Algebra F} →
      let
        coalg2alg = IsRecursive.recur is-rec A
        h : (F-Coalgebra.A R) ⇒ (F-Algebra.A A)
        h = Coalg-to-Alg-Morphism.f coalg2alg
      in
      record
        { f = h
        ; commutes = begin
          (h ∘ alg) ≈⟨ {!!} ⟩
          (F-Algebra.α A) ∘ (Functor.F₁ F h)
          ∎
        }
  ; !-unique = {!!}
  }

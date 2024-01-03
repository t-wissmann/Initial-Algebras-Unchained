{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level

module FinCoequalizer where

open import Data.Product
open import Data.Sum.Base
open import Relation.Binary
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqClos
open import Relation.Binary.PropositionalEquality.Core
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Bool.Base
open import Function using (_∋_)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core using (dec-true; from-yes)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.Properties
import Relation.Binary.Reasoning.Base.Single as RelationR

record EndoCoequalize {ℓ} {Y : Set} (R : Rel Y ℓ) : Set ℓ where
  field
    f : Y → Y
    identify-R : ∀ (y₁ y₂ : Y) → R y₁ y₂ → f y₁ ≡ f y₂
    reflect-f : ∀ (y : Y) → EqClosure R y (f y)

SpanRel : {X : Set} {Y : Set} (g h : X → Y) → Rel Y 0ℓ
SpanRel {X} {Y} g h = λ y-g y-h → Σ[ x ∈ X ](g x ≡ y-g   ×   h x ≡ y-h)

shift : {k : ℕ} {Y : Set} → (Fin (ℕ.suc k) → Y) → (Fin k → Y)
shift gh i = gh (Fin.suc i)

shift-SpanRel : {k : ℕ} {Y : Set} (g h : Fin (ℕ.suc k) → Y) → (SpanRel (shift g) (shift h)) ⇒ (SpanRel g h)
shift-SpanRel {k} {Y} g h {y₁} {y₂} (i , g-prop , h-prop) = Fin.suc i , g-prop , h-prop

finite-coequalize : (k : ℕ) (Y : Set) → Decidable (_≡_ {_} {Y}) → (g h : Fin k → Y) → EndoCoequalize (SpanRel g h)
finite-coequalize ℕ.zero Y Y≡-dec g h =
  record {
    f = λ x → x ;
    identify-R = λ {y₁ y₂ (() , (gx , hx)) } ;
    reflect-f = λ y → ε
    }
finite-coequalize (ℕ.suc k) Y Y≡-dec g h =
  record {
    f = f ;
    identify-R = identify-R ;
    reflect-f = reflect-f
  }
  where
    nested : EndoCoequalize (SpanRel (shift g) (shift h))
    nested = finite-coequalize k Y Y≡-dec (shift g) (shift h)
    module nested = EndoCoequalize nested

    _==_ : Y → Y → Bool
    _==_ x y = Dec.does (Y≡-dec x y)

    f' : Y → Y
    f' fy with (fy == nested.f (g Fin.zero))
    ...    | true = nested.f (h Fin.zero)
    ...    | false = fy
    -- ^-- in the new 'f', we send all elements of the equivalence class
    --     of g0 to the equivalence class to h0
    f : Y → Y
    f y = f' (nested.f y)

    ==-correct : {y₁ y₂ : Y} → y₁ ≡ y₂ → y₁ == y₂ ≡ true
    ==-correct {y₁} {y₂} eq = dec-true (Y≡-dec y₁ y₂) eq

    ==-reflect : {y₁ y₂ : Y} → y₁ == y₂ ≡ true → y₁ ≡ y₂
    ==-reflect {y₁} {y₂} eq = from-yes {!eq!} -- dec-true (Y≡-dec y₁ y₂) eq

    g0-prop : {y : Y} → g Fin.zero ≡ y → (nested.f y == nested.f (g Fin.zero)) ≡ true
    g0-prop {y} eq = ==-correct (cong nested.f (sym eq))
    h0-prop : {y : Y} → h Fin.zero ≡ y → f y ≡ nested.f (h Fin.zero)
    h0-prop {y} eq with (nested.f y == nested.f (g Fin.zero))
    ... | true = refl
    ... | false rewrite eq = refl

    identify-R : (y₁ y₂ : Y) → SpanRel g h y₁ y₂ → f y₁ ≡ f y₂
    identify-R y₁ y₂ (Fin.zero , g0=y₁ , h0=y₂) rewrite (g0-prop  g0=y₁) =
      let
        open ≡-Reasoning
      in
      begin
      (nested.f (h Fin.zero)) ≡⟨ sym (h0-prop h0=y₂) ⟩
      f y₂
      ∎
    identify-R y₁ y₂ (Fin.suc k' , gk=y₁ , hk=y₂) =
      cong f' (nested.identify-R y₁ y₂ (k' , (gk=y₁ , hk=y₂)))

    reflect-f : (y : Y) → EqClosure (SpanRel g h) y (f y)
    reflect-f y with (nested.f y == nested.f (g Fin.zero))
    ... | true = (EqClosure (SpanRel g h) y (nested.f (h Fin.zero))) ∋
                 let
                   g↙↘h = SpanRel g h
                   R = EqClosure g↙↘h
                   open RelationR R (EqClos.reflexive g↙↘h) (EqClos.transitive g↙↘h)
                   nested-f-prop : ∀ (z : Y) → EqClosure (SpanRel g h) z (nested.f z)
                   nested-f-prop z = EqClos.map (shift-SpanRel g h) (nested.reflect-f z)
                   fy=fg0 : nested.f y ≡ nested.f (g Fin.zero)
                   fy=fg0 = ==-reflect {!!}
                 in
                 begin
                 y                        ∼⟨ nested-f-prop y ⟩
                 nested.f y               ≡⟨ fy=fg0 ⟩
                 nested.f (g Fin.zero)    ∼⟨ EqClos.symmetric g↙↘h (nested-f-prop _) ⟩
                 g Fin.zero               ∼⟨ return (inj₁ (Fin.zero , (refl , refl))) ⟩
                 h Fin.zero               ∼⟨ nested-f-prop _ ⟩
                 nested.f (h Fin.zero)
                 ∎
    ... | false = EqClosure (SpanRel g h) y (nested.f y) ∋
                  EqClos.map (shift-SpanRel g h) (nested.reflect-f y)

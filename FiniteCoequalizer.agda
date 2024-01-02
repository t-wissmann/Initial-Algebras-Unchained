{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level

module FiniteCoequalizer where

open import Data.Product
open import Relation.Binary
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.PropositionalEquality.Core
open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Bool.Base
open import Relation.Nullary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.Properties

record EndoCoequalize {ℓ} {Y : Set} (R : Rel Y ℓ) : Set ℓ where
  field
    f : Y → Y
    identify-R : ∀ (y₁ y₂ : Y) → R y₁ y₂ → f y₁ ≡ f y₂
    reflect-f : ∀ (y : Y) → EqClosure R y (f y)

SpanRel : {X : Set} {Y : Set} (g h : X → Y) → Rel Y 0ℓ
SpanRel {X} {Y} g h = λ y-g y-h → Σ[ x ∈ X ](g x ≡ y-g   ×   h x ≡ y-h)

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
    identify-R = {!!} ;
    reflect-f = {!!}
  }
  where
    shift : (Fin (ℕ.suc k) → Y) → (Fin k → Y)
    shift gh i = gh (Fin.suc i)

    nested : EndoCoequalize (SpanRel (shift g) (shift h))
    nested = finite-coequalize k Y Y≡-dec (shift g) (shift h)
    module nested = EndoCoequalize nested

    _==_ : Y → Y → Bool
    _==_ x y = Dec.does (Y≡-dec x y)

    f : Y → Y
    f y with (nested.f y == nested.f (g Fin.zero))
    ...    | true = nested.f (h Fin.zero)
    ...    | false = nested.f y
    -- ^-- in the new 'f', we send all elements of the equivalence class
    --     of g0 to the equivalence class to h0

    g0-prop : {y : Y} → g Fin.zero ≡ y → (nested.f y == nested.f (g Fin.zero)) ≡ true
    g0-prop {y} eq = {!!}
    h0-prop : {y : Y} → h Fin.zero ≡ y → f y ≡ nested.f (h Fin.zero)
    h0-prop {y} eq with (nested.f y == nested.f (g Fin.zero))
    ... | true = refl
    ... | false rewrite eq = refl

    open ≡-Reasoning
    identify-R : (y₁ y₂ : Y) → SpanRel g h y₁ y₂ → f y₁ ≡ f y₂
    identify-R y₁ y₂ (Fin.zero , g0=y₁ , h0=y₂) rewrite (g0-prop  g0=y₁) =
      begin
      (nested.f (h Fin.zero)) ≡⟨ sym (h0-prop h0=y₂) ⟩
      f y₂
      ∎
      -- with (nested.f y₁ == nested.f (g Fin.zero))
      --... | true =
      --  begin
      --  (nested.f (h Fin.zero)) ≡⟨ {!!} ⟩
      --  f y₂
      --  ∎
      --... | false = {!!}
      -- let open ≡-Reasoning in
      -- begin
      -- f y₁ ≡⟨ {!!} ⟩
      -- (nested.f (h Fin.zero)) ≡⟨ {!!} ⟩
      -- f y₂
      -- ∎
    identify-R y₁ y₂ (Fin.suc k , gk=y₁ , hk=y₂) = {!!}

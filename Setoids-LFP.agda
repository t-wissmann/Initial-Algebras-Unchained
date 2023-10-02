{-# OPTIONS --without-K --allow-unsolved-metas #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Hom
open import Filtered
open import LFP
open import Data.Nat.Base using (ℕ)
open import Data.Fin
open import Data.Product
open import Function.Equality hiding (setoid; _∘_; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Binary.PropositionalEquality using (→-to-⟶)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Functor.Construction.LiftSetoids
import Relation.Binary.Reasoning.Setoid as SetoidR


open import Setoids-Colimit
open import Setoids-Choice

module Setoids-LFP where

private
  variable
    -- levels for setoids themselves:
    o ℓ : Level

-- -- we use a custom 'setoid' variation to achieve arbitrary levels o, ℓ
-- ≡-setoid : ∀ {o ℓ : Level} → Set 0ℓ → Setoid o ℓ
-- ≡-setoid {o} {ℓ} X =
--   record { Carrier = Lift o X
--   ; _≈_ = λ (lift x₁) (lift x₂) → L.Lift ℓ (x₁ ≡ x₂)
--   ; isEquivalence =
--     record {
--       refl = Level.lift refl ;
--       sym = λ (L.lift eq) → Level.lift (sym eq) ;
--       trans = λ (L.lift x≡y) (L.lift y≡z) → Level.lift (trans x≡y y≡z) } }

Fin≈ : ℕ → Setoid 0ℓ 0ℓ
Fin≈ n = setoid (Fin n)

Fin≈-zero-empty : {ℓ-a : Level} {a : Set ℓ-a} → Fin 0 → a
Fin≈-zero-empty ()

Fin-is-presented : ∀ (n : ℕ) → presented (Setoids 0ℓ 0ℓ) 0ℓ 0ℓ 0ℓ filtered (Fin≈ n)
Fin-is-presented n 𝒟 𝒟-filtered J colim =
  -- see where-clause at the end
  bounded-colimiting
    (lift-hom-n ∘F J)
    (F-map-Coconeˡ lift-hom-n (colim.colimit))
    𝒟-filtered.bounds
    (λ (lift f) →
      let
        -- f is essentially a tuple of elements of the colimit:
        _ : Fin n → Setoid.Carrier colim.coapex
        _ = λ k → f ⟨$⟩ k
        -- since 'colim' is a colimit in setoids, every element
        -- of the family 'f' comes from some object in the diagram
        source-objects : Fin n → 𝒟.Obj
        source-objects k = proj₁ (colimit-choice colim (f ⟨$⟩ k))

        -- the diagram is filtered, so these objects have an upper bound:
        B : 𝒟.Obj
        B = 𝒟-filtered.fin-upper-bound source-objects

        -- and so f factors through it:
        g : Fin n → Setoid.Carrier (J.₀ B)
        g k =
          J.₁ (𝒟-filtered.fin-is-above source-objects k)
          ⟨$⟩ proj₂ (colimit-choice colim (f ⟨$⟩ k))


        open Setoid renaming (_≈_ to _[[_≈_]])
        g-correct : (k : Fin n) → colim.coapex [[ (f ⟨$⟩ k) ≈ colim.proj B ⟨$⟩ (g k) ]]
        g-correct k =
          let
            open SetoidR (colim.coapex)
            X , xₖ = colimit-choice colim (f ⟨$⟩ k)
            connecting-morph = 𝒟-filtered.fin-is-above source-objects k
          in
          begin
          (f ⟨$⟩ k)                   ≈⟨ colimit-choice-correct colim ⟩
          colim.proj X ⟨$⟩ xₖ         ≈˘⟨ colim.colimit-commute connecting-morph (Setoid.refl (J.₀ X)) ⟩
          (colim.proj B ∘ J.₁ connecting-morph) ⟨$⟩ xₖ        ≡⟨⟩
          colim.proj B ⟨$⟩ (J.₁ connecting-morph ⟨$⟩ xₖ)       ≡⟨⟩
          colim.proj B ⟨$⟩ (g k)
          ∎

        g≈ : Fin≈ n ⇒ J.₀ B
        g≈ = →-to-⟶ g
      in
      record {
        i = B ;
        preimage = Level.lift g≈ ;
        x-sent-to-c = Level.lift (λ {k} {k'} eq →
          let
            open SetoidR (colim.coapex)
          in
          begin
          (colim.proj B ∘ g≈ ∘ id) ⟨$⟩ k ≡⟨⟩
          colim.proj B ⟨$⟩ (g k) ≈˘⟨ g-correct k ⟩
          f ⟨$⟩ k ≈⟨ Π.cong f eq ⟩
          f ⟨$⟩ k'
          ∎
          )
        })
    λ {i} kp →
      let
        module kp = KernelPairs kp
        F-colim = F-map-Coconeˡ (LiftSetoids 0ℓ 0ℓ ∘F Hom.Hom[ Setoids 0ℓ 0ℓ ,-] (Fin≈ n)) colim.colimit
        module F-colim = Cocone (F-colim)
        -- we are given two tuples:
        f : Fin≈ n ⇒ J.₀ i
        f = Lift.lower kp.pr₁
        g : Fin≈ n ⇒ J.₀ i
        g = Lift.lower kp.pr₂
        -- which are identified in the cocone
        open Setoid renaming (_≈_ to _[[_≈_]])
        F-identified : F-colim.N [[ F-colim.ψ i ⟨$⟩ kp.pr₁ ≈ F-colim.ψ i ⟨$⟩ kp.pr₂ ]]
        F-identified = kp.identified
        -- expanding the definition of F yields:
        identified : hom-setoid [[ colim.proj i ∘ f ∘ id ≈ colim.proj i ∘ g ∘ id ]]
        identified = Lift.lower kp.identified

        i' , ( h , eq ) = induction n i f g identified
      in
      record { B = i' ; inj₁ = h ; inj₂ = h ; identifies = Level.lift eq }
  where
    open Hom (Setoids 0ℓ 0ℓ)
    hom-n = Hom[ (Fin≈ n) ,-]
    lift-hom-n = LiftSetoids 0ℓ 0ℓ ∘F hom-n
    module colim = Colimit colim
    open Category (Setoids 0ℓ 0ℓ)
    module 𝒟 = Category 𝒟
    module J = Functor J
    module 𝒟-filtered = filtered 𝒟-filtered
    open Setoid renaming (_≈_ to _[[_≈_]])
    induction : ∀ (k : ℕ) (j : Category.Obj 𝒟) →
                  (s t : Fin≈ k ⇒ J.₀ j) →
                  hom-setoid [[ colim.proj j ∘ s ≈ colim.proj j ∘ t ]] →
                  Σ[ j' ∈ 𝒟.Obj ] (Σ[ h ∈ j 𝒟.⇒ j' ] ( hom-setoid [[ J.₁ h ∘ s ≈ J.₁ h ∘ t ]]))
    induction ℕ.zero j s t eq-proj = j , (𝒟.id , (λ {k} _ → Fin≈-zero-empty k ))
    induction (ℕ.suc k) j s t eq-proj =
      let
        -- the elements s 0 and t 0 are identified in the colimit:
        proj-identifies-0 : colim.coapex [[ colim.proj j ⟨$⟩ (s ⟨$⟩ Fin.zero) ≈ colim.proj j ⟨$⟩ (t ⟨$⟩ Fin.zero) ]]
        proj-identifies-0 = eq-proj (Setoid.refl (Fin≈ (ℕ.suc k)))

        -- and so s 0 and t 0 are identified somewhere in the diagram:
        ident-in-dia-0 : identified-in-diagram J (s ⟨$⟩ Fin.zero) (t ⟨$⟩ Fin.zero)
        ident-in-dia-0 = filtered-identification-colim J colim 𝒟-filtered proj-identifies-0
        module ident-in-dia-0 = identified-in-diagram ident-in-dia-0
        j-0 = 𝒟-filtered.fuse-obj ident-in-dia-0.inj₁ ident-in-dia-0.inj₂
        h-0 : j 𝒟.⇒ j-0
        h-0 =
          (𝒟-filtered.fuse-morph ident-in-dia-0.inj₁ ident-in-dia-0.inj₂)
          𝒟.∘ ident-in-dia-0.inj₁

        -- we restrict s/t/eq-ref to the other components in order to apply the I.H. to them:
        s-suc : Fin≈ k ⇒ J.₀ j
        s-suc = →-to-⟶ (λ m → s ⟨$⟩ Fin.suc m)
        t-suc : Fin≈ k ⇒ J.₀ j
        t-suc = →-to-⟶ (λ m → t ⟨$⟩ Fin.suc m)
        eq-proj-suc : hom-setoid [[ colim.proj j ∘ s-suc ≈ colim.proj j ∘ t-suc ]]
        eq-proj-suc = λ {refl → eq-proj (Setoid.refl (Fin≈ (ℕ.suc k)))}
        -- the induction hypothesis:
        j-suc , (h-suc , ident-in-dia-suc) = induction k j s-suc t-suc eq-proj-suc

        -- we can combine the two morphisms for 0 and the I.H.:
        j = 𝒟-filtered.close-span-obj h-0 h-suc
        h =
          (𝒟-filtered.close-span-morph₂ h-0 h-suc)
          𝒟.∘ h-suc
        -- so J.₀ j is the object in the diagram in which
        -- s and t are identified and h is the morphism identifying both
        open SetoidR (J.₀ j)
      in
      j , h , λ { -- case distinction: so we have either s0/t0 or s-suc/t-suc
        {Fin.zero} refl →
          begin
          (J.₁ h ∘ s) ⟨$⟩ Fin.zero ≈⟨ {!!} ⟩
          (J.₁ h ∘ t) ⟨$⟩ Fin.zero
          ∎
      ; {Fin.suc m} refl →
          begin
          (J.₁ h ∘ s) ⟨$⟩ Fin.suc m ≈⟨ {!!} ⟩
          (J.₁ h ∘ t) ⟨$⟩ Fin.suc m
          ∎
      }


setoids-LFP : WeaklyLFP (Setoids 0ℓ 0ℓ) 0ℓ 0ℓ 0ℓ filtered
setoids-LFP = record {
  Idx = ℕ ;
  fin = Fin≈ ;
  fin-presented = Fin-is-presented ;
  build-from-fin = λ X → {!!}
  }

{-# OPTIONS --without-K --safe #-}
open import Level
import Level as L


open import Relation.Binary using (Setoid)
open import Categories.Category.Instance.Setoids

open import Categories.Category
open import Categories.Category.Lift
open import Categories.Functor hiding (id)
open import Categories.Functor.Hom
open import Filtered
open import Data.Nat using (ℕ)
import Data.Nat
import Data.Sum.Base as Sum
open import Relation.Binary.Core using (Rel)
open import Data.Fin hiding (lift)
open import Data.Fin.Instances using (Fin-≡-isDecEquivalence)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-↑ˡ; splitAt-↑ʳ; splitAt-raise)
open import Data.Product
-- open import Function.Equality hiding (setoid; _∘_; cong) renaming (id to ⟶id)
open import Function.Bundles
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (cong; refl)
open import Relation.Binary.PropositionalEquality.Properties
-- open import Relation.Binary.PropositionalEquality using (→-to-⟶)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Functor.Construction.LiftSetoids
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Bundles
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)


open import Setoids-Colimit
open import Setoids-Choice
open import Colimit-Lemmas
open import Hom-Colimit-Choice
open import FinCoequalizer

module Setoids-Accessible where

private
  -- WARNING: it seems to be impossible to raise the levels of the diagrams! Even
  -- if the colimit of a diagram scheme from a higher level exists, it is impossible
  -- to apply the Setoids-Choice principle!
  Setoids' = Setoids 0ℓ 0ℓ

id-filtered : ∀ {o ℓ e : Level} {𝒟} → filtered {o} {ℓ} {e} 𝒟 → filtered {o} {ℓ} {e} 𝒟
id-filtered f = f

→-to-⟶ : ∀ {a b ℓ : Level} {A : Set a} {B : Setoid b ℓ} →
         (A → Setoid.Carrier B) → Func (setoid A) B
→-to-⟶ {B = B} f = record
  { to = f
  ; cong = λ {refl → Setoid.refl B }
  }

const : ∀ {a b ℓ : Level} {A : Set a} {B : Setoid b ℓ} →
         Setoid.Carrier B → Func (setoid A) B
const x = →-to-⟶ (λ _ → x)

open import Canonical-Cocone Setoids'
open import Accessible-Category Setoids' 0ℓ 0ℓ 0ℓ filtered id-filtered
open import Presentable Setoids' 0ℓ 0ℓ 0ℓ filtered
open import Categories.Category.Slice Setoids'
open LiftHom Setoids' 0ℓ 0ℓ 0ℓ

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

Fin-is-presentable : ∀ (n : ℕ) → presentable (Fin≈ n)
Fin-is-presentable n 𝒟 𝒟-filtered J colim =
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
          f ⟨$⟩ k ≈⟨ Func.cong f eq ⟩
          f ⟨$⟩ k'
          ∎
          )
        })
    λ {i} kp →
      let
        module kp = KernelPairs kp
        F-colim = F-map-Coconeˡ (LiftHom[ (Fin≈ n) ,-] ) colim.colimit
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
    open Hom (Setoids')
    hom-n = Hom[ (Fin≈ n) ,-]
    lift-hom-n = LiftHom[ (Fin≈ n) ,-]
    module colim = Colimit colim
    open Category (Setoids')
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
        M = 𝒟-filtered.merge-all ident-in-dia-0.inj₁ ident-in-dia-0.inj₂
        module M = MergedMorphisms M
        j-0 = M.tip
        coeq = M.merge
        coeq-prop = M.prop
        h-0 : j 𝒟.⇒ j-0
        h-0 = coeq 𝒟.∘ ident-in-dia-0.inj₁

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
        closed = 𝒟-filtered.close-span h-0 h-suc
        module closed = ClosedSpan closed
        j' = closed.tip
        h-inj₁ = closed.close-fst
        h-inj₂ = closed.close-snd
        h : j 𝒟.⇒ j'
        h = h-inj₁ 𝒟.∘ h-0

        -- J-expand-0 : hom-setoid [[ J.₁ h ≈ J.₁ h-inj₁ ∘ J.₁ coeq ∘ J.₁ ident-in-dia-0.inj₁ ]]
        -- J-expand-0 = let open HomReasoning in
        --   begin
        --   J.₁ h ≈⟨ J.homomorphism ⟩
        --   J.₁ h-inj₁ ∘ J.₁ h-0 ≈⟨ (refl⟩∘⟨ J.homomorphism) ⟩
        --   J.₁ h-inj₁ ∘ J.₁ coeq ∘ J.₁ ident-in-dia-0.inj₁
        --   ∎

        open SetoidR (J.₀ j')
        refl-j = (Setoid.refl (J.₀ j))
      in
      j' , h , λ { -- case distinction: so we have either s0/t0 or s-suc/t-suc
        {Fin.zero} refl →
          begin
          (J.₁ h ∘ s) ⟨$⟩ Fin.zero ≡⟨⟩
          J.₁ h ⟨$⟩ (s ⟨$⟩ Fin.zero) ≈⟨ J.homomorphism refl-j ⟩
          J.₁ h-inj₁ ⟨$⟩  (J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₁) ⟨$⟩ (s ⟨$⟩ Fin.zero)) ≈⟨ Func.cong (J.₁ h-inj₁) (J.homomorphism refl-j) ⟩
          (J.₁ h-inj₁ ∘ J.₁ coeq) ⟨$⟩ (J.₁ ident-in-dia-0.inj₁ ⟨$⟩ (s ⟨$⟩ Fin.zero)) ≈⟨ Func.cong (J.₁ h-inj₁ ∘ J.₁ coeq) ident-in-dia-0.identifies ⟩
          (J.₁ h-inj₁ ∘ J.₁ coeq) ⟨$⟩ (J.₁ ident-in-dia-0.inj₂ ⟨$⟩ (t ⟨$⟩ Fin.zero)) ≈˘⟨ Func.cong (J.₁ h-inj₁) (J.homomorphism refl-j) ⟩
          (J.₁ h-inj₁ ∘ J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₂)) ⟨$⟩ (t ⟨$⟩ Fin.zero) ≈˘⟨ Func.cong (J.₁ h-inj₁) (J.F-resp-≈ coeq-prop refl-j) ⟩
          (J.₁ h-inj₁ ∘ J.₁ (coeq 𝒟.∘ ident-in-dia-0.inj₁)) ⟨$⟩ (t ⟨$⟩ Fin.zero) ≈˘⟨ J.homomorphism refl-j ⟩
          (J.₁ (h-inj₁ 𝒟.∘ coeq 𝒟.∘ ident-in-dia-0.inj₁)) ⟨$⟩ (t ⟨$⟩ Fin.zero) ≡⟨⟩
          (J.₁ h ∘ t) ⟨$⟩ Fin.zero
          ∎
      ; {Fin.suc m} refl →
          begin
          (J.₁ h ∘ s) ⟨$⟩ Fin.suc m ≡⟨⟩
          (J.₁ (h-inj₁ 𝒟.∘ h-0) ∘ s) ⟨$⟩ Fin.suc m ≈⟨ J.F-resp-≈ closed.commutes refl-j ⟩
          (J.₁ (h-inj₂ 𝒟.∘ h-suc) ∘ s) ⟨$⟩ Fin.suc m ≈⟨ J.homomorphism refl-j ⟩
          J.₁ h-inj₂ ⟨$⟩ (J.₁ h-suc ⟨$⟩ (s ⟨$⟩ Fin.suc m)) ≈⟨ Func.cong (J.₁ h-inj₂) (ident-in-dia-suc (Setoid.refl (Fin≈ k))) ⟩
          J.₁ h-inj₂ ⟨$⟩ (J.₁ h-suc ⟨$⟩ (t ⟨$⟩ Fin.suc m)) ≈˘⟨ J.homomorphism refl-j ⟩
          (J.₁ (h-inj₂ 𝒟.∘ h-suc) ∘ t) ⟨$⟩ Fin.suc m ≈˘⟨ J.F-resp-≈ closed.commutes refl-j ⟩
          (J.₁ (h-inj₁ 𝒟.∘ h-0) ∘ t) ⟨$⟩ Fin.suc m ≡⟨⟩
          (J.₁ h ∘ t) ⟨$⟩ Fin.suc m
          ∎
      }

canonical-cocone-is-limitting : ∀ (X : Setoid 0ℓ 0ℓ) → IsLimitting (Cocone[ Fin≈ ↓ X ])
canonical-cocone-is-limitting X =
  let
    open Setoid renaming (_≈_ to _[[_≈_]]) hiding (sym)
    CanCocone = Cocone[ Fin≈ ↓ X ]
    module F = Functor (Functor[ Fin≈ ↓ X ])
    open Category (Setoids 0ℓ 0ℓ)

    t : (Setoid.Carrier X) → Category.Obj (Cat[ Fin≈ ↓ X ])
    t x = (1 , const x)

    ! : (C : Cocone (Functor[ Fin≈ ↓ X ])) → Cocone⇒ _ CanCocone C
    ! C =
      let
        module C = Cocone C
        underlying : (Setoid.Carrier X)  → (Setoid.Carrier C.N)
        underlying x = C.ψ (t x) ⟨$⟩ Fin.zero
      in
      record {
      arr = record {
        to = underlying
           ;
        cong = λ {x} {x'} x≈x' →
          let
            -- f : Slice⇒ (sliceobj (const x)) (sliceobj (const x'))
            f : (Cat[ Fin≈ ↓ X ]) [ t x , t x' ]
            f = slicearr
                  {h = id}
                  λ { {Fin.zero} {Fin.zero} refl → Setoid.sym X x≈x'}
            eq : C.ψ (t x) ≈ C.ψ (t x') ∘ F.₁ f
            eq =
              let open HomReasoning in
              begin
              C.ψ (t x) ≈˘⟨ C.commute f ⟩ C.ψ (t x') ∘ F.₁ f
              ∎
          in
          eq (Setoid.refl (Fin≈ 1)) }
      ; commute = λ {s} {x} {x'} x≈x' →
        let
          n , r = s
          morph : ∀ (y : Setoid.Carrier (Fin≈ n)) → (Cat[ Fin≈ ↓ X ]) [ t (r ⟨$⟩ y) , s ]
          morph y =
            slicearr
              {h = const y}
              λ { {Fin.zero} {Fin.zero} refl → Setoid.refl X}
          open SetoidR (C.N)
        in
        begin
        underlying (r ⟨$⟩ x) ≡⟨⟩
        C.ψ (t (r ⟨$⟩ x)) ⟨$⟩ Fin.zero
          ≈˘⟨ C.commute (morph x) (Setoid.refl (Fin≈ 1)) ⟩
        C.ψ s ⟨$⟩ ((F.₁ (morph x)) ⟨$⟩ Fin.zero)
          ≡⟨⟩
        C.ψ s ⟨$⟩ x
          ≈⟨ Func.cong (C.ψ s) x≈x' ⟩
        C.ψ s ⟨$⟩ x'
        ∎
        }
  in
  record {
    ! = λ{C} → ! C ;
    !-unique = λ {C} other {x} {x'} x≈x' →
    let
      -- given an other cocone morphism to C
      module C = Cocone C
      module !C = Cocone⇒ (! C)
      module other = Cocone⇒ other
      open SetoidR (C.N)
    in
    begin
    !C.arr ⟨$⟩ x
      ≡⟨⟩
    C.ψ (t x) ⟨$⟩ Fin.zero
      ≈˘⟨ other.commute (Setoid.refl (Fin≈ 1)) ⟩
    other.arr ⟨$⟩ x
      ≈⟨ Func.cong other.arr x≈x' ⟩
    other.arr ⟨$⟩ x'
    ∎
  }

concat-tuples : {a : Level} {n m : ℕ} {X : Set a} (s : Fin n → X) (t : Fin m → X) → (Fin (n  Data.Nat.+ m) → X)
concat-tuples {a} {n} {m} s t n+m = Sum.[ s , t ] (splitAt n n+m)



merge-parallel : (k n : ℕ) (X : Setoid 0ℓ 0ℓ)
  (s : Func (Fin≈ k) X)
  (t : Func (Fin≈ n) X)
  (g h : Cat[ Fin≈ ↓ X ] [ (k , s) , (n , t) ]) → MergedMorphisms (Cat[ Fin≈ ↓ X ]) g h
merge-parallel k n X s t (slicearr {h = g≈} g-prop) (slicearr {h = h≈} h-prop) =
  record {
    tip = n , t ;
    merge = (slicearr {h = →-to-⟶ EndoCoeq.f } λ { {x} {x} refl → Setoid.sym X (merge-△ x) });
    prop = λ { {x} {x} refl  → EndoCoeq.identify-R (g≈.to x) (h≈.to x) (x , (refl , refl)) }
  }
  where
    module t = Func t
    module g≈ = Func g≈
    module h≈ = Func h≈
    module EndoCoeq = EndoCoequalize (finite-coequalize k (Fin n) (IsDecEquivalence._≟_ Fin-≡-isDecEquivalence) g≈.to h≈.to)

    open Setoid X using (_≈_)
    open SetoidR X
    merge-△ : (x : Fin n) → (t ⟨$⟩ x) ≈ (t ⟨$⟩ (EndoCoeq.f x))
    merge-△ x = EqClosure-ump _
      (λ y1 y2 → t ⟨$⟩ y1 ≈ t ⟨$⟩ y2) -- kernelpair
      (setoid-kernel-IsEquivalence X (λ y → t ⟨$⟩ y))
      (λ { {y1} {y2} (y , (gy , hy)) →
        begin
        t ⟨$⟩ y1    ≡˘⟨ cong t.to gy ⟩
        t ⟨$⟩ (g≈ ⟨$⟩ y)    ≈⟨ g-prop refl ⟩
        s ⟨$⟩ y    ≈˘⟨ h-prop refl ⟩
        t ⟨$⟩ (h≈ ⟨$⟩ y)    ≡⟨ cong t.to hy ⟩
        t ⟨$⟩ y2
        ∎
        })
      (EndoCoeq.reflect-f x)


canonical-cat-is-filtered : ∀ (X : Setoid 0ℓ 0ℓ) → filtered (Cat[ Fin≈ ↓ X ])
canonical-cat-is-filtered X =
  record {
    bounds = record
              { non-empty = 0 , (record { to = λ () ; cong = λ {x} → exfalso x }) ;
              upper-bound = λ {(k , s) (n , t) →
                (k Data.Nat.+ n) , →-to-⟶ (concat-tuples (_⟨$⟩_ s) (_⟨$⟩_ t)) } ;
              is-above₁ = λ {(k , s) (n , t) →
                let
                  open SetoidR X
                  -- inject+ = _↑ˡ_
                in
                slicearr {h = →-to-⟶ (λ - → - ↑ˡ n)}
                λ {i} {i'} i≈i' → begin
                concat-tuples (_⟨$⟩_ s) (_⟨$⟩_ t) (i ↑ˡ n)
                  ≡⟨⟩
                Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (splitAt k (i ↑ˡ n))
                  ≡⟨ cong Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (splitAt-↑ˡ k i n) ⟩
                -- Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (Sum.inj₁ i)
                --  ≡⟨⟩
                s ⟨$⟩ i
                  ≈⟨ Func.cong s i≈i' ⟩
                s ⟨$⟩ i'
                ∎
                } ;
              is-above₂ = λ {(k , s) (n , t) →
                let
                  open SetoidR X
                in
                slicearr {h = →-to-⟶ (_↑ʳ_ {n} k)}
                λ {i} {i'} i≈i' →
                begin
                concat-tuples (_⟨$⟩_ s) (_⟨$⟩_ t) (k ↑ʳ i)
                  ≡⟨⟩
                Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (splitAt k (k ↑ʳ i))
                  ≡⟨ cong Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (splitAt-↑ʳ k n i) ⟩
                -- Sum.[ _⟨$⟩_ s , _⟨$⟩_ t ] (Sum.inj₂ i)
                --  ≡⟨⟩
                t ⟨$⟩ i
                  ≈⟨ Func.cong t i≈i' ⟩
                t ⟨$⟩ i'
                ∎
              } } ;
    merge-parallel = record { merge-all = λ { {k , s} {n , t} g h →
          merge-parallel k  n X s t g h
        }
      }
    }
  where
    exfalso : ∀ {a : Level} {A : Set a} → Fin 0 → A
    exfalso ()



lift-filtered : ∀ {o ℓ e o' ℓ' e' : Level} → {𝒞 : Category o ℓ e} → filtered 𝒞 → filtered (liftC o' ℓ' e' 𝒞)
lift-filtered fil =
  record { bounds =
    record {
      non-empty = Level.lift fil.non-empty ;
      upper-bound = λ a b → Level.lift (fil.upper-bound (lower a) (lower b)) ;
      is-above₁ = λ a b → Level.lift (fil.is-above₁ (lower a) (lower b)) ;
      is-above₂ = λ a b → Level.lift (fil.is-above₂ (lower a) (lower b)) } ;
      merge-parallel = record { merge-all = λ g h →
        let module ma = MergedMorphisms (fil.merge-all (lower g) (lower h)) in
        record { tip = Level.lift ma.tip ; merge = Level.lift ma.merge ; prop = Level.lift ma.prop
      } } }
  where module fil = filtered fil

Setoids-Accessible : Accessible
Setoids-Accessible = record
               { Idx = ℕ
               ; fin = Fin≈
               ; fin-presentable = Fin-is-presentable
               ; build-from-fin = canonical-cocone-is-limitting
               ; canonical-has-prop = λ X → lift-filtered (canonical-cat-is-filtered X)
               ; coproduct = λ A B _ _ →  BinaryCoproducts.coproduct (Cocartesian.coproducts Setoids-Cocartesian) {A} {B} 
               }

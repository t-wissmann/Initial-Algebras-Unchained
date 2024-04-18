{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)

module Coalgebra.Recursive {o ℓ e} (𝒞 : Category o ℓ e) (F : Endofunctor 𝒞) where

private
  module 𝒞 = Category 𝒞
  module F = Functor F

open import Level

open import Categories.Functor.Coalgebra
open import Categories.Functor.Algebra hiding (iterate)
open import Categories.Category using (Category)
open import Categories.Category.Construction.F-Algebras
open import Categories.Diagram.Cocone.Properties
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Morphism using (IsIso; Iso; module ≅; Retract)
import Categories.Morphism
open import Categories.Object.Initial using (IsInitial)
open import Categories.Morphism.Reasoning

open import F-Coalgebra-Colimit
open import Colimit-Lemmas


-- We first recap some lemmas from:
--   [CUV06] Venanzio Capretta, Tarmo Uustalu, and Varmo Vene.
--           Recursive coalgebras from comonads.
--           Inf. Comput., 204(4):437–468, 2006.

record C2A-morphism {o ℓ e} {𝒞 : Category o ℓ e} {F : Endofunctor 𝒞}
  (X : F-Coalgebra F)
  (Y : F-Algebra F) : Set (ℓ ⊔ e) where
  open Category 𝒞
  module X = F-Coalgebra X
  module Y = F-Algebra Y
  open Functor F
  field
    f : X.A ⇒ Y.A
    commutes : f ≈ Y.α ∘ F₁ f ∘ X.α

-- we can precompose solutions with coalgebra morphisms:
C2A-precompose : {B D : F-Coalgebra F} → {A : F-Algebra F} →
  C2A-morphism D A → F-Coalgebra-Morphism B D → C2A-morphism B A
C2A-precompose {B} {D} {A} eval mor =
  let
    open Category 𝒞
    module eval = C2A-morphism eval
    module mor = F-Coalgebra-Morphism mor
    module B = F-Coalgebra B
    module D = F-Coalgebra D
    module A = F-Algebra A
    open HomReasoning
    open Functor F
  in
  record
  { f = eval.f ∘ mor.f ;
  commutes = begin
    eval.f ∘ mor.f                     ≈⟨ eval.commutes ⟩∘⟨refl  ⟩
    (A.α ∘ F₁ eval.f ∘ D.α) ∘ mor.f    ≈⟨ assoc ⟩
    A.α ∘ (F₁ eval.f ∘ D.α) ∘ mor.f    ≈⟨ refl⟩∘⟨ assoc ⟩
    A.α ∘ F₁ eval.f ∘ D.α ∘ mor.f      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ mor.commutes ⟩
    A.α ∘ F₁ eval.f ∘ F₁ mor.f ∘ B.α   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    A.α ∘ (F₁ eval.f ∘ F₁ mor.f) ∘ B.α ≈˘⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
    A.α ∘ F₁ (eval.f ∘ mor.f) ∘ B.α
          ∎
  }

record IsRecursive (X : F-Coalgebra F) : Set (o ⊔ ℓ ⊔ e) where
  morph = C2A-morphism.f
  field
    -- there is at least one solution:
    recur : (B : F-Algebra F) → C2A-morphism X B
    -- there is at most one solution:
    unique : (B : F-Algebra F) → (g h : C2A-morphism X B) →
      𝒞 [ morph g ≈ morph h ]


-- whenever a recursive coalgebra is an iso, it is the initial algebra:
-- [CUV06, Prop. 7(a)]
iso-recursive⇒initial :
  (R : F-Coalgebra F)
  → IsRecursive R
  → (r-iso : IsIso 𝒞 (F-Coalgebra.α R))
  → IsInitial (F-Algebras F) (to-Algebra (IsIso.inv r-iso))
iso-recursive⇒initial R is-rec r-iso =
  let
    open Category 𝒞
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
        h = C2A-morphism.f coalg2alg
        Fh = Functor.F₁ F h
      in
      record
        { f = h
        ; commutes = begin
          h ∘ r⁻¹
            ≈⟨  C2A-morphism.commutes coalg2alg ⟩∘⟨refl ⟩
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
      g-coalg2alg : C2A-morphism R A
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
  open Category 𝒞
  private
    module R = F-Coalgebra R
    module B = F-Coalgebra B

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
        module R2D = C2A-morphism R2D
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
        module sol1 = C2A-morphism sol1
        module sol2 = C2A-morphism sol2
        open HomReasoning
        -- first of all, the solutions are equal when precomposed with 'h: R -> B':
        sol1-h-is-sol2-h : sol1.f ∘ h.f ≈ sol2.f ∘ h.f
        sol1-h-is-sol2-h =
          IsRecursive.unique R-is-rec D
             (C2A-precompose sol1 h)
             (C2A-precompose sol2 h)

        -- this is essentially the reasoning: we do it forward for sol1 and
        -- backwards for sol2.
        sol-transformation sol =
          let
            module sol = C2A-morphism sol
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
  sandwich-recursive R (iterate R) is-rec r (Category.id (F-Coalgebras F)) equation
  where
    module R = F-Coalgebra R
    module FR = F-Coalgebra (iterate R)
    r : F-Coalgebra-Morphism R (iterate R)
    r = record { f = R.α ; commutes = 𝒞.Equiv.refl }

    equation : 𝒞 [ FR.α ≈ F.₁ R.α 𝒞.∘ 𝒞.id ]
    equation = 𝒞.Equiv.sym 𝒞.identityʳ

-- the functor sends coalgebra morphisms to coalgebra morphisms:
iterate-F-Coalgebra-Morphism : {A B : F-Coalgebra F}
  → (h : F-Coalgebra-Morphism A B)
  → F-Coalgebra-Morphism (iterate A) (iterate B)
iterate-F-Coalgebra-Morphism {A} {B} h =
  record {
    f = F.₁ h.f ; commutes = begin
      F.₁ β ∘ F.₁ h.f ≈˘⟨ F.homomorphism ⟩
      F.₁ (β ∘ h.f) ≈⟨ F.F-resp-≈ h.commutes ⟩
      F.₁ (F.₁ h.f ∘ α) ≈⟨ F.homomorphism ⟩
      F.₁ (F.₁ h.f) ∘ F.₁ α
      ∎}
  where
    module h = F-Coalgebra-Morphism h
    open F-Coalgebra A
    open F-Coalgebra B renaming (A to B; α to β)
    open Category 𝒞
    open HomReasoning


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

module _ {o' ℓ' e' : Level} {𝒟 : Category o' ℓ' e'} (J : Functor 𝒟 (F-Coalgebras F)) where
  private
    module 𝒟 = Category 𝒟
    module J = Functor J


  Limitting-Cocone-IsRecursive :
        (∀ (i : 𝒟.Obj) → IsRecursive (J.₀ i))
        -- ^- if all coalgebras in the diagram are recursive
      → (cocone : Cocone J)
        -- ^- if we have a cocone in coalgebras
      → IsLimitting (F-map-Coconeˡ forget-Coalgebra cocone)
        -- ^- which is limitting in the base category
      → IsRecursive (Cocone.N cocone)
        -- ^- then the tip of the cocone is also recursive
  Limitting-Cocone-IsRecursive all-recursive cocone limitting =
    -- we convert Cocone-Morphisms and C2A-morphisms back and forth:
    -- we write 'sol' (short for 'solution') for the unique C2A-morphisms.
    record { recur = λ B → cocone⇒-to-sol B (limitting.! {alg2cocone B})
           ; unique = λ B g h → limitting.!-unique₂ (sol-to-cocone⇒ B g) (sol-to-cocone⇒ B h)
           }
    where
      open Category 𝒞
      open HomReasoning
      module cocone = Cocone cocone
      module limitting = IsInitial limitting
      obj-cocone = (F-map-Coconeˡ forget-Coalgebra cocone)
      module obj-cocone = Cocone obj-cocone

      -- every algebra induces a cocone of the unique C2A-morphisms:
      alg2cocone : F-Algebra F → Cocone (forget-Coalgebra ∘F J)
      alg2cocone B =
        let module B = F-Algebra B in
        record { coapex = record {
          ψ = λ i → C2A-morphism.f (IsRecursive.recur (all-recursive i) B) ;
          commute = λ {i} {i'} h →
            let
              sol1 = IsRecursive.recur (all-recursive i) B
              sol2 = C2A-precompose (IsRecursive.recur (all-recursive i') B) (J.₁ h)
            in
            -- the triangles of the cocone commute because of uniqueness of C2A-morphisms:
            IsRecursive.unique (all-recursive i) B sol2 sol1 } }

      -- every Cocone-Morphism induces a C2A-morphism
      cocone⇒-to-sol : (B : F-Algebra F)
                  → Cocone⇒ (forget-Coalgebra ∘F J) obj-cocone (alg2cocone B)
                  → C2A-morphism cocone.N B
      cocone⇒-to-sol B mor = let
          module B = F-Algebra B
          module mor = Cocone⇒ mor
        in
        record { f = mor.arr ; commutes = limitting-cocone-is-jointly-epic obj-cocone limitting (λ i →
          let
            sol = IsRecursive.recur (all-recursive i) B
            module sol = C2A-morphism sol
          in
          begin
          mor.arr ∘ obj-cocone.ψ i ≈⟨ mor.commute {i} ⟩
          sol.f  ≈⟨ sol.commutes ⟩
          B.α ∘ F.F₁ sol.f ∘ F-Coalgebra.α (J.₀ i)  ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ mor.commute ⟩∘⟨refl ⟩
          B.α ∘ F.F₁ (mor.arr ∘ obj-cocone.ψ i) ∘ F-Coalgebra.α (J.₀ i)  ≈⟨ refl⟩∘⟨ pushˡ 𝒞 F.homomorphism ⟩
          B.α ∘ F.F₁ mor.arr ∘ F.₁ (obj-cocone.ψ i) ∘ F-Coalgebra.α (J.₀ i)  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (cocone.ψ i) ⟩
          B.α ∘ F.F₁ mor.arr ∘ F-Coalgebra.α cocone.N ∘ obj-cocone.ψ i  ≈˘⟨ (assoc ○ (refl⟩∘⟨ assoc)) ⟩
          (B.α ∘ F.F₁ mor.arr ∘ F-Coalgebra.α cocone.N) ∘ obj-cocone.ψ i
          ∎) }

      -- And conversely, every C2A-Morphism induces a every Cocone-Morphism
      sol-to-cocone⇒ : (B : F-Algebra F) → C2A-morphism cocone.N B
                  → Cocone⇒ (forget-Coalgebra ∘F J) obj-cocone (alg2cocone B)
      sol-to-cocone⇒ B sol = let
          module B = F-Algebra B
          module sol = C2A-morphism sol
        in record
        { arr = sol.f
        ; commute = λ {i} →
            IsRecursive.unique (all-recursive i) B
            (C2A-precompose sol (cocone.ψ i))
            (IsRecursive.recur (all-recursive i) B)
        }


R-Coalgebras-Colimit : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D R-Coalgebras)
        → Colimit (forget-Coalgebra ∘F forget-rec ∘F  J) → Colimit J
R-Coalgebras-Colimit J 𝒞-colim =
  FullSub-Colimit R-Coalgebra.coalg J Coalg-colim R (≅.refl (F-Coalgebras F))
  where
    module J = Functor J
    module 𝒞-colim = Colimit 𝒞-colim
    Coalg-colim : Colimit (forget-rec ∘F J)
    Coalg-colim = F-Coalgebras-Colimit _ 𝒞-colim
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
            C2A-morphism.f (R.recur B) ;
          commute = λ {R} {R'} h →
            let
              -- h is a coalg-hom from R to R':
              module R = R-Coalgebra (J.F₀ R)
              module R' = R-Coalgebra (J.F₀ R')
              open Category 𝒞
              open HomReasoning
              open Equiv
              module h = F-Coalgebra-Morphism (J.F₁ h)
              module U = Functor (forget-Coalgebra ∘F forget-rec ∘F J)
              module U' = Functor (forget-rec ∘F J)
              -- we can use it to construct another solution from R to B:
              sol : C2A-morphism R.coalg B
              sol =
                let
                  module r' = C2A-morphism (R'.recur B)
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
    alg2solution : (B : F-Algebra F) → C2A-morphism Coalg-colim.coapex B
    alg2solution B =
      let
        module B = F-Algebra B
        open Category 𝒞
        open HomReasoning

        sol : 𝒞 [ F-Coalgebra.A Coalg-colim.coapex , B.A ]
        sol = 𝒞-colim.rep (alg2cocone B)
      in
      record { f = sol ;
        commutes = colimit-is-jointly-epic 𝒞-colim λ R →
            let
              module R = R-Coalgebra (J.F₀ R)
              module R-sol = C2A-morphism (R.recur B)
            in
            begin
            sol ∘ 𝒞-colim.proj R
              ≈⟨ 𝒞-colim.commute ⟩
            R-sol.f
              ≈⟨ R-sol.commutes ⟩
            B.α ∘ F.F₁ R-sol.f ∘ R.α
              ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ 𝒞-colim.commute ⟩∘⟨refl ⟩
            B.α ∘ F.F₁ (sol ∘ 𝒞-colim.proj R) ∘ R.α
              ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
            B.α ∘ (F.F₁ sol ∘ F.F₁ (𝒞-colim.proj R)) ∘ R.α
              ≈⟨ refl⟩∘⟨ assoc ⟩
            B.α ∘ F.F₁ sol ∘ (F.F₁ (𝒞-colim.proj R) ∘ R.α)
              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (Coalg-colim.proj R) ⟩
            B.α ∘ F.F₁ sol ∘ F-Coalgebra.α Coalg-colim.coapex ∘ 𝒞-colim.proj R
              ≈˘⟨ refl⟩∘⟨  assoc ⟩
            B.α ∘ (F.F₁ sol ∘ F-Coalgebra.α Coalg-colim.coapex) ∘ 𝒞-colim.proj R
              ≈˘⟨  assoc ⟩
            (B.α ∘ F.F₁ sol ∘ F-Coalgebra.α Coalg-colim.coapex) ∘ 𝒞-colim.proj R
            ∎
          }

    -- we can then show that the colimit coalgebra must be recursive:
    R : R-Coalgebra
    R = record {
      coalg = Coalg-colim.coapex ;
      ump = record {
        recur = alg2solution;
        unique = λ B g h →
          colimit-is-jointly-epic 𝒞-colim λ R →
            let
              open Category 𝒞
              open HomReasoning
              module B = F-Algebra B
              module R = R-Coalgebra (J.F₀ R)
              -- we need to show that every solution in the colim induces a solution of R
              proj-sol : C2A-morphism Coalg-colim.coapex B → C2A-morphism R.coalg B
              proj-sol s =
                let module s = C2A-morphism s in
                record {
                f = s.f ∘ 𝒞-colim.proj R ;
                commutes =
                  begin
                  s.f ∘ 𝒞-colim.proj R
                    ≈⟨ s.commutes ⟩∘⟨refl ⟩
                  (B.α ∘ F.F₁ s.f ∘ F-Coalgebra.α Coalg-colim.coapex) ∘ 𝒞-colim.proj R
                    ≈⟨ assoc ⟩
                  B.α ∘ ((F.F₁ s.f ∘ F-Coalgebra.α Coalg-colim.coapex) ∘ 𝒞-colim.proj R)
                    ≈⟨ refl⟩∘⟨ assoc ⟩
                  B.α ∘ F.F₁ s.f ∘ F-Coalgebra.α Coalg-colim.coapex ∘ 𝒞-colim.proj R
                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (Coalg-colim.proj R) ⟩
                  B.α ∘ F.F₁ s.f ∘ F.F₁ (𝒞-colim.proj R) ∘ R.α
                    ≈˘⟨ refl⟩∘⟨ assoc ⟩
                  B.α ∘ (F.F₁ s.f ∘ F.F₁ (𝒞-colim.proj R)) ∘ R.α
                    ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
                  B.α ∘ F.F₁ (s.f ∘ 𝒞-colim.proj R) ∘ R.α
                  ∎
                }
            in
            R.unique B (proj-sol g) (proj-sol h)
        } }


retract-coalgebra : (X : F-Coalgebra F) {Y : 𝒞.Obj}
  → Retract 𝒞 (F-Coalgebra.A X) Y
  → F-Coalgebra F
retract-coalgebra X {Y} r = record { A = Y ; α = F₁ r.section ∘ X.α ∘ r.retract }
  where
    open Functor F
    open Category 𝒞
    module r = Retract r
    module X = F-Coalgebra X


retract-coalgebra-hom : (X : F-Coalgebra F) {Y : 𝒞.Obj}
  → (r : Retract 𝒞 (F-Coalgebra.A X) Y)
  → F-Coalgebras F [ X , retract-coalgebra X r ]
retract-coalgebra-hom X {Y} r =
  record { f = r.section ; commutes = begin
    (F₁ r.section ∘ X.α ∘ r.retract) ∘ r.section ≈⟨ assoc²' 𝒞 ⟩
    F₁ r.section ∘ X.α ∘ r.retract ∘ r.section ≈⟨ refl⟩∘⟨ elimʳ 𝒞 r.is-retract ⟩
    F₁ r.section ∘ X.α
    ∎}
  where
    open Functor F
    open Category 𝒞
    open HomReasoning
    module r = Retract r
    module X = F-Coalgebra X

retract-coalgebra-hom⁻¹ : (X : F-Coalgebra F) {Y : 𝒞.Obj}
  → (r : Retract 𝒞 (F-Coalgebra.A X) Y)
  → F-Coalgebras F [ retract-coalgebra X r , X ]
retract-coalgebra-hom⁻¹ X {Y} r =
  record { f = r.retract ; commutes = begin
    X.α ∘ r.retract ≈˘⟨ pullˡ 𝒞 (elimˡ 𝒞 (F-resp-≈ r.is-retract ○ identity)) ⟩
    F₁ (r.retract ∘ r.section) ∘ X.α ∘ r.retract ≈⟨ pushˡ 𝒞 homomorphism ⟩
    F₁ r.retract ∘ F₁ r.section ∘ X.α ∘ r.retract
    ∎}
  where
    open Functor F
    open Category 𝒞
    open HomReasoning
    module r = Retract r
    module X = F-Coalgebra X

retract-coalgebra-hom-to-iterate : (X : F-Coalgebra F) {Y : 𝒞.Obj}
  → (r : Retract 𝒞 (F-Coalgebra.A X) Y)
  → F-Coalgebras F [ retract-coalgebra X r , (iterate X) ]
retract-coalgebra-hom-to-iterate X {Y} r =
  record { f = X.α ∘ r.retract ; commutes =
    begin
    F₁ X.α ∘ X.α ∘ r.retract ≈˘⟨ refl⟩∘⟨ elimˡ 𝒞 identity ⟩
    F₁ X.α ∘ F₁ id ∘ X.α ∘ r.retract ≈˘⟨ refl⟩∘⟨ F-resp-≈ r.is-retract ⟩∘⟨refl  ⟩
    F₁ X.α ∘ F₁ (r.retract ∘ r.section) ∘ X.α ∘ r.retract ≈⟨ refl⟩∘⟨ pushˡ 𝒞 homomorphism ⟩
    F₁ X.α ∘ F₁ r.retract ∘ F₁ r.section ∘ X.α ∘ r.retract ≈˘⟨ pushˡ 𝒞 homomorphism ⟩
    F₁ (X.α ∘ r.retract) ∘ F₁ r.section ∘ X.α ∘ r.retract
    ∎
  }
  where
    open Functor F
    open Category 𝒞
    open HomReasoning
    module r = Retract r
    module X = F-Coalgebra X

retract-coalgebra-recursive : (X : F-Coalgebra F) {Y : 𝒞.Obj}
  → (r : Retract 𝒞 (F-Coalgebra.A X) Y)
  → IsRecursive X
  → IsRecursive (retract-coalgebra X r)
retract-coalgebra-recursive X {Y} r X-rec =
  sandwich-recursive X (retract-coalgebra X r) X-rec
    (retract-coalgebra-hom X r)
    (retract-coalgebra-hom-to-iterate X r) 𝒞.Equiv.refl
  where
    open Functor F
    open Category 𝒞
    open HomReasoning
    module r = Retract r
    module X = F-Coalgebra X

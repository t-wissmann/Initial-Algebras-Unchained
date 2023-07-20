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
open import Categories.Morphism using (IsIso; Iso)
open import Categories.Object.Initial using (IsInitial)
open import Function.Equality using (cong)
open import Categories.Morphism.Reasoning

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

-- The recursive coalgebras form a full subcategory of F-Coalgebras:
R-Coalgebras : Category (ℓ ⊔ o ⊔ e) (e ⊔ ℓ) e
R-Coalgebras = FullSubCategory (F-Coalgebras F) R-Coalgebra.coalg
  where
    open import Categories.Category.SubCategory using (FullSubCategory)

forget-Coalgebra : Functor (F-Coalgebras F) C
forget-Coalgebra =
    let
      -- open Category (F-Coalgebras F)
      open Category C
      open HomReasoning
      open Equiv
    in
    record
      { F₀ = F-Coalgebra.A
      ; F₁ = F-Coalgebra-Morphism.f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ equal → equal
      }

module _ {i : Level} where
  record Sink : Set (suc i ⊔ o ⊔ ℓ) where
    field
      {I} : Set i
      sink-dom : I → Category.Obj C
      {sink-codom} : Category.Obj C
      sink : (x : I) → C [ sink-dom x , sink-codom ]

    -- the property whether a Sink is jointly epic:
    jointly-epic : Set _
    jointly-epic =
      ∀ (Z : Category.Obj C) (g h : C [ sink-codom , Z ]) →
        (∀ (x : I) → C [ C [ g ∘ sink x ] ≈ C [ h ∘ sink x ] ]) →
        C [ g ≈ h ]

open import Categories.Diagram.Cocone

sink-from-cocone : ∀ {o′ ℓ′ e′} {J : Category o′ ℓ′ e′} (G : Functor J C) → Cocone G → Sink
sink-from-cocone = λ G cocone →
  record {
    sink-dom = Functor.F₀ G;
    sink = λ x → Cocone.ψ cocone x }

-- jointly-epic = ∀ {i : Level} {I : Set i} {X : I → Category.Obj C} (f : (x : I) → Category._⇒_ C (X))
-- colimit-injection-jointly-epic : (o ℓ e : Level) {o′ ℓ′ e′ : Level} (C : Category o′ ℓ′ e′)
--   {J : Category o ℓ e} (F : Functor J C) (colim: Colimit F)

open import Categories.Category.Cocomplete
-- The F-Coalgebras are cocomplete if the underlying category is:
module _ where
  open import Categories.Functor using (_∘F_)
  open import Categories.Diagram.Colimit using (Colimit)
  open import Categories.Diagram.Cocone

  F-Coalgebras-Cocomplete : (o' ℓ' e' : Level) → Cocomplete o' ℓ' e' C → Cocomplete o' ℓ' e' (F-Coalgebras F)
  F-Coalgebras-Cocomplete o' ℓ' e' C-Cocomplete {D} = λ (J : Functor D (F-Coalgebras F)) →
    let
      module J = Functor J
      -- we first compute the colimit in C:
      composed-diagram = forget-Coalgebra ∘F J
      colim = C-Cocomplete composed-diagram
      module colim = Colimit colim
      -- Question: why does the following line work but not `K = colim.initial.⊥.N`?
      K = Cocone.N colim.initial.⊥
      -- for the coalgebra on K, we define a cocone with tip 'FK:'
      FK-cocone : Cocone composed-diagram
      FK-cocone =
        let
          open Functor F
          open Category C
          open HomReasoning
        in
        record { coapex = record {
          -- for every object X in the diagram:
          ψ = λ A →
            F₁ (Cocone.ψ colim.initial.⊥ A) ∘ (F-Coalgebra.α (J.F₀ A))
          ;
          -- for every hom h in the diagram:
          commute = λ {A} {A'} h →
            let
              module h = F-Coalgebra-Morphism (J.F₁ h)
            in
            begin
            (F₁ (colim.proj A') ∘ F-Coalgebra.α (J.F₀ A')) ∘ h.f        ≈⟨ assoc ⟩
            F₁ (colim.proj A') ∘ F-Coalgebra.α (J.F₀ A') ∘ h.f          ≈⟨ refl⟩∘⟨ h.commutes ⟩
            F₁ (colim.proj A') ∘ F₁ h.f ∘ F-Coalgebra.α (J.F₀ A)        ≈⟨ sym-assoc ⟩
            (F₁ (colim.proj A') ∘ F₁ h.f) ∘ F-Coalgebra.α (J.F₀ A)
            ≈˘⟨ homomorphism ⟩∘⟨refl ⟩
            F₁ (colim.proj A' ∘ h.f) ∘ F-Coalgebra.α (J.F₀ A)
            ≈⟨ F-resp-≈ (colim.colimit-commute h) ⟩∘⟨refl ⟩
            F₁ (colim.proj A) ∘ F-Coalgebra.α (J.F₀ A)
            ∎
          }
        }

      -- and we then use the universal property of K to define a coalgebra on K.
      -- for that, we first use the universal property:
      cocone-morph : Cocone⇒ _ colim.initial.⊥ FK-cocone
      cocone-morph = IsInitial.! colim.initial.⊥-is-initial
      k : F-Coalgebra-on F K
      k = Cocone⇒.arr cocone-morph

      K,k : F-Coalgebra F
      K,k = record { A = K ; α = k }

      -- the colimit injections/projections are all coalgebra morphisms:
      coalg-inj : ∀ A → F-Coalgebra-Morphism (J.F₀ A) K,k
      coalg-inj = λ A,α →
        let
          open Functor F
          open Category C
          open F-Coalgebra (J.F₀ A,α)
          open HomReasoning
          f = Cocone.ψ colim.initial.⊥ A,α
        in
        record {
        -- the underlying morphism is just the ordinary colimit injection
        f = f ;
        commutes =
            begin
            k ∘ f   ≈⟨ Cocone⇒.commute cocone-morph ⟩
            F₁ f ∘ α
            ∎
        }
    in
    record {
      initial = record {
        ⊥ = record {
          coapex = record {
            ψ = coalg-inj ;
            commute = λ h →
              -- for all connecting morphisms, we inherit the triangle commutativity
              Cocone.commute colim.initial.⊥ h
              } } ;
        ⊥-is-initial =
          record {
            ! = λ {competing} →
              let
                -- for any other cocone in F-Coalgebras
                module N = F-Coalgebra (Cocone.N competing)
                module competing = Cocone competing
                -- send the cocone down to C:
                C-cocone : Cocone composed-diagram
                C-cocone = record {
                  coapex = record {
                    ψ = λ X → F-Coalgebra-Morphism.f (competing.ψ X) ;
                    commute = competing.commute
                    } }
                C-cocone-morph : Cocone⇒ _ colim.colimit C-cocone
                C-cocone-morph = colim.initial.!
              in
              record {
                arr =
                  record {
                    f = Cocone⇒.arr C-cocone-morph ;
                    commutes = {!colim.!} } ;
                commute = {!!} } ;
            !-unique = {!!} }
        }
    }

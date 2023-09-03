{-# OPTIONS --without-K #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)

module F-Coalgebra-Colimit {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} where

open import Level

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial using (IsInitial)

open import Unchained-Utils

open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone

-- TODO: how can I make G an implicit parameter in the following theorem/proof?
-- TODO2: why does 'C' have to be an explicit parameter to jointly-epic?

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


open import Categories.Category.Cocomplete
open import Categories.Functor using (_∘F_)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cocone

F-Coalgebras-Colimit : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
        → Colimit (forget-Coalgebra ∘F J) → Colimit J
F-Coalgebras-Colimit {o'} {ℓ'} {e'} {D} J colim =
  let
    module J = Functor J
    -- we first compute the colimit in C:
    composed-diagram = forget-Coalgebra ∘F J
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
      in
      record {
      -- the underlying morphism is just the ordinary colimit injection
      f = colim.proj A,α ;
      commutes =
          begin
          k ∘ colim.proj A,α   ≈⟨ Cocone⇒.commute cocone-morph ⟩
          F₁ (colim.proj A,α) ∘ α
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

              -- this induces a cocone morphism in C
              C-cocone-morph : Cocone⇒ _ colim.colimit C-cocone
              C-cocone-morph = colim.initial.!
              -- which gives rise to the coalgebra morphism:
              h : F-Coalgebra-Morphism K,k competing.N
              h =
                let
                  h = Cocone⇒.arr C-cocone-morph
                  open Category C
                  open Functor F
                  open HomReasoning
                in
                record {
                f = h ;
                commutes = colimit-is-jointly-epic colim λ X →
                    let
                      module X = F-Coalgebra (J.F₀ X)
                    in
                    begin
                      (N.α ∘ h) ∘ colim.proj X     ≈⟨ assoc ⟩
                      N.α ∘ (h ∘ colim.proj X)     ≈⟨ refl⟩∘⟨ Cocone⇒.commute C-cocone-morph ⟩
                      N.α ∘ Cocone.ψ C-cocone X    ≈⟨ F-Coalgebra-Morphism.commutes (competing.ψ X) ⟩
                      F₁ (Cocone.ψ C-cocone X) ∘ X.α  ≈˘⟨ F-resp-≈ (Cocone⇒.commute C-cocone-morph) ⟩∘⟨refl ⟩
                      F₁ (h ∘ colim.proj X) ∘ X.α ≈⟨ homomorphism ⟩∘⟨refl ⟩
                      (F₁ h ∘ F₁ (colim.proj X)) ∘ X.α ≈⟨ assoc ⟩
                      F₁ h ∘ (F₁ (colim.proj X) ∘ X.α) ≈˘⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (coalg-inj X) ⟩
                      F₁ h ∘ (k ∘ colim.proj X) ≈˘⟨ assoc ⟩
                      (F₁ h ∘ k) ∘ colim.proj X
                    ∎
                }
            in
            record {
              arr = h ;
              commute = λ {X} →
                let
                  open Category C
                  module h = F-Coalgebra-Morphism h
                  open HomReasoning
                in
                begin
                  h.f ∘ colim.proj X     ≈⟨ Cocone⇒.commute C-cocone-morph ⟩
                  F-Coalgebra-Morphism.f (competing.ψ X)
                ∎
              } ;
          !-unique = λ {competing} another-cocone-morph →
            let
              -- some redundancy:
              module competing = Cocone competing
              C-cocone : Cocone composed-diagram
              C-cocone = record {
                coapex = record {
                  ψ = λ X → F-Coalgebra-Morphism.f (competing.ψ X) ;
                  commute = competing.commute
                  } }
              -- for the actual proof:
              module another-cocone-morph = Cocone⇒ another-cocone-morph
              -- for any other cocone moprhism,
              -- we directly have one between the cocones in C
              another-C-cocone-morph : Cocone⇒ _ colim.colimit C-cocone
              another-C-cocone-morph = record {
                arr = F-Coalgebra-Morphism.f another-cocone-morph.arr ;
                commute = another-cocone-morph.commute
                }
              -- colim.initial.⊥.!-unique another-C-cocone-morph
            in
            IsInitial.!-unique colim.initial.⊥-is-initial another-C-cocone-morph
          }
      }
  }

F-Coalgebras-Cocomplete : (o' ℓ' e' : Level) → Cocomplete o' ℓ' e' C → Cocomplete o' ℓ' e' (F-Coalgebras F)
F-Coalgebras-Cocomplete o' ℓ' e' C-Cocomplete {D} = λ (J : Functor D (F-Coalgebras F)) →
  F-Coalgebras-Colimit J (C-Cocomplete (forget-Coalgebra ∘F J))

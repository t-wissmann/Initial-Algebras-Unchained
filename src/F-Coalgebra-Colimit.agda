{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Agda.Builtin.Equality renaming (refl to ≡-refl)
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ; F-map-Cocone⇒ˡ)

module F-Coalgebra-Colimit {o ℓ e} {𝒞 : Category o ℓ e} {F : Endofunctor 𝒞} where

private
  module 𝒞 = Category 𝒞

open import Level

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial using (IsInitial)

open import Colimit-Lemmas

open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone

forget-Coalgebra : Functor (F-Coalgebras F) 𝒞
forget-Coalgebra =
    let
      -- open Category (F-Coalgebras F)
      open Category 𝒞
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


-- Whenever a cocone in F-Coalgebras is (co)limitting on the level of the base category,
-- it is (co)limitting in F-Coalgebras, too!
F-Coalgebras-Limitting-Cocone : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'}
  → (J : Functor D (F-Coalgebras F))
  → (K : Cocone J)
  → IsLimitting (F-map-Coconeˡ forget-Coalgebra K)
  → IsLimitting K
F-Coalgebras-Limitting-Cocone {o'} {ℓ'} {e'} {D} J K UK-limitting =
  record {
    ! = λ {competing} →
      record {
        arr = coalg-initiality.h competing ;
        commute = λ {X} →
          Cocone⇒.commute (coalg-initiality.C-cocone-morph competing)
      } ;
    !-unique = λ {competing} other-mor →
      IsInitial.!-unique UK-limitting (F-map-Cocone⇒ˡ U other-mor)
      }
  where
    module J = Functor J
    U = forget-Coalgebra
    UK = F-map-Coconeˡ forget-Coalgebra K
    module UK = Cocone UK
    module K = Cocone K

    k = F-Coalgebra.α K.N

    -- the colimit in 𝒞:
    colim : Colimit (U ∘F J)
    colim = Colimit-from-prop UK-limitting
    module colim = Colimit colim
    -- we first compute the colimit in C:
    composed-diagram = forget-Coalgebra ∘F J

    module coalg-initiality (competing : Cocone J) where
      -- for any other cocone in F-Coalgebras
      module N = F-Coalgebra (Cocone.N competing)
      module competing = Cocone competing
      -- send the cocone down to C:
      C-cocone : Cocone composed-diagram
      C-cocone = F-map-Coconeˡ U competing

      -- this induces a cocone morphism in 𝒞
      C-cocone-morph : Cocone⇒ _ UK C-cocone
      C-cocone-morph = IsInitial.! UK-limitting
      -- which gives rise to the coalgebra morphism:
      h : F-Coalgebra-Morphism K.N competing.N
      h =
        let
          h = Cocone⇒.arr C-cocone-morph
          open Category 𝒞
          open Functor F
          open HomReasoning
        in
        record {
        f = h ;
        commutes = colimit-is-jointly-epic colim λ X →
            let
              module X = F-Coalgebra (J.₀ X)
            in
            begin
              (N.α ∘ h) ∘ colim.proj X     ≈⟨ assoc ⟩
              N.α ∘ (h ∘ colim.proj X)     ≈⟨ refl⟩∘⟨ Cocone⇒.commute C-cocone-morph ⟩
              N.α ∘ Cocone.ψ C-cocone X    ≈⟨ F-Coalgebra-Morphism.commutes (competing.ψ X) ⟩
              F₁ (Cocone.ψ C-cocone X) ∘ X.α  ≈˘⟨ F-resp-≈ (Cocone⇒.commute C-cocone-morph) ⟩∘⟨refl ⟩
              F₁ (h ∘ colim.proj X) ∘ X.α ≈⟨ homomorphism ⟩∘⟨refl ⟩
              (F₁ h ∘ F₁ (colim.proj X)) ∘ X.α ≈⟨ assoc ⟩
              F₁ h ∘ (F₁ (colim.proj X) ∘ X.α) ≈˘⟨ refl⟩∘⟨ F-Coalgebra-Morphism.commutes (K.ψ X) ⟩
              F₁ h ∘ (k ∘ colim.proj X) ≈˘⟨ assoc ⟩
              (F₁ h ∘ k) ∘ colim.proj X
            ∎
        }

F-Coalgebras-Lift-Cocone : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
  → Colimit (forget-Coalgebra ∘F J) → Cocone J
F-Coalgebras-Lift-Cocone J colim = J-cocone
  where
    module J = Functor J
    module colim = Colimit colim
    -- Question: why does the following line work but not `K = colim.initial.⊥.N`?
    K = Cocone.N colim.initial.⊥
    -- for the coalgebra on K, we define a cocone with tip 'FK:'
    FK-cocone : Cocone (forget-Coalgebra ∘F J)
    FK-cocone =
      let
        open Functor F
        open Category 𝒞
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
        open Category 𝒞
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

    J-cocone : Cocone J
    J-cocone = record { coapex = record {
      ψ = coalg-inj ;
      commute = Cocone.commute colim.initial.⊥
      } }

F-Coalgebras-Colimit-Carrier-Limitting : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
        → (colim : Colimit (forget-Coalgebra ∘F J))
        → IsLimitting (F-map-Coconeˡ forget-Coalgebra (F-Coalgebras-Lift-Cocone J colim))
F-Coalgebras-Colimit-Carrier-Limitting J colim =
      record {
        ! = λ {K'} →
          record {
            arr = colim.rep K' ;
            commute = colim.commute } ;
        !-unique = λ {K'} f →
          let
            -- we need to unfold/fold the definitions a bit:
            f' : Cocone⇒ _ colim.colimit K'
            f' = record { arr = Cocone⇒.arr f ; commute = Cocone⇒.commute f }
            eq : 𝒞 [ Cocone⇒.arr (colim.initial.! {K'}) ≈ Cocone⇒.arr f' ]
            eq = colim.initial.!-unique f'
          in
          eq
          }
      where
        module J = Functor J
        module colim = Colimit colim
        J-cocone : Cocone J
        J-cocone = F-Coalgebras-Lift-Cocone J colim


F-Coalgebras-Colimit : {o' ℓ' e' : Level} → {D : Category o' ℓ' e'} → (J : Functor D (F-Coalgebras F))
        → Colimit (forget-Coalgebra ∘F J) → Colimit J
F-Coalgebras-Colimit {o'} {ℓ'} {e'} {D} J colim =
  Colimit-from-prop
    (F-Coalgebras-Limitting-Cocone J J-cocone
      (F-Coalgebras-Colimit-Carrier-Limitting J colim))
  where
        J-cocone : Cocone J
        J-cocone = F-Coalgebras-Lift-Cocone J colim

F-Coalgebras-Cocomplete : (o' ℓ' e' : Level) → Cocomplete o' ℓ' e' 𝒞 → Cocomplete o' ℓ' e' (F-Coalgebras F)
F-Coalgebras-Cocomplete o' ℓ' e' C-Cocomplete {D} = λ (J : Functor D (F-Coalgebras F)) →
  F-Coalgebras-Colimit J (C-Cocomplete (forget-Coalgebra ∘F J))

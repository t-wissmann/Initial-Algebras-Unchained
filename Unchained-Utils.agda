{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor using (Functor)

module Unchained-Utils {o ℓ e} {𝒞 : Category o ℓ e} where

open import Level
open import Agda.Builtin.Sigma

open import Categories.Category.Construction.F-Coalgebras
open import Categories.Category.Construction.Cocones using (Cocones)
open import Categories.Functor.Coalgebra
open import Categories.Morphism 𝒞 -- open the module with the category 𝒞 fixed.
open import Categories.Object.Initial using (IsInitial)

open import Categories.Category
open import Categories.Object.Coproduct using (Coproduct)

open import Categories.Diagram.Colimit using (Colimit; transport-by-iso)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties
open import Categories.Functor using (_∘F_)
open import Agda.Builtin.Equality
open import Categories.Morphism.Reasoning
open import Categories.Morphism.Reasoning.Core


open import Categories.Category.SubCategory
open import Categories.Functor.Construction.SubCategory using (FullSub)
open import Notation

private
  module 𝒞 = Category 𝒞

record Full-≈ {o' ℓ' e' : Level} {𝒟 : Category o' ℓ' e'} (F : Functor 𝒟 𝒞) : Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where
  private
    module 𝒟 = Category 𝒟
    module F = Functor F
  field
    preimage : ∀ (X Y : 𝒟.Obj) → 𝒞 [ F.₀ X , F.₀ Y ] → 𝒟 [ X , Y ]
    preimage-prop : ∀ (X Y : 𝒟.Obj) → (f : 𝒞 [ F.₀ X , F.₀ Y ]) → 𝒞 [ F.₁ (preimage X Y f) ≈ f ]

-- The property that a cocone is Colimitting/Limitting:
IsLimitting : {o' ℓ' e' : Level} {D : Category o' ℓ' e'} {J : Functor D 𝒞} → Cocone J → Set _
IsLimitting {J = J} cocone = IsInitial (Cocones J) cocone

-- The property that a functor F preserves the colimit of diagram J:
preserves-colimit : {o' o'' ℓ' ℓ'' e' e'' : _} →
  {𝒟 : Category o' ℓ' e'} →
  {ℰ : Category o'' ℓ'' e''} →
  (J : Functor 𝒟 𝒞) → (F : Functor 𝒞 ℰ) → Set _
preserves-colimit J F =
  ∀ (colim : Colimit J) → IsInitial (Cocones (F ∘F J)) (F-map-Coconeˡ F (Colimit.colimit colim))


-- the property whether a Sink is jointly epic:
jointly-epic : ∀ {i : Level} {I : Set i} {dom : I → Category.Obj 𝒞} {codom : Category.Obj 𝒞}
               (sink : (x : I) → 𝒞 [ dom x , codom ]) → Set _
jointly-epic {i} {I} {dom} {codom} sink =
  ∀ {Z : Category.Obj 𝒞} {g h : 𝒞 [ codom , Z ]} →
    (∀ (x : I) → 𝒞 [ 𝒞 [ g ∘ sink x ] ≈ 𝒞 [ h ∘ sink x ] ]) →
    𝒞 [ g ≈ h ]

limitting-cocone-is-jointly-epic : ∀ {o′ ℓ′ e′} {J : Category o′ ℓ′ e′} {G : Functor J 𝒞}
                                 → (cocone : Cocone G)
                                 → IsLimitting cocone
                                 → jointly-epic (Cocone.ψ cocone)
limitting-cocone-is-jointly-epic {G = G} cocone limitting {Z} {g} {h} equalize-g-h =
  IsInitial.!-unique₂ limitting g-morph h-morph -- g-morph h-morph
  where
    open Category 𝒞
    open HomReasoning
    module cocone = Cocone cocone
    -- first, define a cocone on Z via h:
    Z-cocone : Cocone G
    Z-cocone = record {
      N = Z ;
        coapex = record {
        ψ = λ X → h ∘ cocone.ψ X;
        commute = λ {X} {X'} f →
          begin
          (h ∘ cocone.ψ X') ∘ Functor.F₁ G f ≈⟨ assoc ⟩
          h ∘ (cocone.ψ X' ∘ Functor.F₁ G f) ≈⟨ refl⟩∘⟨ cocone.commute f ⟩
          h ∘ cocone.ψ X
          ∎
          } }
    -- -- TODO: why doesn't the proof work with the following definition of h-morph?
    -- h-morph : Cocone⇒ _ colim.colimit Z-cocone
    -- h-morph = IsInitial.! colim.initial.⊥-is-initial
    -- g and h induce cocone morphisms:
    h-morph : Cocone⇒ _ cocone Z-cocone
    h-morph = record
      { arr = h ;
      commute = λ {X} → Equiv.refl }
    g-morph : Cocone⇒ _ cocone Z-cocone
    g-morph = record
      { arr = g ;
      commute = λ {X} → equalize-g-h X }

colimit-is-jointly-epic : ∀ {o′ ℓ′ e′} {J : Category o′ ℓ′ e′} {G : Functor J 𝒞} →
                          (colim : Colimit G) → jointly-epic (Colimit.proj colim)
colimit-is-jointly-epic {G = G} colim {Z} =
  limitting-cocone-is-jointly-epic
    (Colimit.colimit colim) (Colimit.initial.⊥-is-initial colim)

module _ {o' ℓ' e' : Level} (𝒟 : Category o' ℓ' e') (D : Functor 𝒟 𝒞) (colim : Colimit D) where
  private
    module 𝒟 = Category 𝒟
    module D = Functor D
    module colim = Colimit colim

  colimit-unique-rep : (B : 𝒞.Obj) →
      -- if everything in the diagram has a unique morphism to B
      (∀ (i : 𝒟.Obj) → 𝒞 [ D.₀ i =∃!=> B ]) →
      -- then the colimit does so as well
      𝒞 [ colim.coapex =∃!=> B ]
  colimit-unique-rep B uniq =
    record {
      arr = cocone-mor.arr ;
      unique = λ other →
        colimit-is-jointly-epic colim λ i →
          begin
          cocone-mor.arr ∘ colim.proj i ≈⟨ cocone-mor.commute ⟩
          B-cocone.ψ i ≡⟨⟩
          singleton-hom.arr (uniq i) ≈⟨ singleton-hom.unique (uniq i) _ ⟩
          other ∘ colim.proj i
          ∎
    }
    where
      open Category 𝒞
      open HomReasoning
      -- we first need to prove existence:
      B-cocone : Cocone D
      B-cocone = record {coapex = record
        { ψ = λ i → singleton-hom.arr (uniq i)
        ; commute = λ {i} {j} f → Equiv.sym
                    (singleton-hom.unique
                      (uniq i)
                      (𝒞 [ singleton-hom.arr (uniq j) ∘ D.₁ f ])) }
        }
      module B-cocone = Cocone B-cocone
      cocone-mor : Cocone⇒ D colim.colimit B-cocone
      cocone-mor = colim.rep-cocone B-cocone
      module cocone-mor = Cocone⇒ cocone-mor


-- Lemma:
-- Consider a diagram J in a full subcategory of 𝒞 with a colimit in 𝒞.
-- If there is an object in the subcategory isomorphic to the C-colimit
-- then this gives rise to a colimit of J in the subcategory
FullSub-Colimit : {o' ℓ' e' i : Level}
                → {D : Category o' ℓ' e'}
                → {I : Set i}
                → (U : I → Category.Obj 𝒞)
                → (J : Functor D (FullSubCategory 𝒞 U))
                → (C-colim : Colimit (FullSub 𝒞 ∘F  J))
                → (lifted-colim-obj : I)
                → Colimit.coapex C-colim ≅ U lifted-colim-obj
                → Colimit J
FullSub-Colimit {D = D} {I = I} U J plain-C-colim lifted-colim-obj iso =
  record { initial = record { ⊥ = Sub-Cocone ; ⊥-is-initial = Sub-Cocone-initial } }
  where
    C-colim = (transport-by-iso (FullSub 𝒞 ∘F  J) plain-C-colim iso)
    module C-colim = Colimit (C-colim)
    open Category 𝒞
    open HomReasoning
    module J = Functor J
    module iso = _≅_ iso

    -- by the transport, we have a colimit on an object in the subcategory:
    test : C-colim.coapex ≡ U lifted-colim-obj
    test = refl
    -- so, we now only need to lift the colimit along 'U'

    Sub-Cocone : Cocone J
    Sub-Cocone = record {
      N = lifted-colim-obj ;
      coapex = record { ψ = C-colim.proj ; commute = C-colim.colimit-commute } }

    Sub-Cocone-ump : {other : Cocone J} → Cocone⇒ J Sub-Cocone other
    Sub-Cocone-ump {other} =
      record {
        arr = morph ;
        commute = λ {X} →
          Cocone⇒.commute (C-colim.initial.! {A = C-other})
        }
      where
        module other = Cocone other
        C-other : Cocone (FullSub 𝒞 ∘F J)
        C-other = (F-map-Coconeˡ (FullSub 𝒞) other)
        morph : 𝒞 [ C-colim.coapex , U other.N ]
        morph = Cocone⇒.arr (C-colim.initial.! {A = C-other})

    Sub-Cocone-initial : IsInitial (Cocones J) Sub-Cocone
    Sub-Cocone-initial = record {
      ! = Sub-Cocone-ump ;
      !-unique = λ {other : Cocone J} cocone-morph →
        let
          module other = Cocone other
          module cocone-morph = Cocone⇒ cocone-morph
          C-other : Cocone (FullSub 𝒞 ∘F J)
          C-other = (F-map-Coconeˡ (FullSub 𝒞) other)

          -- send the cocone 'other' down to C:
          C-cocone-morph : Cocone⇒ (FullSub 𝒞 ∘F J) C-colim.colimit C-other
          C-cocone-morph = record {
            arr = cocone-morph.arr ;
            commute = λ {X} → cocone-morph.commute }
        in
        IsInitial.!-unique C-colim.initial.⊥-is-initial C-cocone-morph
      }

Colimit-from-prop : {o' ℓ' e' : Level} {D : Category o' ℓ' e'} {J : Functor D 𝒞}
                      → {cocone : Cocone J} → IsLimitting cocone → Colimit J
Colimit-from-prop {cocone = cocone} limitting =
  record { initial = record { ⊥ = cocone ; ⊥-is-initial = limitting } }

HasCoproducts : Set _
HasCoproducts = ∀ (A B : 𝒞.Obj) → Coproduct 𝒞 A B

module _ {A B C : 𝒞.Obj} (p : Coproduct 𝒞 A B) where
  open Category 𝒞
  module p = Coproduct p
  record CoproductCases (f g : p.A+B ⇒ C) : Set e where
    field
      case-precompose-i₁ : f ∘ p.i₁ ≈ g ∘ p.i₁
      case-precompose-i₂ : f ∘ p.i₂ ≈ g ∘ p.i₂

  -- The injections of a coproduct are jointly epic:
  coproduct-jointly-epic :
    ∀ {f g : p.A+B ⇒ C} → CoproductCases f g → f ≈ g
  coproduct-jointly-epic {f} {g} cases =
    let
      open HomReasoning
      open CoproductCases cases
    in
    begin
    f ≈˘⟨ p.g-η ⟩
    p.[ f ∘ p.i₁ , f ∘ p.i₂ ] ≈⟨ p.[]-cong₂ case-precompose-i₁ case-precompose-i₂ ⟩
    p.[ g ∘ p.i₁ , g ∘ p.i₂ ] ≈⟨ p.g-η ⟩
    g
    ∎

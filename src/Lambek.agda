{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Object.Terminal

module Lambek {o ℓ e : Level} (𝒞 : Category o ℓ e) (F : Endofunctor 𝒞) (A,α : F-Coalgebra F) where

open import Categories.Morphism 𝒞
open F-Coalgebra A,α

private
  module F = Functor F
  Coalg = (F-Coalgebras F)
  module Coalg = Category (Coalg)
  module 𝒞 = Category 𝒞

-- This is essentially the Lambek proof from Categories.Category.Construction.F-Algebras.
-- But, we generalize the two crucial properties of the terminal coalgebra to as
-- explicit axioms:
-- 1. 'id' is the only endomorphism on A,α
-- 2. there is some homomorphism from F(A,α) to A,α

lambek : (∀ (f : A,α Coalg.⇒ A,α) → Coalg [ f ≈ Coalg.id ]) →
         (h : (iterate A,α) Coalg.⇒ A,α) →
         Iso α (F-Coalgebra-Morphism.f h)
lambek id_uniq h = record { isoˡ = h∘α≈id ; isoʳ = α∘h≈id }
  where
    open Category 𝒞

    module h = F-Coalgebra-Morphism h
    -- every coalgebra structure is itself a coalgebra homomorphism:
    α-hom : A,α Coalg.⇒ (iterate A,α)
    α-hom = record { f = α ; commutes = 𝒞.Equiv.refl }

    -- we can compose it with the proposed inverse h to yield
    -- an endomorphism on A,α
    h∘α : A,α Coalg.⇒ A,α
    h∘α = h Coalg.∘ α-hom

    -- this endomorphism is necessarily the identity
    h∘α≈id : Coalg [ h∘α ≈ Coalg.id ]
    h∘α≈id = id_uniq h∘α

    -- for the other identity (on FA), we use the first identity
    -- and use that 'h' is coalgebra morphism:
    α∘h≈id : α ∘ h.f ≈ id
    α∘h≈id = let open HomReasoning in
      begin
      α ∘ h.f            ≈⟨ h.commutes ⟩
      F.₁ h.f ∘ F.₁ α    ≈˘⟨ F.homomorphism ⟩
      F.₁ (h.f ∘ α)      ≈⟨ F.F-resp-≈ h∘α≈id ⟩
      F.₁ id             ≈⟨ F.identity ⟩
      id
      ∎

-- A more opaque version:
lambek' : (∀ (f : A,α Coalg.⇒ A,α) → Coalg [ f ≈ Coalg.id ]) →
         (inv : (iterate A,α) Coalg.⇒ A,α) →
         (A ≅ F.₀ A)
lambek' id_uniq inv = record {
  from = α ;
  to = F-Coalgebra-Morphism.f inv ;
  iso = lambek id_uniq inv }

-- We can instantiate above result back to the usual statement that the
-- terminal coalgebra has isomorphic structure:
lambek-terminal-coalgebra : IsTerminal Coalg A,α → IsIso α
lambek-terminal-coalgebra A,α-terminal = record
  { inv = F-Coalgebra-Morphism.f h
  ; iso = lambek (λ f → !-unique₂ {A,α} {f} {Coalg.id}) h
  }
  where
    open IsTerminal A,α-terminal
    h : Coalg [ iterate A,α , A,α ]
    h = !

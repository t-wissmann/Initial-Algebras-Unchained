{-# OPTIONS --without-K --safe #-}
open import Level

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_; Endofunctor)
open import Categories.Functor.Hom
open import Categories.Category.Cocomplete
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cocone.Properties using (F-map-Coconeˡ)
open import Agda.Builtin.Equality
open import Categories.Category.Construction.F-Coalgebras
open import Data.Product

open import Categories.Functor.Coalgebra

open import LFP using (WeaklyLFP)
open import Filtered
open import Colimit-Lemmas
open import Iterate.ProofGlobals

-- Let (A,α) be locally finite. For every P → FA, we construct
-- a finite-recursive coalgebra with a canonical coalgebra morphism to (FA,Fα).
-- Of course, this coalgebra morphism is not necessarily monomorphic. Still,
-- we call it 'sub'-coalgebra because it conveys the right intuition that
-- we use it to build (FA,Fα) from finite coalgebras.
module Iterate.FiniteSubcoalgebra {o ℓ} {fil-level}
  {o' ℓ' : Level } -- Level for diagram schemes
  (Fil : Category (o' ⊔ ℓ) (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ)  → Set fil-level) -- some variant of 'filtered'
  (proof-globals : ProofGlobals {o' = o'} {ℓ' = ℓ'} o ℓ Fil)
  where

open ProofGlobals proof-globals

-- In the proof, we consider commuting triangles of 𝒞-morphisms P→FA
-- that factor through some coalgebra-colimit injection:
--
--          P  -----> Carrier( F(A,α) )
--          |                     ^
--          |                     |
--          |                     |
--          '-------> Carrier( F(X,x) )
all-triangles =
  Σ[ P ∈ 𝒞p/FA.Obj ]
  Triangle F-coalg-colim (FA-colim.proj P)

-- In fact, every P can be extended to such a triangle, because
-- U-𝒞p/FA P is presentable and so it preserves the filtered colimit of the
-- coalgebra-colimit under (the postcomposition of) F:
DP-preserves-coalg-colim : ∀ (P : 𝒞p/FA.Obj) →
  preserves-colimit
    (F ∘F coalg-colim.carrier-diagram)
    LiftHom[ U-𝒞p/FA.₀ P ,-]
DP-preserves-coalg-colim P =
  let (idx , _) = P in
      𝒞-lfp.fin-presentable
        idx
        coalg-colim.𝒟 -- the diagram scheme
        𝒟-filtered    -- ... which is filtered
        (F ∘F coalg-colim.carrier-diagram)

-- And so we obtain a triangle for each P:
P-to-triangle : 𝒞p/FA.Obj → all-triangles
P-to-triangle P = P ,
  hom-colim-choice F-coalg-colim (U-𝒞p/FA.₀ P)
    (DP-preserves-coalg-colim P)
    (FA-colim.proj P)

-- In the following, we construct a presentable coalgebra
-- "below" (FA,Fα).
-- The construction uses multiple components, all parametric
-- in such a triangle, which we now fix globally:
module CC (t : all-triangles) where
  -- The first ingredient is the 'intermediate' coalgebra through which
  -- the triangle factors:
  X,x-dia : coalg-colim.𝒟.Obj -- the underlying object in the diagram scheme
  X,x-dia = Triangle.x (proj₂ t)
  X,x : F-Coalgebra F
  X,x = coalg-colim.D.₀ X,x-dia

  proj-X,x : F-Coalgebra-Morphism X,x A,α
  proj-X,x = coalg-colim.colim.proj (Triangle.x (proj₂ t))
  module proj-X,x = F-Coalgebra-Morphism proj-X,x

  -- We also introduce names for the carrier and the structure:
  open F-Coalgebra X,x renaming (A to X; α to x) public

  P : 𝒞.Obj
  P = U-𝒞p/FA.₀ (proj₁ t)

  p : P ⇒ F.₀ A
  p = FA-colim.proj (proj₁ t)

  P-is-presentable : presentable P
  P-is-presentable =
    -- here, we need to unfold the definition of P as a sliceobj
    -- from the index of a presentable object
    let (idx , _) = (proj₁ t) in
    𝒞-lfp.fin-presentable idx

  X-is-presentable : presentable X
  X-is-presentable = FiniteRecursive.finite-carrier coalg-colim.all-have-prop

  X,x-is-recursive : IsRecursive X,x
  X,x-is-recursive = FiniteRecursive.is-recursive coalg-colim.all-have-prop

  -- the constructed coalgebra has a coproduct as its carrier
  P+X : Coproduct P X
  P+X = 𝒞-lfp.coproduct P X P-is-presentable X-is-presentable
  module P+X = Coproduct P+X renaming (A+B to obj)

  p' : P ⇒ F.₀ X
  p' = Triangle.p' (proj₂ t)

  triangle-commutes : p ≈ F.₁ proj-X,x.f ∘ p'
  triangle-commutes = Triangle.commutes (proj₂ t)

  -- This p' is essentially unique in the sense that if there is another
  -- suitable p'', then p' and p'' are identified somewhere in the diagram
  p'-unique : ∀ (p'' : P ⇒ F.₀ X) → p ≈ F.₁ proj-X,x.f ∘ p'' →
    Σ[ Y,y-dia ∈ coalg-colim.𝒟.Obj ]
    Σ[ h ∈ coalg-colim.𝒟 [ X,x-dia , Y,y-dia ] ]
    F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ p' ≈ F.₁ (V.₁ (coalg-colim.D.₁ h)) ∘ p''
  p'-unique p'' p''-commutes =
    let open HomReasoning in
    coequalize-colimit-factorization
      F-coalg-colim
      P
      (Fil-to-filtered 𝒟-filtered)
      (hom-colim-unique-factor
          F-coalg-colim
          (Fil-to-filtered 𝒟-filtered)
          P
          (DP-preserves-coalg-colim
            (proj₁ t) F-coalg-colim))
      p' p''
      (begin
        F.₁ proj-X,x.f ∘ p'   ≈˘⟨ triangle-commutes ⟩
        p                     ≈⟨ p''-commutes ⟩
        F.₁ proj-X,x.f ∘ p''
        ∎)

  [p',x] : P+X.obj ⇒ F.₀ X
  [p',x] = P+X.[ p' , x ]

  -- the structure of the constructed coalgebra:
  Fi₂[p',x] : P+X.obj ⇒ F.₀ P+X.obj
  Fi₂[p',x] = F.₁ P+X.i₂ ∘ P+X.[ p' , x ]

  -- the combined constructed coalgebra
  P+X-coalg : F-Coalgebra F
  P+X-coalg = record { A = P+X.obj ; α = Fi₂[p',x] }

  -- The constructed coalgebra sits nicely between X,x and FX,Fx
  -- as we will see now:
  hom-from-X : F-Coalgebra-Morphism X,x P+X-coalg
  hom-from-X =
    record { f = P+X.i₂ ;
    commutes = begin
      Fi₂[p',x] ∘ P+X.i₂ ≈⟨ assoc ⟩
      F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ refl⟩∘⟨ P+X.inject₂ ⟩
      F.₁ P+X.i₂ ∘ x
      ∎}
    where
      open HomReasoning
  module hom-from-X = F-Coalgebra-Morphism hom-from-X

  hom-to-FX : F-Coalgebra-Morphism P+X-coalg (iterate X,x)
  hom-to-FX =
    record { f = P+X.[ p' , x ] ;
    commutes = begin
      F.₁ x ∘ P+X.[ p' , x ] ≈˘⟨ F.F-resp-≈ P+X.inject₂ ⟩∘⟨refl ⟩
      F.₁ (P+X.[ p' , x ] ∘ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
      (F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂) ∘ P+X.[ p' , x ] ≈⟨ assoc ⟩
      F.₁ P+X.[ p' , x ] ∘ F.₁ P+X.i₂ ∘ P+X.[ p' , x ] ≡⟨⟩
      F.₁ P+X.[ p' , x ] ∘ Fi₂[p',x]
      ∎}
    where
      open HomReasoning
  module hom-to-FX = F-Coalgebra-Morphism hom-to-FX

  hom-to-FA : F-Coalgebra-Morphism P+X-coalg (iterate A,α)
  hom-to-FA = (iterate-F-Coalgebra-Morphism proj-X,x) F-Coalgebras.∘ hom-to-FX
  module hom-to-FA = F-Coalgebra-Morphism hom-to-FA

  hom-to-FA-i₁ : p ≈ hom-to-FA.f ∘ P+X.i₁
  hom-to-FA-i₁ =
    begin
    p ≈⟨ triangle-commutes ⟩
    F.₁ proj-X,x.f ∘ p' ≈˘⟨ refl⟩∘⟨ P+X.inject₁ ⟩
    F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₁ ≈⟨ sym-assoc ⟩
    (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₁ ≡⟨⟩
    hom-to-FA.f ∘ P+X.i₁
    ∎
    where
      open HomReasoning

  hom-to-FA-i₂ : α ∘ proj-X,x.f ≈ hom-to-FA.f ∘ P+X.i₂
  hom-to-FA-i₂ =
    begin
    α ∘ proj-X,x.f ≈⟨ proj-X,x.commutes ⟩
    F.₁ proj-X,x.f ∘ x ≈˘⟨ refl⟩∘⟨ P+X.inject₂ ⟩
    F.₁ proj-X,x.f ∘ P+X.[ p' , x ] ∘ P+X.i₂ ≈⟨ sym-assoc ⟩
    (F.₁ proj-X,x.f ∘ hom-to-FX.f) ∘ P+X.i₂ ≡⟨⟩
    hom-to-FA.f ∘ P+X.i₂
    ∎
    where
      open HomReasoning

  P+X-is-presentable : presentable P+X.obj
  P+X-is-presentable =
        presentable-coproduct
          P+X Fil-to-filtered P-is-presentable X-is-presentable

  --   The property that all objects in the diagram ...
  P+X-coalg-is-FiniteRecursive : FiniteRecursive P+X-coalg
  P+X-coalg-is-FiniteRecursive =
    record {
      -- 1. .. have presentable carrier
      finite-carrier = P+X-is-presentable ;
      -- 2. .. are recursive:
      is-recursive =
        -- for recursiveness, we use our formalization of ([CUV06, Prop. 5])
        sandwich-recursive _ _ X,x-is-recursive hom-from-X hom-to-FX
          (let open HomReasoning in begin
          Fi₂[p',x] ≡⟨⟩ F.₁ hom-from-X.f ∘ hom-to-FX.f
          ∎)
      }

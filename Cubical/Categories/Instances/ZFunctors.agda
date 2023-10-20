{-

   The impredicative way to do the functor of points of qcqs-schemes
   (over Spec(ℤ))

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.ZFunctors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)

open import Cubical.Data.FinData
open import Cubical.Data.Int as Int
  renaming ( ℤ to ℤ ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)


open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)
open CommAlgebraHoms
-- open Cospan
-- open Pullback

private
 variable
  ℓ ℓ' ℓ'' : Level


module _ {ℓ : Level} where
  open Functor
  open NatTrans
  open ZarLat
  open ZarLatUniversalProp
  open CommRingStr ⦃...⦄
  open IsRingHom

  -- using the naming conventions of Nieper-Wisskirchen
  ℤFunctor = Functor (CommRingsCategory {ℓ = ℓ}) (SET ℓ)
  ℤFUNCTOR = FUNCTOR (CommRingsCategory {ℓ = ℓ}) (SET ℓ)

  -- Yoneda in the notation of Demazure-Gabriel
  -- uses that double op is original category definitionally
  Sp : Functor (CommRingsCategory {ℓ = ℓ} ^op) ℤFUNCTOR
  Sp = YO {C = (CommRingsCategory {ℓ = ℓ} ^op)}

  -- special functors to talk about schemes
  -- the Zariski lattice classifying compact open subobjects
  𝓛 : ℤFunctor
  F-ob 𝓛 A = ZL A , SQ.squash/
  F-hom 𝓛 φ = inducedZarLatHom φ .fst
  F-id 𝓛 {A} = cong fst (inducedZarLatHomId A)
  F-seq 𝓛 φ ψ = cong fst (inducedZarLatHomSeq φ ψ)

  -- the forgetful functor
  -- aka the affine line
  -- (aka the representable of ℤ[x])
  -- open Construction ℤCommRing
  -- private
  --   ℤ[x] : CommRing ℓ-zero
  --   ℤ[x] = CommAlgebra→CommRing (ℤCommRing [ Unit ])

  𝔸¹ : ℤFunctor
  𝔸¹ = ForgetfulCommRing→Set --Sp .F-ob ℤ[x]


  -- the big lattice of compact opens
  CompactOpen : ℤFunctor → Type (ℓ-suc ℓ)
  CompactOpen X = X ⇒ 𝓛

  -- the induced subfunctor
  ⟦_⟧ᶜᵒ : {X : ℤFunctor} (U : CompactOpen X)
        → ℤFunctor
  F-ob (⟦_⟧ᶜᵒ {X = X} U) A = (Σ[ x ∈ X .F-ob A .fst  ] U .N-ob A x ≡ D A 1r)
                                , isSetΣSndProp (X .F-ob A .snd) λ _ → squash/ _ _
   where instance _ = snd A
  F-hom (⟦_⟧ᶜᵒ {X = X} U) {x = A} {y = B} φ (x , Ux≡D1) = (X .F-hom φ x) , path
    where
    instance
      _ = A .snd
      _ = B .snd
    open IsLatticeHom
    path : U .N-ob B (X .F-hom φ x) ≡ D B 1r
    path = U .N-ob B (X .F-hom φ x) ≡⟨ funExt⁻ (U .N-hom φ) x ⟩
           𝓛 .F-hom φ (U .N-ob A x) ≡⟨ cong (𝓛 .F-hom φ) Ux≡D1 ⟩
           𝓛 .F-hom φ (D A 1r)      ≡⟨ inducedZarLatHom φ .snd .pres1 ⟩
           D B 1r ∎
  F-id (⟦_⟧ᶜᵒ {X = X} U) = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                     (funExt⁻ (X .F-id) (x .fst)))
  F-seq (⟦_⟧ᶜᵒ {X = X} U) φ ψ = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                          (funExt⁻ (X .F-seq φ ψ) (x .fst)))


  -- the global sections functor
  Γ : Functor ℤFUNCTOR (CommRingsCategory {ℓ-suc ℓ} ^op)
  fst (F-ob Γ X) = X ⇒ 𝔸¹
  -- ring struncture induced by internal ring object 𝔸¹
  N-ob (CommRingStr.0r (snd (F-ob Γ X))) A _ = 0r
    where instance _ = A .snd
  N-hom (CommRingStr.0r (snd (F-ob Γ X))) φ = funExt λ _ → sym (φ .snd .pres0)
  N-ob (CommRingStr.1r (snd (F-ob Γ X))) A _ = 1r
    where instance _ = A .snd
  N-hom (CommRingStr.1r (snd (F-ob Γ X))) φ = funExt λ _ → sym (φ .snd .pres1)
  N-ob ((snd (F-ob Γ X) CommRingStr.+ α) β) A x = α .N-ob A x + β .N-ob A x
    where instance _ = A .snd
  N-hom ((snd (F-ob Γ X) CommRingStr.+ α) β) {x = A} {y = B} φ = funExt path
    where
    instance
      _ = A .snd
      _ = B .snd
    path : ∀ x → α .N-ob B (X .F-hom φ x) + β .N-ob B (X .F-hom φ x)
               ≡ φ .fst (α .N-ob A x + β .N-ob A x)
    path x = α .N-ob B (X .F-hom φ x) + β .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _+_ (funExt⁻ (α .N-hom φ) x) (funExt⁻ (β .N-hom φ) x) ⟩
             φ .fst (α .N-ob A x) + φ .fst (β .N-ob A x)
           ≡⟨ sym (φ .snd .pres+ _ _) ⟩
             φ .fst (α .N-ob A x + β .N-ob A x) ∎
  N-ob ((snd (F-ob Γ X) CommRingStr.· α) β) A x = α .N-ob A x · β .N-ob A x
    where instance _ = A .snd
  N-hom ((snd (F-ob Γ X) CommRingStr.· α) β) {x = A} {y = B} φ = funExt path
    where
    instance
      _ = A .snd
      _ = B .snd
    path : ∀ x → α .N-ob B (X .F-hom φ x) · β .N-ob B (X .F-hom φ x)
               ≡ φ .fst (α .N-ob A x · β .N-ob A x)
    path x = α .N-ob B (X .F-hom φ x) · β .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _·_ (funExt⁻ (α .N-hom φ) x) (funExt⁻ (β .N-hom φ) x) ⟩
             φ .fst (α .N-ob A x) · φ .fst (β .N-ob A x)
           ≡⟨ sym (φ .snd .pres· _ _) ⟩
             φ .fst (α .N-ob A x · β .N-ob A x) ∎
  N-ob ((CommRingStr.- snd (F-ob Γ X)) α) A x = - α .N-ob A x
    where instance _ = A .snd
  N-hom ((CommRingStr.- snd (F-ob Γ X)) α) {x = A} {y = B} φ = funExt path
    where
    instance
      _ = A .snd
      _ = B .snd
    path : ∀ x → - α .N-ob B (X .F-hom φ x) ≡ φ .fst (- α .N-ob A x)
    path x = - α .N-ob B (X .F-hom φ x) ≡⟨ cong -_ (funExt⁻ (α .N-hom φ) x) ⟩
             - φ .fst (α .N-ob A x)     ≡⟨ sym (φ .snd .pres- _) ⟩
             φ .fst (- α .N-ob A x)     ∎

  CommRingStr.isCommRing (snd (F-ob Γ X)) = makeIsCommRing
    isSetNatTrans
    (λ _ _ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.+Assoc _ _ _))
    (λ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.+IdR _))
    (λ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.+InvR _))
    (λ _ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.+Comm _ _))
    (λ _ _ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.·Assoc _ _ _))
    (λ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.·IdR _))
    (λ _ _ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.·DistR+ _ _ _))
    (λ _ _ → makeNatTransPath (funExt₂ λ A _ → A .snd .CommRingStr.·Comm _ _))

  -- action on natural transformations
  fst (F-hom Γ α) = α ●ᵛ_
  pres0 (snd (F-hom Γ α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres1 (snd (F-hom Γ α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres+ (snd (F-hom Γ α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres· (snd (F-hom Γ α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres- (snd (F-hom Γ α)) _ = makeNatTransPath (funExt₂ λ _ _ → refl)

  -- functoriality of Γ
  F-id Γ = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))
  F-seq Γ _ _ = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))


-- we get an adjunction Γ ⊣ Sp modulo size issues
-- note that we can't write unit and counit as
-- elements of type NatTrans because the type CommRingHom
-- ends up living in the next higher universe
open Functor
open NatTrans
open Iso
open IsRingHom


ΓSpOb : (A : CommRing ℓ) → CommRingHom ((Γ ∘F Sp) .F-ob A) A
fst (ΓSpOb A) α = yonedaᴾ 𝔸¹ A .fun α
pres0 (snd (ΓSpOb A)) = refl
pres1 (snd (ΓSpOb A)) = refl
pres+ (snd (ΓSpOb A)) _ _ = refl
pres· (snd (ΓSpOb A)) _ _ = refl
pres- (snd (ΓSpOb A)) _ = refl

ΓSpHom : {A B : CommRing ℓ} (φ : CommRingHom A B)
       → φ ∘cr ΓSpOb A ≡  ΓSpOb B ∘cr ((Γ ∘F Sp) .F-hom φ)
ΓSpHom {A = A} {B = B} φ = RingHom≡ (funExt funExtHelper)
  where
  funExtHelper : ∀ (α : Sp .F-ob A ⇒ 𝔸¹)
               → φ .fst (yonedaᴾ 𝔸¹ A .fun α) ≡ yonedaᴾ 𝔸¹ B .fun (Sp .F-hom φ ●ᵛ α)
  funExtHelper α =  funExt⁻ (sym (yonedaIsNaturalInOb {F = 𝔸¹} A B φ))
                            (record { N-ob = α .N-ob ; N-hom = α .N-hom })
                            -- hack because Functor doesn't have η-equality


SpΓObOb : (X : ℤFunctor) (A : CommRing ℓ)
      → X .F-ob A .fst → CommRingHom (Γ .F-ob X) A
fst (SpΓObOb X A x) α = α .N-ob A x
pres0 (snd (SpΓObOb X A x)) = refl
pres1 (snd (SpΓObOb X A x)) = refl
pres+ (snd (SpΓObOb X A x)) _ _ = refl
pres· (snd (SpΓObOb X A x)) _ _ = refl
pres- (snd (SpΓObOb X A x)) _ = refl


-- isAffine : (X : ℤFunctor {ℓ = ℓ}) → Type (ℓ-suc ℓ)
-- isAffine X = ∀ (A : CommRing _) → isEquiv (SpΓObOb X A)
-- TODO equivalence with naive def:

-- the rest of the "quasi natural transoformation"
SpΓObHom : (X : ℤFunctor) {A B : CommRing ℓ} (φ : CommRingHom A B)
         → SpΓObOb X B ∘ (X .F-hom φ) ≡ (φ ∘cr_) ∘ SpΓObOb X A
SpΓObHom X {A = A} {B = B} φ = funExt funExtHelper
  where
  funExtHelper : ∀ (x : X .F-ob A .fst)
               → SpΓObOb X B (X .F-hom φ x) ≡ φ ∘cr (SpΓObOb X A x)
  funExtHelper x = RingHom≡ (funExt funExtHelper2)
    where
    funExtHelper2 : ∀ (α : X ⇒ 𝔸¹)
                  → α .N-ob B (X .F-hom φ x) ≡ φ .fst (α .N-ob A x)
    funExtHelper2 α = funExt⁻ (α .N-hom φ) x


-- can only state equality on object part, but that would be enough
SpΓHom : {X Y : ℤFunctor} (α : X ⇒ Y) (A : CommRing ℓ) (x : X .F-ob A .fst)
       → SpΓObOb Y A (α .N-ob A x) ≡ SpΓObOb X A x ∘cr Γ .F-hom α
SpΓHom _ _ _ = RingHom≡ refl

-- TODO: can you state the triangle identities in a reasonable form?

module AdjBij where

  private module _ {A : CommRing ℓ} {X : ℤFunctor {ℓ}} where
    _♭ : CommRingHom A (Γ .F-ob X) → X ⇒ Sp .F-ob A
    fst (N-ob (φ ♭) B x) a = φ .fst a .N-ob B x

    pres0 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres0)
    pres1 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres1)
    pres+ (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres+ _ _)
    pres· (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres· _ _)
    pres- (snd (N-ob (φ ♭) B x)) _ = cong (λ y → y .N-ob B x) (φ .snd .pres- _)

    N-hom (φ ♭) ψ = funExt (λ x → RingHom≡ (funExt λ a → funExt⁻ (φ .fst a .N-hom ψ) x))


    -- the other direction is just precomposition modulo Yoneda
    _♯ : X ⇒ Sp .F-ob A → CommRingHom A (Γ .F-ob X)
    fst (α ♯) a = α ●ᵛ yonedaᴾ 𝔸¹ A .inv a

    pres0 (snd (α ♯)) = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres0)
    pres1 (snd (α ♯)) = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres1)
    pres+ (snd (α ♯)) _ _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres+ _ _)
    pres· (snd (α ♯)) _ _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres· _ _)
    pres- (snd (α ♯)) _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres- _)


    -- the two maps are inverse to each other
    ♭♯Id : ∀ (α  : X ⇒ Sp .F-ob A) → ((α ♯) ♭) ≡ α
    ♭♯Id _ = makeNatTransPath (funExt₂ λ _ _ → RingHom≡ (funExt (λ _ → refl)))

    ♯♭Id : ∀ (φ : CommRingHom A (Γ .F-ob X)) → ((φ ♭) ♯) ≡ φ
    ♯♭Id _ = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))

  Γ⊣SpIso : {A : CommRing ℓ} {X : ℤFunctor {ℓ}}
         → Iso (CommRingHom A (Γ .F-ob X)) (X ⇒ Sp .F-ob A)
  fun Γ⊣SpIso = _♭
  inv Γ⊣SpIso = _♯
  rightInv Γ⊣SpIso = ♭♯Id
  leftInv Γ⊣SpIso = ♯♭Id

  Γ⊣SpNatℤFunctor : {A : CommRing ℓ} {X Y : ℤFunctor {ℓ}} (α : X ⇒ Sp .F-ob A) (β : Y ⇒ X)
                  → (β ●ᵛ α) ♯ ≡ (Γ .F-hom β) ∘cr (α ♯)
  Γ⊣SpNatℤFunctor _ _ = RingHom≡ (funExt (λ _ → makeNatTransPath (funExt₂ (λ _ _ → refl))))

  Γ⊣SpNatCommRing : {X : ℤFunctor {ℓ}} {A B : CommRing ℓ}
                    (φ : CommRingHom A (Γ .F-ob X)) (ψ : CommRingHom B A)
                  → (φ ∘cr ψ) ♭ ≡ (φ ♭) ●ᵛ Sp .F-hom ψ
  Γ⊣SpNatCommRing _ _ = makeNatTransPath (funExt₂ λ _ _ → RingHom≡ (funExt (λ _ → refl)))

  -- the counit is an equivalence
  private
    ε : (A : CommRing ℓ) → CommRingHom A ((Γ ∘F Sp) .F-ob A)
    ε A = (idTrans (Sp .F-ob A)) ♯

  Γ⊣SpCounitEquiv : (A : CommRing ℓ) → CommRingEquiv A ((Γ ∘F Sp) .F-ob A)
  fst (Γ⊣SpCounitEquiv A) = isoToEquiv theIso
    where
    theIso : Iso (A .fst) ((Γ ∘F Sp) .F-ob A .fst)
    fun theIso = ε A .fst
    inv theIso = yonedaᴾ 𝔸¹ A .fun
    rightInv theIso α = ℤFUNCTOR .⋆IdL _ ∙ yonedaᴾ 𝔸¹ A .leftInv α
    leftInv theIso a = path -- I get yellow otherwise
      where
      path : yonedaᴾ 𝔸¹ A .fun ((idTrans (Sp .F-ob A)) ●ᵛ yonedaᴾ 𝔸¹ A .inv a) ≡ a
      path = cong (yonedaᴾ 𝔸¹ A .fun) (ℤFUNCTOR .⋆IdL _) ∙ yonedaᴾ 𝔸¹ A .rightInv a
  snd (Γ⊣SpCounitEquiv A) = ε A .snd


module _ {ℓ : Level} where
  isAffine : (X : ℤFunctor {ℓ = ℓ}) → Type (ℓ-suc ℓ)
  isAffine X = ∃[ A ∈ CommRing ℓ ] CommRingEquiv A (Γ .F-ob X)

-- The unit is an equivalence iff the ℤ-functor is affine
-- unfortunately, we can't give a natural transformation
-- X ⇒ Sp (Γ X), because the latter ℤ-functor lives in a higher universe.
-- we can however give terms that look just like the unit,
-- giving us an alternative def. of affine ℤ-functors
module AffineDefs {ℓ : Level} where

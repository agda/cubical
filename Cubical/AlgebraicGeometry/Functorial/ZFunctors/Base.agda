{-

  A ℤ-functor is just a functor from rings to sets.

  NOTE: we consider the functor category [ Ring ℓ , Set ℓ ] for some universe level ℓ
        and not [ Ring ℓ , Set (ℓ+1) ] as is done in
        "Introduction to Algebraic Geometry and Algebraic Groups"
        by Demazure & Gabriel!

  The category of ℤ-functors contains the category of (qcqs-) schemes
  as a full subcategory and satisfies a "universal property"
  similar to the one of schemes:

    There is a coadjunction 𝓞 ⊣ᵢ Sp
    (relative to the inclusion i : CommRing ℓ → CommRing (ℓ+1))
    between the "global sections functor" 𝓞
    and the fully-faithful embedding of affines Sp,
    whose counit is a natural isomorphism

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Site.Instances.ZariskiCommRing

open import Cubical.HITs.PropositionalTruncation as PT


open Category hiding (_∘_)


module _ {ℓ : Level} where

  open Functor
  open NatTrans
  open CommRingStr ⦃...⦄
  open IsCommRingHom

  Aff : Category (ℓ-suc ℓ) ℓ
  Aff = CommRingsCategory {ℓ = ℓ} ^op

  -- using the naming conventions of Demazure & Gabriel
  ℤFunctor = Presheaf Aff ℓ
  ℤFUNCTOR = PresheafCategory Aff ℓ

  -- Yoneda in the notation of Demazure & Gabriel,
  -- uses that double op is original category definitionally
  Sp : Functor Aff ℤFUNCTOR
  Sp = YO

  -- TODO: should probably just be hasUniversalElement
  isAffine : (X : ℤFunctor) → Type (ℓ-suc ℓ)
  isAffine X = ∃[ A ∈ CommRing ℓ ] NatIso (Sp .F-ob A) X
  -- TODO: 𝔸¹ ≅ Sp ℤ[x] and 𝔾ₘ ≅ Sp ℤ[x,x⁻¹] ≅ D(x) ↪ 𝔸¹ as first examples of affine schemes

  -- a ℤ-functor that is a sheaf wrt the Zariski coverage is called local
  isLocal : ℤFunctor → Type (ℓ-suc ℓ)
  isLocal X = isSheaf zariskiCoverage X

  -- the forgetful functor
  -- aka the affine line
  -- (aka the representable of ℤ[x])
  𝔸¹ : ℤFunctor
  𝔸¹ = ForgetfulCommRing→Set ∘F fromOpOp

  -- the global sections functor
  𝓞 : Functor ℤFUNCTOR (CommRingsCategory {ℓ = ℓ-suc ℓ} ^op)
  fst (F-ob 𝓞 X) = X ⇒ 𝔸¹

  -- ring struncture induced by internal ring object 𝔸¹
  N-ob (CommRingStr.0r (snd (F-ob 𝓞 X))) A _ = 0r
    where instance _ = A .snd
  N-hom (CommRingStr.0r (snd (F-ob 𝓞 X))) φ = funExt λ _ → sym (φ .snd .pres0)

  N-ob (CommRingStr.1r (snd (F-ob 𝓞 X))) A _ = 1r
    where instance _ = A .snd
  N-hom (CommRingStr.1r (snd (F-ob 𝓞 X))) φ = funExt λ _ → sym (φ .snd .pres1)

  N-ob ((snd (F-ob 𝓞 X) CommRingStr.+ α) β) A x = α .N-ob A x + β .N-ob A x
    where instance _ = A .snd
  N-hom ((snd (F-ob 𝓞 X) CommRingStr.+ α) β) {x = A} {y = B} φ = funExt path
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

  N-ob ((snd (F-ob 𝓞 X) CommRingStr.· α) β) A x = α .N-ob A x · β .N-ob A x
    where instance _ = A .snd
  N-hom ((snd (F-ob 𝓞 X) CommRingStr.· α) β) {x = A} {y = B} φ = funExt path
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

  N-ob ((CommRingStr.- snd (F-ob 𝓞 X)) α) A x = - α .N-ob A x
    where instance _ = A .snd
  N-hom ((CommRingStr.- snd (F-ob 𝓞 X)) α) {x = A} {y = B} φ = funExt path
    where
    instance
      _ = A .snd
      _ = B .snd
    path : ∀ x → - α .N-ob B (X .F-hom φ x) ≡ φ .fst (- α .N-ob A x)
    path x = - α .N-ob B (X .F-hom φ x) ≡⟨ cong -_ (funExt⁻ (α .N-hom φ) x) ⟩
             - φ .fst (α .N-ob A x)     ≡⟨ sym (φ .snd .pres- _) ⟩
             φ .fst (- α .N-ob A x)     ∎

  CommRingStr.isCommRing (snd (F-ob 𝓞 X)) = makeIsCommRing
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
  fst (F-hom 𝓞 α) = α ●ᵛ_
  pres0 (snd (F-hom 𝓞 α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres1 (snd (F-hom 𝓞 α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres+ (snd (F-hom 𝓞 α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres· (snd (F-hom 𝓞 α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres- (snd (F-hom 𝓞 α)) _ = makeNatTransPath (funExt₂ λ _ _ → refl)

  -- functoriality of 𝓞
  F-id 𝓞 = CommRingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))
  F-seq 𝓞 _ _ = CommRingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))



-- There is a coadjunction 𝓞 ⊣ᵢ Sp
-- (relative to the inclusion i : CommRing ℓ → CommRing (ℓ+1))
-- between the "global sections functor" 𝓞
-- and the fully-faithful embedding of affines Sp,
-- whose counit is a natural isomorphism
module AdjBij {ℓ : Level} where

  open Functor
  open NatTrans
  open Iso
  open IsCommRingHom

  private module _ {A : CommRing ℓ} {X : ℤFunctor {ℓ}} where
    _♭ : CommRingHom A (𝓞 .F-ob X) → X ⇒ Sp .F-ob A
    fst (N-ob (φ ♭) B x) a = φ .fst a .N-ob B x

    pres0 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres0)
    pres1 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres1)
    pres+ (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres+ _ _)
    pres· (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres· _ _)
    pres- (snd (N-ob (φ ♭) B x)) _ = cong (λ y → y .N-ob B x) (φ .snd .pres- _)

    N-hom (φ ♭) ψ = funExt (λ x → CommRingHom≡ (funExt λ a → funExt⁻ (φ .fst a .N-hom ψ) x))


    -- the other direction is just precomposition modulo Yoneda
    _♯ : X ⇒ Sp .F-ob A → CommRingHom A (𝓞 .F-ob X)
    fst (α ♯) a = α ●ᵛ yonedaᴾ 𝔸¹ A .inv a

    pres0 (snd (α ♯)) = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres0)
    pres1 (snd (α ♯)) = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres1)
    pres+ (snd (α ♯)) _ _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres+ _ _)
    pres· (snd (α ♯)) _ _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres· _ _)
    pres- (snd (α ♯)) _ = makeNatTransPath (funExt₂ λ B x → α .N-ob B x .snd .pres- _)


    -- the two maps are inverse to each other
    ♭♯Id : ∀ (α  : X ⇒ Sp .F-ob A) → ((α ♯) ♭) ≡ α
    ♭♯Id _ = makeNatTransPath (funExt₂ λ _ _ → CommRingHom≡ (funExt (λ _ → refl)))

    ♯♭Id : ∀ (φ : CommRingHom A (𝓞 .F-ob X)) → ((φ ♭) ♯) ≡ φ
    ♯♭Id _ = CommRingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))


  -- we get a relative adjunction 𝓞 ⊣ᵢ Sp
  -- with respect to the inclusion i : CommRing ℓ → CommRing (ℓ+1)
  𝓞⊣SpIso : {A : CommRing ℓ} {X : ℤFunctor {ℓ}}
          → Iso (CommRingHom A (𝓞 .F-ob X)) (X ⇒ Sp .F-ob A)
  fun 𝓞⊣SpIso = _♭
  inv 𝓞⊣SpIso = _♯
  rightInv 𝓞⊣SpIso = ♭♯Id
  leftInv 𝓞⊣SpIso = ♯♭Id

  𝓞⊣SpNatℤFunctor : {A : CommRing ℓ} {X Y : ℤFunctor {ℓ}} (α : X ⇒ Sp .F-ob A) (β : Y ⇒ X)
                  → (β ●ᵛ α) ♯ ≡ (𝓞 .F-hom β) ∘cr (α ♯)
  𝓞⊣SpNatℤFunctor _ _ = CommRingHom≡ (funExt (λ _ → makeNatTransPath (funExt₂ (λ _ _ → refl))))

  𝓞⊣SpNatCommRing : {X : ℤFunctor {ℓ}} {A B : CommRing ℓ}
                    (φ : CommRingHom A (𝓞 .F-ob X)) (ψ : CommRingHom B A)
                  → (φ ∘cr ψ) ♭ ≡ (φ ♭) ●ᵛ Sp .F-hom ψ
  𝓞⊣SpNatCommRing _ _ = makeNatTransPath (funExt₂ λ _ _ → CommRingHom≡ (funExt (λ _ → refl)))

  -- the counit is an equivalence
  private
    ε : (A : CommRing ℓ) → CommRingHom A ((𝓞 ∘F Sp) .F-ob A)
    ε A = (idTrans (Sp .F-ob A)) ♯

  𝓞⊣SpCounitEquiv : (A : CommRing ℓ) → CommRingEquiv A ((𝓞 ∘F Sp) .F-ob A)
  fst (𝓞⊣SpCounitEquiv A) = isoToEquiv theIso
    where
    theIso : Iso (A .fst) ((𝓞 ∘F Sp) .F-ob A .fst)
    fun theIso = ε A .fst
    inv theIso = yonedaᴾ 𝔸¹ A .fun
    rightInv theIso α = ℤFUNCTOR .⋆IdL _ ∙ yonedaᴾ 𝔸¹ A .leftInv α
    leftInv theIso a = path -- I get yellow otherwise
      where
      path : yonedaᴾ 𝔸¹ A .fun ((idTrans (Sp .F-ob A)) ●ᵛ yonedaᴾ 𝔸¹ A .inv a) ≡ a
      path = cong (yonedaᴾ 𝔸¹ A .fun) (ℤFUNCTOR .⋆IdL _) ∙ yonedaᴾ 𝔸¹ A .rightInv a
  snd (𝓞⊣SpCounitEquiv A) = ε A .snd

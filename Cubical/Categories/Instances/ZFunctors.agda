{-

   The impredicative way to define functorial qcqs-schemes (over Spec(ℤ))

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.ZFunctors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels


open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Site.Instances.ZariskiCommRing
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Relation.Binary.Order.Poset

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)

private
 variable
  ℓ ℓ' ℓ'' : Level


module _ {ℓ : Level} where

  open Functor
  open NatTrans
  open CommRingStr ⦃...⦄
  open IsRingHom

  -- using the naming conventions of Demazure & Gabriel
  ℤFunctor = Functor (CommRingsCategory {ℓ = ℓ}) (SET ℓ)
  ℤFUNCTOR = FUNCTOR (CommRingsCategory {ℓ = ℓ}) (SET ℓ)

  -- Yoneda in the notation of Demazure & Gabriel,
  -- uses that double op is original category definitionally
  Sp : Functor (CommRingsCategory {ℓ = ℓ} ^op) ℤFUNCTOR
  Sp = YO {C = (CommRingsCategory {ℓ = ℓ} ^op)}

  -- the forgetful functor
  -- aka the affine line
  -- (aka the representable of ℤ[x])
  𝔸¹ : ℤFunctor
  𝔸¹ = ForgetfulCommRing→Set

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
  F-id 𝓞 = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))
  F-seq 𝓞 _ _ = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))



-- There is an adjunction 𝓞 ⊣ᵢ Sp
-- (relative to the inclusion i : CommRing ℓ → CommRing (ℓ+1))
-- between the "global sections functor" 𝓞
-- and the fully-faithful embedding of affines Sp,
-- whose counit is a natural isomorphism
module AdjBij where

  open Functor
  open NatTrans
  open Iso
  open IsRingHom

  private module _ {A : CommRing ℓ} {X : ℤFunctor {ℓ}} where
    _♭ : CommRingHom A (𝓞 .F-ob X) → X ⇒ Sp .F-ob A
    fst (N-ob (φ ♭) B x) a = φ .fst a .N-ob B x

    pres0 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres0)
    pres1 (snd (N-ob (φ ♭) B x)) = cong (λ y → y .N-ob B x) (φ .snd .pres1)
    pres+ (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres+ _ _)
    pres· (snd (N-ob (φ ♭) B x)) _ _ = cong (λ y → y .N-ob B x) (φ .snd .pres· _ _)
    pres- (snd (N-ob (φ ♭) B x)) _ = cong (λ y → y .N-ob B x) (φ .snd .pres- _)

    N-hom (φ ♭) ψ = funExt (λ x → RingHom≡ (funExt λ a → funExt⁻ (φ .fst a .N-hom ψ) x))


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
    ♭♯Id _ = makeNatTransPath (funExt₂ λ _ _ → RingHom≡ (funExt (λ _ → refl)))

    ♯♭Id : ∀ (φ : CommRingHom A (𝓞 .F-ob X)) → ((φ ♭) ♯) ≡ φ
    ♯♭Id _ = RingHom≡ (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))


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
  𝓞⊣SpNatℤFunctor _ _ = RingHom≡ (funExt (λ _ → makeNatTransPath (funExt₂ (λ _ _ → refl))))

  𝓞⊣SpNatCommRing : {X : ℤFunctor {ℓ}} {A B : CommRing ℓ}
                    (φ : CommRingHom A (𝓞 .F-ob X)) (ψ : CommRingHom B A)
                  → (φ ∘cr ψ) ♭ ≡ (φ ♭) ●ᵛ Sp .F-hom ψ
  𝓞⊣SpNatCommRing _ _ = makeNatTransPath (funExt₂ λ _ _ → RingHom≡ (funExt (λ _ → refl)))

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


-- Affine schemes
module _ {ℓ : Level} where
  open Functor

  isAffine : (X : ℤFunctor) → Type (ℓ-suc ℓ)
  isAffine X = ∃[ A ∈ CommRing ℓ ] NatIso (Sp .F-ob A) X

  -- TODO: 𝔸¹ ≅ Sp ℤ[x] and 𝔾ₘ ≅ Sp ℤ[x,x⁻¹] as first examples of affine schemes


-- The unit is an equivalence iff the ℤ-functor is affine.
-- Unfortunately, we can't give a natural transformation
-- X ⇒ Sp (𝓞 X), because the latter ℤ-functor lives in a higher universe.
-- We can however give terms that look just like the unit,
-- giving us an alternative def. of affine ℤ-functors
private module AffineDefs {ℓ : Level} where
  open Functor
  open NatTrans
  open Iso
  open IsRingHom
  η : (X : ℤFunctor) (A : CommRing ℓ) → X .F-ob A .fst → CommRingHom (𝓞 .F-ob X) A
  fst (η X A x) α = α .N-ob A x
  pres0 (snd (η X A x)) = refl
  pres1 (snd (η X A x)) = refl
  pres+ (snd (η X A x)) _ _ = refl
  pres· (snd (η X A x)) _ _ = refl
  pres- (snd (η X A x)) _ = refl

  -- this is basically a natural transformation
  ηObHom : (X : ℤFunctor) {A B : CommRing ℓ} (φ : CommRingHom A B)
           → η X B ∘ (X .F-hom φ) ≡ (φ ∘cr_) ∘ η X A
  ηObHom X φ = funExt (λ x → RingHom≡ (funExt λ α → funExt⁻ (α .N-hom φ) x))

  -- can only state equality on object part, but that would be enough
  ηHom : {X Y : ℤFunctor} (α : X ⇒ Y) (A : CommRing ℓ) (x : X .F-ob A .fst)
         → η Y A (α .N-ob A x) ≡ η X A x ∘cr 𝓞 .F-hom α
  ηHom _ _ _ = RingHom≡ refl

  isAffine' : (X : ℤFunctor) → Type (ℓ-suc ℓ)
  isAffine' X = ∀ (A : CommRing ℓ) → isEquiv (η X A)
  -- TODO: isAffine → isAffine'


-- compact opens and affine covers
module _ {ℓ : Level} where

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open IsRingHom
  open IsLatticeHom
  open ZarLat
  open ZarLatUniversalProp

  -- the Zariski lattice classifying compact open subobjects
  ZarLatFun : ℤFunctor {ℓ = ℓ}
  F-ob ZarLatFun A = ZL A , SQ.squash/
  F-hom ZarLatFun φ = inducedZarLatHom φ .fst
  F-id ZarLatFun {A} = cong fst (inducedZarLatHomId A)
  F-seq ZarLatFun φ ψ = cong fst (inducedZarLatHomSeq φ ψ)

  CompactOpen : ℤFunctor → Type (ℓ-suc ℓ)
  CompactOpen X = X ⇒ ZarLatFun

  -- the induced subfunctor
  ⟦_⟧ᶜᵒ : {X : ℤFunctor} (U : CompactOpen X) → ℤFunctor
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
    path = U .N-ob B (X .F-hom φ x)         ≡⟨ funExt⁻ (U .N-hom φ) x ⟩
           ZarLatFun .F-hom φ (U .N-ob A x) ≡⟨ cong (ZarLatFun .F-hom φ) Ux≡D1 ⟩
           ZarLatFun .F-hom φ (D A 1r)      ≡⟨ inducedZarLatHom φ .snd .pres1 ⟩
           D B 1r ∎
  F-id (⟦_⟧ᶜᵒ {X = X} U) = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                     (funExt⁻ (X .F-id) (x .fst)))
  F-seq (⟦_⟧ᶜᵒ {X = X} U) φ ψ = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                          (funExt⁻ (X .F-seq φ ψ) (x .fst)))


  isAffineCompactOpen : {X : ℤFunctor} (U : CompactOpen X) → Type (ℓ-suc ℓ)
  isAffineCompactOpen U = isAffine ⟦ U ⟧ᶜᵒ

  -- TODO: define basic opens D(f) ↪ Sp A and prove ⟦ D(f) ⟧ᶜᵒ ≅ Sp A[1/f]

  -- the (big) dist. lattice of compact opens
  CompOpenDistLattice : Functor ℤFUNCTOR (DistLatticesCategory {ℓ = ℓ-suc ℓ} ^op)
  fst (F-ob CompOpenDistLattice X) = CompactOpen X

  -- lattice structure induce by internal lattice object ZarLatFun
  N-ob (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) A _ = 0l
    where instance _ = ZariskiLattice A .snd
  N-hom (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) _ = funExt λ _ → refl

  N-ob (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) A _ = 1l
    where instance _ = ZariskiLattice A .snd
  N-hom (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) {x = A} {y = B} φ = funExt λ _ → path
    where
    instance
      _ = A .snd
      _ = B .snd
      _ = ZariskiLattice B .snd
    path : D B 1r ≡ D B (φ .fst 1r) ∨l 0l
    path = cong (D B) (sym (φ .snd .pres1)) ∙ sym (∨lRid _)

  N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V) A x = U .N-ob A x ∨l V .N-ob A x
    where instance _ = ZariskiLattice A .snd
  N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V)  {x = A} {y = B} φ = funExt path
    where
    instance
      _ = ZariskiLattice A .snd
      _ = ZariskiLattice B .snd
    path : ∀ x → U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
               ≡ ZarLatFun .F-hom φ (U .N-ob A x ∨l V .N-ob A x)
    path x = U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _∨l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x) ∨l ZarLatFun .F-hom φ (V .N-ob A x)
           ≡⟨ sym (inducedZarLatHom φ .snd .pres∨l _ _) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x ∨l V .N-ob A x) ∎

  N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V) A x = U .N-ob A x ∧l V .N-ob A x
    where instance _ = ZariskiLattice A .snd
  N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V)  {x = A} {y = B} φ = funExt path
    where
    instance
      _ = ZariskiLattice A .snd
      _ = ZariskiLattice B .snd
    path : ∀ x → U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
               ≡ ZarLatFun .F-hom φ (U .N-ob A x ∧l V .N-ob A x)
    path x = U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _∧l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x) ∧l ZarLatFun .F-hom φ (V .N-ob A x)
           ≡⟨ sym (inducedZarLatHom φ .snd .pres∧l _ _) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x ∧l V .N-ob A x) ∎

  DistLatticeStr.isDistLattice (snd (F-ob CompOpenDistLattice X)) = makeIsDistLattice∧lOver∨l
    isSetNatTrans
    (λ _ _ _ → makeNatTransPath (funExt₂
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lAssoc _ _ _)))
    (λ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lRid _)))
    (λ _ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lComm _ _)))
    (λ _ _ _ → makeNatTransPath (funExt₂
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lAssoc _ _ _)))
    (λ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lRid _)))
    (λ _ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lComm _ _)))
    (λ _ _ → makeNatTransPath (funExt₂ -- don't know why ∧lAbsorb∨l doesn't work
               (λ A _ → ZariskiLattice A .snd .DistLatticeStr.absorb _ _ .snd)))
    (λ _ _ _ → makeNatTransPath (funExt₂ -- same here
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧l-dist-∨l _ _ _ .fst)))

  -- (contravariant) action on morphisms
  fst (F-hom CompOpenDistLattice α) = α ●ᵛ_
  pres0 (snd (F-hom CompOpenDistLattice α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres1 (snd (F-hom CompOpenDistLattice α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres∨l (snd (F-hom CompOpenDistLattice α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
  pres∧l (snd (F-hom CompOpenDistLattice α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)

  -- functoriality
  F-id CompOpenDistLattice = LatticeHom≡f _ _
                               (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))
  F-seq CompOpenDistLattice _ _ = LatticeHom≡f _ _
                                    (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))


  module _ (X : ℤFunctor) where
    open isIso
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    compOpenTopNatIso : NatIso X ⟦ 1l ⟧ᶜᵒ
    N-ob (trans compOpenTopNatIso) _ φ = φ , refl
    N-hom (trans compOpenTopNatIso) _ = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    inv (nIso compOpenTopNatIso B) = fst
    sec (nIso compOpenTopNatIso B) = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    ret (nIso compOpenTopNatIso B) = funExt λ _ → refl


  module _ (X : ℤFunctor) where
    open Join (CompOpenDistLattice .F-ob X)
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob X)))
    open PosetStr (IndPoset .snd) hiding (_≤_)
    open LatticeTheory ⦃...⦄
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    record AffineCover : Type (ℓ-suc ℓ) where
      field
        n : ℕ
        U : FinVec (CompactOpen X) n
        covers : ⋁ U ≡ 1l -- TODO: equivalent to X ≡ ⟦ ⋁ U ⟧ᶜᵒ
        isAffineU : ∀ i → isAffineCompactOpen (U i)

    hasAffineCover : Type (ℓ-suc ℓ)
    hasAffineCover = ∥ AffineCover ∥₁

    -- the structure sheaf
    private COᵒᵖ = (DistLatticeCategory (CompOpenDistLattice .F-ob X)) ^op

    compOpenIncl : {U V : CompactOpen X} → V ≤ U → ⟦ V ⟧ᶜᵒ ⇒ ⟦ U ⟧ᶜᵒ
    N-ob (compOpenIncl {U = U} {V = V} V≤U) A (x , Vx≡D1) = x , path
      where
      instance
        _ = A .snd
        _ = ZariskiLattice A .snd
        _ = DistLattice→Lattice (ZariskiLattice A)
      path : U .N-ob A x ≡ D A 1r
      path = U .N-ob A x                ≡⟨ funExt⁻ (funExt⁻ (cong N-ob (sym V≤U)) A) x ⟩
             V .N-ob A x ∨l U .N-ob A x ≡⟨ cong (_∨l U .N-ob A x) Vx≡D1 ⟩
             D A 1r ∨l U .N-ob A x      ≡⟨ 1lLeftAnnihilates∨l _ ⟩
             D A 1r ∎
    N-hom (compOpenIncl V≤U) φ = funExt λ x → Σ≡Prop (λ _ → squash/ _ _) refl

    compOpenInclId : ∀ {U : CompactOpen X} → compOpenIncl (is-refl U) ≡ idTrans ⟦ U ⟧ᶜᵒ
    compOpenInclId = makeNatTransPath (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))

    compOpenInclSeq : ∀ {U V W : CompactOpen X} (U≤V : U ≤ V) (V≤W : V ≤ W)
                    → compOpenIncl (is-trans _ _ _ U≤V V≤W)
                    ≡ compOpenIncl U≤V ●ᵛ compOpenIncl V≤W
    compOpenInclSeq _ _ = makeNatTransPath
                            (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))

    strDLSh : Functor COᵒᵖ (CommRingsCategory {ℓ = ℓ-suc ℓ})
    F-ob strDLSh  U = 𝓞 .F-ob ⟦ U ⟧ᶜᵒ
    F-hom strDLSh U≥V = 𝓞 .F-hom (compOpenIncl U≥V)
    F-id strDLSh = cong (𝓞 .F-hom) compOpenInclId ∙ 𝓞 .F-id
    F-seq strDLSh _ _ = cong (𝓞 .F-hom) (compOpenInclSeq _ _) ∙ 𝓞 .F-seq _ _

  -- the canonical one element affine cover of a representable
  module _ (A : CommRing ℓ) where
    open AffineCover
    private instance _ = (CompOpenDistLattice ⟅ Sp ⟅ A ⟆ ⟆) .snd

    singlAffineCover : AffineCover (Sp .F-ob A)
    n singlAffineCover = 1
    U singlAffineCover zero = 1l
    covers singlAffineCover = ∨lRid _
    isAffineU singlAffineCover zero = ∣ A , compOpenTopNatIso (Sp ⟅ A ⟆) ∣₁


  -- qcqs-schemes as Zariski sheaves (local ℤ-functors) with an affine cover in the sense above
  isLocal : ℤFunctor → Type (ℓ-suc ℓ)
  isLocal X = isSheaf zariskiCoverage X

  isQcQsScheme : ℤFunctor → Type (ℓ-suc ℓ)
  isQcQsScheme X = isLocal X × hasAffineCover X

  -- affine schemes are qcqs-schemes
  isQcQsSchemeAffine : ∀ (A : CommRing ℓ) → isQcQsScheme (Sp .F-ob A)
  fst (isQcQsSchemeAffine A) = isSubcanonicalZariskiCoverage A
  snd (isQcQsSchemeAffine A) = ∣ singlAffineCover A ∣₁

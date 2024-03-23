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
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty
open import Cubical.Algebra.ZariskiLattice.Properties

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Site.Cover
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

  -- TODO: 𝔸¹ ≅ Sp ℤ[x] and 𝔾ₘ ≅ Sp ℤ[x,x⁻¹] ≅ D(x) ↪ 𝔸¹ as first examples of affine schemes


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

  -- the Zariski lattice functor classifying compact open subobjects
  ZarLatFun : ℤFunctor {ℓ = ℓ}
  F-ob ZarLatFun A = ZL A , SQ.squash/
  F-hom ZarLatFun φ = inducedZarLatHom φ .fst
  F-id ZarLatFun {A} = cong fst (inducedZarLatHomId A)
  F-seq ZarLatFun φ ψ = cong fst (inducedZarLatHomSeq φ ψ)

  -- this is a separated presheaf
  -- (TODO: prove this a sheaf)
  isSeparatedZarLatFun : isSeparated zariskiCoverage ZarLatFun
  isSeparatedZarLatFun A (unimodvec n f 1∈⟨f₁,⋯,fₙ⟩) u w uRest≡wRest =
    u                         ≡⟨ sym (∧lLid _) ⟩
    1l ∧l u                  ≡⟨ congL _∧l_ D1≡⋁Dfᵢ ⟩
    (⋁ (D A ∘ f)) ∧l u       ≡⟨ ⋁Meetldist _ _ ⟩
    ⋁ (λ i → D A (f i) ∧l u) ≡⟨ ⋁Ext Dfᵢ∧u≡Dfᵢ∧w ⟩
    ⋁ (λ i → D A (f i) ∧l w) ≡⟨ sym (⋁Meetldist _ _) ⟩
    (⋁ (D A ∘ f)) ∧l w       ≡⟨ congL _∧l_ (sym D1≡⋁Dfᵢ) ⟩
    1l ∧l w                  ≡⟨ ∧lLid _ ⟩
    w ∎
    where
    open Join (ZariskiLattice A)
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (ZariskiLattice A)))
         using (IndPoset)
    open LatticeTheory (DistLattice→Lattice (ZariskiLattice A))
    open PosetStr (IndPoset .snd)
    open IsSupport (isSupportD A)
    open RadicalIdeal A
    instance
      _ = A .snd
      _ = ZariskiLattice A .snd

    D1≡⋁Dfᵢ : 1l ≡ ⋁ (D A ∘ f)
    D1≡⋁Dfᵢ = is-antisym _ _
                (supportRadicalIneq f 1r (∈→∈√ _ _ 1∈⟨f₁,⋯,fₙ⟩))
                  (1lRightAnnihilates∨l _)

    Dfᵢ∧u≡Dfᵢ∧w : ∀ i → D A (f i) ∧l u ≡ D A (f i) ∧l w
    Dfᵢ∧u≡Dfᵢ∧w i =
        D A (f i) ∧l u
      ≡⟨ sym (cong fst (funExt⁻ (cong fst toLocToDown≡ToDown) u)) ⟩
        locToDownHom .fst (inducedZarLatHom /1AsCommRingHom .fst u) .fst
      ≡⟨ cong (λ x → locToDownHom .fst x .fst) (uRest≡wRest i) ⟩
        locToDownHom .fst (inducedZarLatHom /1AsCommRingHom .fst w) .fst
      ≡⟨ cong fst (funExt⁻ (cong fst toLocToDown≡ToDown) w) ⟩
        D A (f i) ∧l w ∎
      where
      open InvertingElementsBase.UniversalProp A (f i)
      open LocDownSetIso A (f i)

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
    open isIsoC
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    compOpenTopNatIso : NatIso X ⟦ 1l ⟧ᶜᵒ
    N-ob (trans compOpenTopNatIso) _ φ = φ , refl
    N-hom (trans compOpenTopNatIso) _ = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    inv (nIso compOpenTopNatIso B) = fst
    sec (nIso compOpenTopNatIso B) = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    ret (nIso compOpenTopNatIso B) = funExt λ _ → refl


  module _ (X : ℤFunctor) where
    open isIsoC
    open Join (CompOpenDistLattice .F-ob X)
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob X)))
    open PosetStr (IndPoset .snd) hiding (_≤_)
    open LatticeTheory ⦃...⦄
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    compOpenGlobalIncl : (U : CompactOpen X) → ⟦ U ⟧ᶜᵒ ⇒ X
    N-ob (compOpenGlobalIncl U) A = fst
    N-hom (compOpenGlobalIncl U) φ = refl

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

    -- this is essentially U∧_
    compOpenDownHom : (U : CompactOpen X)
                    → DistLatticeHom (CompOpenDistLattice .F-ob X)
                                     (CompOpenDistLattice .F-ob ⟦ U ⟧ᶜᵒ)
    compOpenDownHom U = CompOpenDistLattice .F-hom (compOpenGlobalIncl U)

    module _ {U V : CompactOpen X} (V≤U : V ≤ U) where
      -- We need this separate definition to avoid termination checker issues,
      -- but we don't understand why.
      private
        compOpenDownHomFun : (A : CommRing ℓ)
                           → ⟦ V ⟧ᶜᵒ .F-ob A .fst
                           → ⟦ compOpenDownHom U .fst V ⟧ᶜᵒ .F-ob A .fst
        compOpenDownHomFun A v = (compOpenIncl V≤U ⟦ A ⟧) v , snd v

      compOpenDownHomNatIso : NatIso ⟦ V ⟧ᶜᵒ ⟦ compOpenDownHom U .fst V ⟧ᶜᵒ
      N-ob (trans compOpenDownHomNatIso) = compOpenDownHomFun
      N-hom (trans compOpenDownHomNatIso) _ =
        funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (Σ≡Prop (λ _ → squash/ _ _) refl)
      inv (nIso compOpenDownHomNatIso A) ((x , Ux≡D1) , Vx≡D1) = x , Vx≡D1
      sec (nIso compOpenDownHomNatIso A) =
        funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (Σ≡Prop (λ _ → squash/ _ _) refl)
      ret (nIso compOpenDownHomNatIso A) = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl

    compOpenInclId : ∀ {U : CompactOpen X} → compOpenIncl (is-refl U) ≡ idTrans ⟦ U ⟧ᶜᵒ
    compOpenInclId = makeNatTransPath (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))

    compOpenInclSeq : ∀ {U V W : CompactOpen X} (U≤V : U ≤ V) (V≤W : V ≤ W)
                    → compOpenIncl (is-trans _ _ _ U≤V V≤W)
                    ≡ compOpenIncl U≤V ●ᵛ compOpenIncl V≤W
    compOpenInclSeq _ _ = makeNatTransPath
                            (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))


    -- the structure sheaf
    private COᵒᵖ = (DistLatticeCategory (CompOpenDistLattice .F-ob X)) ^op

    strDLSh : Functor COᵒᵖ (CommRingsCategory {ℓ = ℓ-suc ℓ})
    F-ob strDLSh  U = 𝓞 .F-ob ⟦ U ⟧ᶜᵒ
    F-hom strDLSh U≥V = 𝓞 .F-hom (compOpenIncl U≥V)
    F-id strDLSh = cong (𝓞 .F-hom) compOpenInclId ∙ 𝓞 .F-id
    F-seq strDLSh _ _ = cong (𝓞 .F-hom) (compOpenInclSeq _ _) ∙ 𝓞 .F-seq _ _


  -- def. affine cover and locality for definition of qcqs-scheme
  module _ (X : ℤFunctor) where
    open isIsoC
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

  -- qcqs-schemes as Zariski sheaves (local ℤ-functors) with an affine cover in the sense above
  isLocal : ℤFunctor → Type (ℓ-suc ℓ)
  isLocal X = isSheaf zariskiCoverage X

  -- Compact opens of Zariski sheaves are sheaves
  presLocalCompactOpen : (X : ℤFunctor) (U : CompactOpen X) → isLocal X → isLocal ⟦ U ⟧ᶜᵒ
  presLocalCompactOpen X U isLocalX R um@(unimodvec _ f _) = isoToIsEquiv isoU
    where
    open Coverage zariskiCoverage
    open InvertingElementsBase R
    instance _ = R .snd

    fᵢCoverR = covers R .snd um

    isoX : Iso (X .F-ob R .fst) (CompatibleFamily X fᵢCoverR)
    isoX = equivToIso (elementToCompatibleFamily _ _ , isLocalX R um)

    compatibleFamIncl : (CompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR) → (CompatibleFamily X fᵢCoverR)
    compatibleFamIncl fam = (fst ∘ fst fam)
                          , λ i j B φ ψ φψComm → cong fst (fam .snd i j B φ ψ φψComm)

    compatibleFamIncl≡ : ∀ (y : Σ[ x ∈ X .F-ob R .fst  ] U .N-ob R x ≡ D R 1r)
                       → compatibleFamIncl (elementToCompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR y)
                       ≡ elementToCompatibleFamily X fᵢCoverR (y .fst)
    compatibleFamIncl≡ y = CompatibleFamily≡ _ _ _ _ λ _ → refl

    isoU : Iso (Σ[ x ∈ X .F-ob R .fst  ] U .N-ob R x ≡ D R 1r)
               (CompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR)
    fun isoU = elementToCompatibleFamily _ _
    fst (inv isoU fam) = isoX .inv (compatibleFamIncl fam)
    snd (inv isoU fam) = -- U (x) ≡ D(1)
                         -- knowing that U(x/1)¸≡ D(1) in R[1/fᵢ]
      let x = isoX .inv (compatibleFamIncl fam) in
      isSeparatedZarLatFun R um (U .N-ob R x) (D R 1r)
        λ i → let open UniversalProp (f i)
                  instance _ = R[1/ (f i) ]AsCommRing .snd in

                inducedZarLatHom /1AsCommRingHom .fst (U .N-ob R x)

              ≡⟨ funExt⁻ (sym (U .N-hom /1AsCommRingHom)) x ⟩

                U .N-ob R[1/ (f i) ]AsCommRing (X .F-hom /1AsCommRingHom x)

              ≡⟨ cong (U .N-ob R[1/ f i ]AsCommRing)
                      (funExt⁻ (cong fst (isoX .rightInv (compatibleFamIncl fam))) i) ⟩

                U .N-ob R[1/ (f i) ]AsCommRing (fam .fst i .fst)

              ≡⟨ fam .fst i .snd ⟩

                D R[1/ (f i) ]AsCommRing 1r

              ≡⟨ sym (inducedZarLatHom /1AsCommRingHom .snd .pres1) ⟩

                inducedZarLatHom /1AsCommRingHom .fst (D R 1r) ∎

    rightInv isoU fam =
      Σ≡Prop (λ _ → isPropIsCompatibleFamily _ _ _)
        (funExt λ i → Σ≡Prop (λ _ → squash/ _ _)
                        (funExt⁻ (cong fst
                          (isoX .rightInv (compatibleFamIncl fam))) i))
    leftInv isoU y = Σ≡Prop (λ _ → squash/ _ _)
                            (cong (isoX .inv) (compatibleFamIncl≡ y)
                              ∙ isoX .leftInv (y .fst))


  -- definition of quasi-compact, quasi-separated schemes
  isQcQsScheme : ℤFunctor → Type (ℓ-suc ℓ)
  isQcQsScheme X = isLocal X × hasAffineCover X


  -- affine schemes are qcqs-schemes
  module _ (A : CommRing ℓ) where
    open AffineCover
    private instance _ = (CompOpenDistLattice ⟅ Sp ⟅ A ⟆ ⟆) .snd

    -- the canonical one element affine cover of a representable
    singlAffineCover : AffineCover (Sp .F-ob A)
    n singlAffineCover = 1
    U singlAffineCover zero = 1l
    covers singlAffineCover = ∨lRid _
    isAffineU singlAffineCover zero = ∣ A , compOpenTopNatIso (Sp ⟅ A ⟆) ∣₁

    isQcQsSchemeAffine : isQcQsScheme (Sp .F-ob A)
    fst isQcQsSchemeAffine = isSubcanonicalZariskiCoverage A
    snd isQcQsSchemeAffine = ∣ singlAffineCover ∣₁


-- standard affine opens
-- TODO: separate file?
module StandardOpens {ℓ : Level} (R : CommRing ℓ) (f : R .fst) where

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open isIsoC
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open IsRingHom
  open RingHoms
  open IsLatticeHom
  open ZarLat

  open InvertingElementsBase R
  open UniversalProp f

  private module ZL = ZarLatUniversalProp

  private
    instance
      _ = R .snd

  D : CompactOpen (Sp ⟅ R ⟆)
  D = yonedaᴾ ZarLatFun R .inv (ZL.D R f)

  SpR[1/f]≅⟦Df⟧ : NatIso (Sp .F-ob R[1/ f ]AsCommRing) ⟦ D ⟧ᶜᵒ
  N-ob (trans SpR[1/f]≅⟦Df⟧) B φ = (φ ∘r /1AsCommRingHom) , ∨lRid _ ∙ path
    where
    open CommRingHomTheory φ
    open IsSupport (ZL.isSupportD B)
    instance
      _ = B .snd
      _ = ZariskiLattice B .snd

    isUnitφ[f/1] : φ .fst (f /1) ∈ B ˣ
    isUnitφ[f/1] = RingHomRespInv (f /1) ⦃ S/1⊆S⁻¹Rˣ f ∣ 1 , sym (·IdR f) ∣₁ ⦄

    path : ZL.D B (φ .fst (f /1)) ≡ 1l
    path = supportUnit _ isUnitφ[f/1]

  N-hom (trans SpR[1/f]≅⟦Df⟧) _ = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (RingHom≡ refl)

  inv (nIso SpR[1/f]≅⟦Df⟧ B) (φ , Dφf≡D1) = invElemUniversalProp B φ isUnitφf .fst .fst
    where
    instance _ = ZariskiLattice B .snd
    isUnitφf : φ .fst f ∈ B ˣ
    isUnitφf = unitLemmaZarLat B (φ $r f) (sym (∨lRid _) ∙ Dφf≡D1)

  sec (nIso SpR[1/f]≅⟦Df⟧ B) =
    funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (RingHom≡ (invElemUniversalProp _ _ _ .fst .snd))
  ret (nIso SpR[1/f]≅⟦Df⟧ B) =
    funExt λ φ → cong fst (invElemUniversalProp B (φ ∘r /1AsCommRingHom) _ .snd (φ , refl))

  isAffineD : isAffineCompactOpen D
  isAffineD = ∣ R[1/ f ]AsCommRing , SpR[1/f]≅⟦Df⟧ ∣₁


-- compact opens of affine schemes are qcqs-schemes
module _ {ℓ : Level} (R : CommRing ℓ) (W : CompactOpen (Sp ⟅ R ⟆)) where

  open StandardOpens

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open isIsoC
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open PosetStr ⦃...⦄
  open IsRingHom
  open RingHoms
  open IsLatticeHom
  open ZarLat

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob (Sp .F-ob R)))) using (IndPoset; ind≤bigOp)
  open InvertingElementsBase R
  open Join
  open JoinMap
  open AffineCover
  private module ZL = ZarLatUniversalProp

  private
    instance
      _ = R .snd
      _ = ZariskiLattice R .snd
      _ = CompOpenDistLattice .F-ob (Sp .F-ob R) .snd
      _ = CompOpenDistLattice .F-ob ⟦ W ⟧ᶜᵒ .snd
      _ = IndPoset .snd

    w : ZL R
    w = yonedaᴾ ZarLatFun R .fun W

    -- yoneda is a lattice homomorphsim
    isHomYoneda : IsLatticeHom (DistLattice→Lattice (ZariskiLattice R) .snd)
                               (yonedaᴾ ZarLatFun R .inv)
                               (DistLattice→Lattice (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) .snd)
    pres0 isHomYoneda = makeNatTransPath (funExt₂ (λ _ _ → refl))
    pres1 isHomYoneda =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres1))
    pres∨l isHomYoneda u v =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres∨l u v))
    pres∧l isHomYoneda u v =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres∧l u v))

    module _ {n : ℕ}
             (f : FinVec (fst R) n)
             (⋁Df≡W : ⋁ (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) (D R ∘ f) ≡ W) where

      Df≤W : ∀ i → D R (f i) ≤ W
      Df≤W i = subst (D R (f i) ≤_) ⋁Df≡W (ind≤bigOp (D R ∘ f) i)

      toAffineCover : AffineCover ⟦ W ⟧ᶜᵒ
      AffineCover.n toAffineCover = n
      U toAffineCover i = compOpenDownHom (Sp ⟅ R ⟆) W .fst (D R (f i))
      covers toAffineCover = sym (pres⋁ (compOpenDownHom (Sp ⟅ R ⟆) W) (D R ∘ f))
                           ∙ cong (compOpenDownHom (Sp ⟅ R ⟆) W .fst) ⋁Df≡W
                           ∙ makeNatTransPath (funExt₂ (λ _ → snd))
      isAffineU toAffineCover i =
        ∣ _ , seqNatIso (SpR[1/f]≅⟦Df⟧ R (f i)) (compOpenDownHomNatIso _ (Df≤W i)) ∣₁

  module _ {n : ℕ}
           (f : FinVec (fst R) n)
           (⋁Df≡w : ⋁ (ZariskiLattice R) (ZL.D R ∘ f) ≡ w) where

    private
      ⋁Df≡W : ⋁ (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) (D R ∘ f) ≡ W
      ⋁Df≡W = sym (pres⋁ (_ , isHomYoneda) (ZL.D R ∘ f))
            ∙ cong (yonedaᴾ ZarLatFun R .inv) ⋁Df≡w
            ∙ yonedaᴾ ZarLatFun R .leftInv W

    makeAffineCoverCompOpenOfAffine : AffineCover ⟦ W ⟧ᶜᵒ
    makeAffineCoverCompOpenOfAffine = toAffineCover f ⋁Df≡W

  hasAffineCoverCompOpenOfAffine : hasAffineCover ⟦ W ⟧ᶜᵒ
  hasAffineCoverCompOpenOfAffine = PT.map truncHelper ([]surjective w)
    where
    truncHelper : Σ[ n,f ∈ Σ ℕ (FinVec (fst R)) ] [ n,f ] ≡ w → AffineCover ⟦ W ⟧ᶜᵒ
    truncHelper ((n , f) , [n,f]≡w) = makeAffineCoverCompOpenOfAffine f (ZL.⋁D≡ R f ∙ [n,f]≡w)

  isQcQsSchemeCompOpenOfAffine : isQcQsScheme ⟦ W ⟧ᶜᵒ
  fst isQcQsSchemeCompOpenOfAffine = presLocalCompactOpen _ _ (isSubcanonicalZariskiCoverage R)
  snd isQcQsSchemeCompOpenOfAffine = hasAffineCoverCompOpenOfAffine


{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Site.Instances.ZariskiCommRing where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Yoneda

open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' ℓ'' : Level

open Coverage
open SliceOb

-- the type of unimodular vectors, i.e. generators of the 1-ideal
record UniModVec (R : CommRing ℓ) : Type ℓ where
  constructor
    unimodvec

  open CommRingStr (str R)
  open CommIdeal R using (_∈_)

  field
    n : ℕ
    f : FinVec ⟨ R ⟩ n
    isUniMod : 1r ∈ ⟨ f ⟩[ R ]

module _ {A : CommRing ℓ} {B : CommRing ℓ'} (φ : CommRingHom A B) where
  open UniModVec
  open IsRingHom ⦃...⦄
  open CommRingStr ⦃...⦄
  open Sum (CommRing→Ring B)
  open SumMap _ _ φ
  private
    module A = CommIdeal A
    module B = CommIdeal B

    instance
      _ = A .snd
      _ = B .snd
      _ = φ .snd

  pullbackUniModVec : UniModVec A → UniModVec B
  n (pullbackUniModVec um) = um .n
  f (pullbackUniModVec um) i = φ $r um .f i
  isUniMod (pullbackUniModVec um) = B.subst-∈ -- 1 ∈ ⟨ f₁ ,..., fₙ ⟩ → 1 ∈ ⟨ φ(f₁) ,..., φ(fₙ) ⟩
                                      ⟨ φ .fst ∘ um .f ⟩[ B ]
                                        pres1 (PT.map mapHelper (um .isUniMod))
    where
    mapHelper : Σ[ α ∈ FinVec ⟨ A ⟩ _ ] 1r ≡ linearCombination A α (um .f)
              → Σ[ β ∈ FinVec ⟨ B ⟩ _ ] φ $r 1r ≡ linearCombination B β (φ .fst ∘ um .f)
    fst (mapHelper (α , 1≡∑αf)) = φ .fst ∘ α
    snd (mapHelper (α , 1≡∑αf)) =
      subst (λ x → φ $r x ≡ linearCombination B (φ .fst ∘ α) (φ .fst ∘ um .f))
            (sym 1≡∑αf)
            (∑Map _ ∙ ∑Ext (λ _ → pres· _ _))


{-

  For 1 ∈ ⟨ f₁ ,..., fₙ ⟩ we get a cover by arrows _/1 : R → R[1/fᵢ] for i=1,...,n
  Pullback along φ : A → B is given by the induced arrows A[1/fᵢ] → B[1/φ(fᵢ)]

-}
zariskiCoverage : Coverage (CommRingsCategory {ℓ = ℓ} ^op) ℓ ℓ-zero
fst (covers zariskiCoverage R) = UniModVec R
fst (snd (covers zariskiCoverage R) um) = Fin n --patches
  where
  open UniModVec um
S-ob (snd (snd (covers zariskiCoverage R) um) i) = R[1/ f i ]AsCommRing
  where
  open UniModVec um
  open InvertingElementsBase R
S-arr (snd (snd (covers zariskiCoverage R) um) i) = /1AsCommRingHom
  where
  open UniModVec um
  open InvertingElementsBase.UniversalProp R (f i)
pullbackStability zariskiCoverage {c = A} um {d = B} φ =
  ∣ pullbackUniModVec φ um , (λ i → ∣ i , ψ i , RingHom≡ (sym (ψComm i)) ∣₁) ∣₁
  where
  open UniModVec
  module A = InvertingElementsBase A
  module B = InvertingElementsBase B
  module AU = A.UniversalProp
  module BU = B.UniversalProp

  ψ : (i : Fin (um .n)) → CommRingHom A.R[1/ um .f i ]AsCommRing B.R[1/ φ $r um .f i ]AsCommRing
  ψ i = uniqInvElemHom φ (um .f i) .fst .fst

  ψComm : ∀ i → (ψ i .fst) ∘ (AU._/1 (um .f i)) ≡ (BU._/1 (φ $r um .f i)) ∘ φ .fst
  ψComm i = uniqInvElemHom φ (um .f i) .fst .snd

{-

   This defines a subcanonical coverage.
   The lemmas needed in the subcanonicity proof are analogous to
   proving the sheaf property of the structure sheaf.

   See the proof of "isLimConeLocCone" in Cubical.Algebra.CommRing.Localisation.Limit

   Ultimately, what happens is that we use the "equalizerLemma" of
   Cubical.Algebra.CommRing.Localisation.Limit
   to construct the required functions induced by a limit in Sets.
   Then, we implicitly use the fact that the forgetful functor
   CommRing → Set reflects limits to show that these functions have to be ring homs.

-}
module SubcanonicalLemmas (A R : CommRing ℓ) where
  open CommRingStr ⦃...⦄
  open CommIdeal R using (_∈_)

  private instance
   _ = A .snd
   _ = R .snd

  module _
    {n : ℕ}
    (f : FinVec ⟨ R ⟩ n)
    (isUniModF : 1r ∈ ⟨ f ⟩[ R ])
    (fam@(φ , isCompatibleφ) : CompatibleFamily (yo A)
                                                (str (covers zariskiCoverage R)
                                                (unimodvec n f isUniModF)))
    where
    open InvertingElementsBase R
    open RingHoms
    module U i = UniversalProp (f i)
    module UP i j = UniversalProp (f i · f j)

    private
      _/1ⁱ : ⟨ R ⟩ → {i : Fin n} →  R[1/ (f i) ]
      (r /1ⁱ) {i = i} = U._/1 i r


    applyEqualizerLemma : ∀ a → ∃![ r ∈ ⟨ R ⟩ ] ∀ i → r /1ⁱ ≡ φ i .fst a
    applyEqualizerLemma a = equalizerLemma R f isUniModF (λ i → φ i .fst a) path
      where
      pathHelper : ∀ i j → χˡ R f i j ∘r (U./1AsCommRingHom i)
                         ≡ χʳ R f i j ∘r (U./1AsCommRingHom j)
      pathHelper i j = RingHom≡
                         (χˡUnique R f i j .fst .snd ∙ sym (χʳUnique R f i j .fst .snd))

      path : ∀ i j → χˡ R f i j .fst (φ i $r a) ≡ χʳ R f i j .fst (φ j $r a)
      path i j = funExt⁻ (cong fst (isCompatibleφ i j _ _ _ (pathHelper i j))) a

    inducedHom : CommRingHom A R
    fst inducedHom a = applyEqualizerLemma a .fst .fst
    snd inducedHom = makeIsRingHom
                       (cong fst (applyEqualizerLemma 1r .snd (1r , 1Coh)))
                       (λ x y → cong fst (applyEqualizerLemma (x + y) .snd (_ , +Coh x y)))
                       (λ x y → cong fst (applyEqualizerLemma (x · y) .snd (_ , ·Coh x y)))
      where
      open IsRingHom
      1Coh : ∀ i → (1r /1ⁱ ≡ φ i .fst 1r)
      1Coh i = sym (φ i .snd .pres1)

      +Coh : ∀ x y i → ((fst inducedHom x + fst inducedHom y) /1ⁱ ≡ φ i .fst (x + y))
      +Coh x y i = let instance _ = snd R[1/ f i ]AsCommRing in
           U./1AsCommRingHom i .snd .pres+ _ _
        ∙∙ cong₂ _+_ (applyEqualizerLemma x .fst .snd i) (applyEqualizerLemma y .fst .snd i)
        ∙∙ sym (φ i .snd .pres+ x y)

      ·Coh : ∀ x y i → ((fst inducedHom x · fst inducedHom y) /1ⁱ ≡ φ i .fst (x · y))
      ·Coh x y i = let instance _ = snd R[1/ f i ]AsCommRing in
           U./1AsCommRingHom i .snd .pres· _ _
        ∙∙ cong₂ _·_ (applyEqualizerLemma x .fst .snd i) (applyEqualizerLemma y .fst .snd i)
        ∙∙ sym (φ i .snd .pres· x y)

    inducedHomUnique : ∀ (ψ : CommRingHom A R)
                     → (∀ a i →  (ψ $r a) /1ⁱ ≡ φ i $r a)
                     → inducedHom ≡ ψ
    inducedHomUnique ψ ψ/1≡φ =
      RingHom≡
        (funExt
          (λ a → cong fst (applyEqualizerLemma a .snd (ψ $r a , ψ/1≡φ a))))


isSubcanonicalZariskiCoverage : isSubcanonical (zariskiCoverage {ℓ = ℓ})
isSubcanonicalZariskiCoverage A R (unimodvec n f isUniModF) = isoToIsEquiv theIso
  where
  open Iso
  open SubcanonicalLemmas A R
  um = (unimodvec n f isUniModF)

  theIso : Iso (CommRingHom A R)
               (CompatibleFamily (yo A) (str (covers zariskiCoverage R) um))
  fun theIso = elementToCompatibleFamily _ _
  inv theIso fam = inducedHom f isUniModF fam
  rightInv theIso fam = CompatibleFamily≡ _ _ _ _
                          λ i → RingHom≡ (funExt
                            λ a → applyEqualizerLemma f isUniModF fam a .fst .snd i)
  leftInv theIso φ = inducedHomUnique _ _ _ _ λ _ _ → refl

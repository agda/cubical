
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Site.Instances.ZariskiCommRing where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
open import Cubical.Categories.Constructions.Slice

open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' ℓ'' : Level

open Coverage
open SliceOb

-- the type of unimodular vectors, i.e. generators of the 1-ideal
record UniModVec (R : CommRing ℓ) : Type ℓ where
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

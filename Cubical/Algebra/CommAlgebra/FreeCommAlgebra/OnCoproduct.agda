{-# OPTIONS --safe #-}
{-
 The goal of this module is to show that for two types I,J, there is an
 isomorphism of algebras

    R[I][J] ≃ R[ I ⊎ J ]

  where '⊎' is the disjoint sum.
-}
module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.OnCoproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Structure

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra

private variable
    ℓ ℓ' : Level

module CalculateFreeCommAlgebraOnCoproduct (R : CommRing ℓ) (I J : Type ℓ) where
  open Construction using (var; const)
  open CommAlgebraStr ⦃...⦄

  {-
     We start by defining R[I][J] and R[I⊎J] as R[I] algebras,
     which we need later to use universal properties
  -}
  R[I][J]overR[I] : CommAlgebra (CommAlgebra→CommRing (R [ I ])) ℓ
  R[I][J]overR[I] = (CommAlgebra→CommRing (R [ I ])) [ J ]

  R[I][J] : CommAlgebra R ℓ
  R[I][J] = baseChange baseRingHom R[I][J]overR[I]

  ψOverR : CommAlgebraHom (R [ I ]) (R [ I ⊎ J ])
  ψOverR = inducedHom (R [ I ⊎ J ]) (λ i → var (inl i))

  ψ : CommRingHom (CommAlgebra→CommRing (R [ I ])) (CommAlgebra→CommRing (R [ I ⊎ J ]))
  ψ = CommAlgebraHom→CommRingHom (R [ I ]) (R [ I ⊎ J ]) ψOverR

  R[I⊎J]overR[I] : CommAlgebra (CommAlgebra→CommRing (R [ I ])) ℓ
  R[I⊎J]overR[I] = Iso.inv (CommAlgChar.CommAlgIso (CommAlgebra→CommRing (R [ I ])))
                   (CommAlgebra→CommRing (R [ I ⊎ J ]) ,
                    ψ)

  {-
    Now we use universal properties to construct maps in both directions.
  -}
  open RingHoms
  open RingStr ⦃...⦄ using (1r)
  instance _ = snd (R [ I ])
           _ = snd R[I⊎J]overR[I]
           _ = snd (CommRing→Ring R)
  module R[I] = CommAlgebraStr (snd (R [ I ]))
  module R[I⊎J]overR[I] = CommAlgebraStr (snd R[I⊎J]overR[I])
  module R[I⊎J] = CommAlgebraStr (snd (R [ I ⊎ J ]))

  to : CommAlgebraHom (R [ I ⊎ J ]) R[I][J]
  to = inducedHom R[I][J]
                  (⊎.rec (λ i → const (var i))
                         λ j → var j)

  isoR = CommAlgChar.CommAlgIso R
  isoR[I] = CommAlgChar.CommAlgIso (CommAlgebra→CommRing (R [ I ]))
  asHomOverR[I] = Iso.fun isoR[I] R[I⊎J]overR[I]
  asHomOverR = Iso.fun isoR (R [ I ⊎ J ])

  ≡RingHoms : snd asHomOverR[I] ∘r baseRingHom ≡ baseRingHom
  ≡RingHoms =
    RingHom≡
      (funExt λ x →
        fst (snd asHomOverR[I] ∘r baseRingHom) x ≡⟨⟩
        fst (snd asHomOverR[I]) (const x · 1a)   ≡⟨⟩
        (const x · 1a) ⋆ 1a                      ≡⟨ cong (_⋆ 1a) (·IdR (const x)) ⟩
        const x ⋆ 1a                             ≡⟨⟩
        (fst ψ (const x)) · 1a                   ≡⟨⟩
        (const x · const 1r) · 1a                ≡⟨ cong (_· 1a) (·IdR (const x)) ⟩
        const x · 1a ∎)

  ≡R[I⊎J] =
    baseChange baseRingHom R[I⊎J]overR[I]                                                     ≡⟨⟩
    Iso.inv isoR ((CommAlgebra→CommRing R[I⊎J]overR[I]) , (snd asHomOverR[I]) ∘r baseRingHom) ≡⟨ step1 ⟩
    Iso.inv isoR (CommAlgebra→CommRing (R [ I ⊎ J ]) , baseRingHom)                           ≡⟨⟩
    Iso.inv isoR asHomOverR                                                                   ≡⟨ step2 ⟩
    R [ I ⊎ J ] ∎
    where
      step1 : Iso.inv isoR ((CommAlgebra→CommRing R[I⊎J]overR[I]) , (snd asHomOverR[I]) ∘r baseRingHom)
              ≡ Iso.inv isoR (CommAlgebra→CommRing (R [ I ⊎ J ]) , baseRingHom)
      step1 i = Iso.inv isoR ((CommAlgebra→CommRing R[I⊎J]overR[I]) , ≡RingHoms i)

      step2 = Iso.leftInv isoR (R [ I ⊎ J ])

  fst≡R[I⊎J] : cong fst ≡R[I⊎J] ≡ refl
  fst≡R[I⊎J] =
    cong fst ≡R[I⊎J]    ≡⟨⟩
    refl ∙ (refl ∙ refl) ≡⟨ sym (lUnit _) ⟩
    refl ∙ refl          ≡⟨ sym (lUnit _) ⟩
    refl ∎

  fromOverR[I] : CommAlgebraHom R[I][J]overR[I] R[I⊎J]overR[I]
  fromOverR[I] = inducedHom R[I⊎J]overR[I] (λ j → var (inr j))

  from' : CommAlgebraHom R[I][J] (baseChange baseRingHom R[I⊎J]overR[I])
  from' = baseChangeHom {S = R}
                        baseRingHom
                        R[I][J]overR[I]
                        R[I⊎J]overR[I]
                        fromOverR[I]

  from : CommAlgebraHom R[I][J] (R [ I ⊎ J ])
  from = subst (CommAlgebraHom R[I][J]) ≡R[I⊎J] from'


  {-
    Calculate, that the maps 'to' and 'from' preserve the variables/generators
    This is needed to use universal properties, to show that to and from are
    inverse to each other.
  -}

  incVar : (x : I ⊎ J) → ⟨ R[I][J] ⟩
  incVar (inl i) = const (var i)
  incVar (inr j) = var j

  toOnGenerators : (x : I ⊎ J) → fst to (var x) ≡ incVar x
  toOnGenerators (inl i) = refl
  toOnGenerators (inr j) = refl

  fromOnGenerators : (x : I ⊎ J) → fst from (incVar x) ≡ (var x)
  fromOnGenerators (inl i) =
    fst from (const (var i))                                                      ≡⟨⟩
    (subst (λ X → ⟨ R[I][J] ⟩ → X) (cong fst ≡R[I⊎J]) (fst from')) (const (var i)) ≡⟨ step1 ⟩
    (subst (λ X → ⟨ R[I][J] ⟩ → X) refl (fst from')) (const (var i))               ≡⟨ step2 ⟩
    (fst from') (const (var i))                                                   ≡⟨⟩
    var (inl i) · 1a                                                              ≡⟨ ·IdR _ ⟩
    var (inl i) ∎
      where step1 : _ ≡ _
            step1 = cong (λ u → subst (λ X → ⟨ R[I][J] ⟩ → X) u (fst from') (const (var i))) fst≡R[I⊎J]
            step2 : _ ≡ _
            step2 = cong (λ u → u (const (var i)))
                         (substRefl {B = λ (X : Type ℓ) → ⟨ R[I][J] ⟩ → X} (fst from'))
  fromOnGenerators (inr j) =
    fst from (var j)                                                      ≡⟨⟩
    (subst (λ X → ⟨ R[I][J] ⟩ → X) (cong fst ≡R[I⊎J]) (fst from')) (var j) ≡⟨ step1 ⟩
    (subst (λ X → ⟨ R[I][J] ⟩ → X) refl (fst from')) (var j)               ≡⟨ step2 ⟩
    (fst from') (var j)                                                   ≡⟨⟩
    (var (inr j)) ∎
      where step1 = cong (λ u → subst (λ X → ⟨ R[I][J] ⟩ → X) u (fst from') (var j)) fst≡R[I⊎J]
            step2 = cong (λ u → u (var j))
                         (substRefl {B = λ (X : Type ℓ) → ⟨ R[I][J] ⟩ → X} (fst from'))

  open AlgebraHoms
  fromTo : (x : ⟨ R [ I ⊎ J ] ⟩) → fst (from ∘a to) x ≡ x
  fromTo = isIdByUMP (from ∘a to)
                     λ x → fst (from ∘a to) (var x) ≡⟨ cong (λ u → fst from u) (toOnGenerators x) ⟩
                           fst from (incVar x)      ≡⟨ fromOnGenerators x ⟩
                           var x ∎

  {-
    For 'to ∘a from', we need 'to' and 'from' as homomorphisms of R[I]-algebras.
  -}

  module _ where
    open IsAlgebraHom
    private
      z = to .snd
      instance _ = snd R[I][J]overR[I]
               -- _ = snd R[I][J]
               _ = snd R

    toOverR[I] : CommAlgebraHom R[I⊎J]overR[I] R[I][J]overR[I]
    toOverR[I] .fst = to .fst
    (toOverR[I] .snd) .pres0 = z .pres0
    (toOverR[I] .snd) .pres1 = z .pres1
    (toOverR[I] .snd) .pres+ = z .pres+
    (toOverR[I] .snd) .pres· = z .pres·
    (toOverR[I] .snd) .pres- = z .pres-
    (toOverR[I] .snd) .pres⋆ r x =
      fst to (r ⋆ x)              ≡⟨⟩
      fst to (fst ψ r · x)        ≡⟨ z .pres· (fst ψ r) x ⟩
      fst to (fst ψ r) · fst to x ≡⟨ cong (_· fst to x) (to∘ψ≡const r) ⟩
      const r · fst to x          ≡⟨⟩
      (r ⋆ fst to x) ∎
      where
        {-
          We use the UMP of R[I] on

          R[I] ─ψ─→ R[I⊎J] ─to─→ R[I][J]
             \                   /
              \______const______/

          To do that, we have to show that
          const is an R-algebra homomorphism
        -}
        open Construction using (+HomConst; ·HomConst)
        constHom : CommAlgebraHom (R [ I ]) R[I][J]
        constHom .fst = const
        constHom .snd =
          makeIsAlgebraHom
            refl
            +HomConst
            ·HomConst
            λ r x →
              const (const r · x)                                       ≡⟨ ·HomConst (const r) x ⟩
              const (const r) · const x                                 ≡[ i ]⟨
                                                                        const (sym (·IdR (const r)) i) · const x ⟩
              const (const r · const 1r) · const x                      ≡[ i ]⟨
                                                                        sym (·IdR (const (const r · const 1r))) i
                                                                           · const x ⟩
              (const (const r · const 1r) · const (const 1r)) · const x ≡⟨⟩
              CommAlgebraStr._⋆_ (snd R[I][J]) r (const x) ∎

        to∘ψOnVar : (i : I) → fst (to ∘a ψOverR) (var i) ≡ const (var i)
        to∘ψOnVar i = refl

        to∘ψ≡const : (x : ⟨ R [ I ] ⟩) → fst to (fst ψ x) ≡ const x
        to∘ψ≡const =
          equalByUMP R[I][J] (to ∘a ψOverR) constHom to∘ψOnVar


  toFromOverR[I] : (x : ⟨ R[I][J]overR[I] ⟩) → fst (toOverR[I] ∘a fromOverR[I]) x ≡ x
  toFromOverR[I] = isIdByUMP (toOverR[I] ∘a fromOverR[I]) λ _ → refl

{- export bundled results -}
module _ {R : CommRing ℓ} {I J : Type ℓ} where
  open CalculateFreeCommAlgebraOnCoproduct R I J

  equivFreeCommSum : CommAlgebraEquiv (R [ I ⊎ J ]) R[I][J]
  equivFreeCommSum = (biInvEquiv→Equiv-left asBiInv) , snd to
    where
      open BiInvEquiv
      asBiInv : BiInvEquiv _ _
      fun asBiInv = fst to
      invr asBiInv = fst fromOverR[I]
      invr-rightInv asBiInv = toFromOverR[I]
      invl asBiInv = fst from
      invl-leftInv asBiInv = fromTo

  equivFreeCommSumOverR[I] : CommAlgebraEquiv R[I⊎J]overR[I] R[I][J]overR[I]
  equivFreeCommSumOverR[I] = biInvEquiv→Equiv-right asBiInv , snd toOverR[I]
    where
      open BiInvEquiv
      asBiInv : BiInvEquiv _ _
      fun asBiInv = fst toOverR[I]
      invr asBiInv = fst fromOverR[I]
      invr-rightInv asBiInv = toFromOverR[I]
      invl asBiInv = fst from
      invl-leftInv asBiInv = fromTo

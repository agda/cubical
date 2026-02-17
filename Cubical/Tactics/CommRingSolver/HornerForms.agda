module Cubical.Tactics.CommRingSolver.HornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool as 𝟚

open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Tactics.CommRingSolver.Utility

open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression public



private
  variable
    ℓ ℓ' : Level

{-
  This defines the type of multivariate Polynomials over the RawRing R.
  The construction is based on the algebraic fact

    R[X₀][X₁]⋯[Xₙ] ≅ R[X₀,⋯,Xₙ]

  BUT: Contrary to algebraic convetions, we will give 'Xₙ' the lowest index
  in the definition of 'Variable' below. So if 'Variable n R k' is identified
  with 'Xₖ', then the RawRing we construct should rather be denoted with

    R[Xₙ][Xₙ₋₁]⋯[X₀]

  or, to be precise about the evaluation order:

    (⋯((R[Xₙ])[Xₙ₋₁])⋯)[X₀]

-}


module HornerForms (R@(⟨R⟩ , _) : CommRing ℓ)
                         (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R')
                         where
 open CommRingStr (snd R)
 RRng : RawRing ℓ
 RRng = rawring ⟨R⟩ 0r 1r _+_ _·_ (-_)
 open RingTheory (CommRing→Ring R)
 module R‵ where
   open CommRingStr (snd R') public
   open RingTheory (CommRing→Ring R') public

 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)

 RAlg : RawAlgebra RRng ℓ'
 RAlg = rawalgebra ⟨R'⟩ scalar‵ 0r‵ 1r‵ (_+‵_) (_·‵_) (-‵_)



 open Eval RRng RAlg public


 data IteratedHornerForms : ℕ → Type ℓ where
   const : ⟨R⟩ → IteratedHornerForms ℕ.zero
   0H : {n : ℕ} → IteratedHornerForms (ℕ.suc n)
   _·X+_ : {n : ℕ} → IteratedHornerForms (ℕ.suc n) → IteratedHornerForms n
                   → IteratedHornerForms (ℕ.suc n)


 {-
   The following function returns true, if there is some
   obvious reason that the Horner-Expression should be zero.
   Since Equality is undecidable in a general RawAlgebra, we cannot
   have a function that fully lives up to the name 'isZero'.
 -}

 isZero : {n : ℕ} → IteratedHornerForms n → Bool
 isZero (const x) = 𝟚.Dec→Bool (x ≟ 0r)
 isZero 0H = true
 isZero (P ·X+ Q) = (isZero P) 𝟚.and (isZero Q)

 leftIsZero : {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
              → isZero (P ·X+ Q) ≡ true
              → isZero P ≡ true
 leftIsZero P Q isZeroSum with isZero P
 ... | true = refl
 ... | false = isZeroSum

 rightIsZero : {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
              → isZero (P ·X+ Q) ≡ true
              → isZero Q ≡ true
 rightIsZero P Q isZeroSum with isZero Q
 ... | true = refl
 ... | false = byBoolAbsurdity (snd (extractFromAnd _ _ isZeroSum))


 module IteratedHornerOperations where


  private
    1H' : (n : ℕ) → IteratedHornerForms n
    1H' ℕ.zero = const 1r
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms n
    0H' ℕ.zero = const 0r
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
               → IteratedHornerForms n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) =
    let left = (P +ₕ Q)
        right = (r +ₕ s)
    in if ((isZero left) and (isZero right))
       then 0ₕ
       else left ·X+ right

  -ₕ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
  -ₕ (const x) = const (- x)
  -ₕ 0H = 0H
  -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

  _⋆_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms (ℕ.suc n)
                → IteratedHornerForms (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
                → IteratedHornerForms n
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ Q) =
    if (isZero r)
    then 0ₕ
    else (r ⋆ P) ·X+ (r ·ₕ Q)

  const x ·ₕ const y = const (x · y)
  0H ·ₕ Q = 0H
  (P ·X+ Q) ·ₕ S =
     let
        z = (P ·ₕ S)
     in if (isZero z)
        then (Q ⋆ S)
        else (z ·X+ 0ₕ) +ₕ (Q ⋆ S)

  isZeroPresLeft⋆ :
    {n : ℕ}
    (r : IteratedHornerForms n)
    (P : IteratedHornerForms (ℕ.suc n))
    → isZero r ≡ true
    → isZero (r ⋆ P) ≡ true
  isZeroPresLeft⋆ r 0H isZero-r = refl
  isZeroPresLeft⋆ r (P ·X+ Q) isZero-r with isZero r
  ...  | true = refl
  ...  | false = byBoolAbsurdity isZero-r

  isZeroPresLeft·ₕ :
    {n : ℕ} (P Q : IteratedHornerForms n)
    → isZero P ≡ true
    → isZero (P ·ₕ Q) ≡ true
  isZeroPresLeft·ₕ (const y) (const x) isZeroP =
    let zz = 𝟚.toWitness {Q = y ≟ 0r} (subst 𝟚.Bool→Type (sym isZeroP) _ )
     in cong {y = yes (0LeftAnnihilates' _ _ zz)} 𝟚.Dec→Bool (isPropDec (is-set _ _) _ _)
  isZeroPresLeft·ₕ 0H Q isZeroP = refl
  isZeroPresLeft·ₕ (P ·X+ Q) S isZeroSum with isZero (P ·ₕ S) 𝟚.≟ true
  ... | no p = byBoolAbsurdity (sym notZeroProd ∙ isZeroProd)
               where notZeroProd = 𝟚.¬true→false _ p
                     isZeroP = extractFromAndLeft isZeroSum
                     isZeroProd = isZeroPresLeft·ₕ P S isZeroP
  ... | yes p with isZero (P ·ₕ S)
  ...        | true = isZeroPresLeft⋆ Q S isZeroQ
                      where isZeroQ = extractFromAndRight isZeroSum
  ...        | false = byBoolAbsurdity p

  asRawRing : (n : ℕ) → RawRing ℓ
  RawRing.Carrier (asRawRing n) = IteratedHornerForms n
  RawRing.0r (asRawRing n) = 0ₕ
  RawRing.1r (asRawRing n) = 1ₕ
  RawRing._+_ (asRawRing n) = _+ₕ_
  RawRing._·_ (asRawRing n) = _·ₕ_
  RawRing.- (asRawRing n) =  -ₕ

 Variable : (n : ℕ) (k : Fin n) → IteratedHornerForms n
 Variable n k = IteratedHornerOperations.X n k

 Constant : (n : ℕ) (r : ⟨R⟩) → IteratedHornerForms n
 Constant ℕ.zero r = const r
 Constant (ℕ.suc n) r =
   decRec (λ _ → IteratedHornerOperations.0ₕ) (λ _ → IteratedHornerOperations.0ₕ ·X+ Constant n r) (r ≟ 0r)

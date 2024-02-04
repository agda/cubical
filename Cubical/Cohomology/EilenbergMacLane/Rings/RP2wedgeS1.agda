{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RP2wedgeS1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2wedgeS1
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.Groups.Wedge
open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle hiding (α↦1)

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Loopspace
open import Cubical.Cohomology.EilenbergMacLane.RingStructure
open import Cubical.Cohomology.EilenbergMacLane.Rings.Z2-properties

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Fin hiding (FinVec)
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.FinData renaming (Fin to FinI)

open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _sq/_)
open import Cubical.HITs.EilenbergMacLane1 hiding (elimProp ; elimSet)
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1 renaming (rec to S¹Fun)
open import Cubical.HITs.Sn
open import Cubical.HITs.RPn
open import Cubical.HITs.Wedge

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup.TensorProduct

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ2

open Iso
open PlusBis
open RingTheory

open AbGroupStr


-- move to RP2
RP²∙ : Pointed ℓ-zero
RP²∙ = RP² , point

RP²∨S¹ = RP²∙ ⋁ (S₊∙ 1)

gen-H¹RP²-raw : RP² → EM ℤ/2 1
gen-H¹RP²-raw =
  RP²Fun embase (emloop 1) (emloop-inv (ℤGroup/ 2) 1)

RP²∨S¹→K₂-fun : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2))) → RP²∨S¹ → EM ℤ/2 2
RP²∨S¹→K₂-fun p (inl x) = RP²Fun (0ₖ 2) refl p x
RP²∨S¹→K₂-fun p (inr x) = 0ₖ 2
RP²∨S¹→K₂-fun p (push a i) = 0ₖ 2

private
  α-raw : RP²∨S¹ → EM ℤ/2 1
  α-raw (inl x) = gen-H¹RP²-raw x
  α-raw (inr x) = embase
  α-raw (push a i) = embase

  β-raw : RP²∨S¹ → EM ℤ/2 1
  β-raw (inl x) = embase
  β-raw (inr x) = S¹Fun embase (emloop 1) x
  β-raw (push a i) = embase

  α : coHom 1 ℤ/2 RP²∨S¹
  α = ∣ α-raw ∣₂

  β : coHom 1 ℤ/2 RP²∨S¹
  β = ∣ β-raw ∣₂

  α↦1 : fst (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) α ≡ (1 , 0)
  α↦1 = refl

  β↦1 : fst (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) β ≡ (0 , 1)
  β↦1 = refl

  γ-raw : RP²∨S¹ → EM ℤ/2 2
  γ-raw = RP²∨S¹→K₂-fun (Iso.inv Iso-Ω²K₂-ℤ/2 1)

  γ-raw⨂ : RP²∨S¹ → EM (ℤ/2 ⨂ ℤ/2) 2
  γ-raw⨂ (inl x) = RP²Fun (0ₖ 2) refl (ℤ/2→Ω²K₂⨂ 1) x
  γ-raw⨂ (inr x) = 0ₖ 2
  γ-raw⨂ (push a i) = 0ₖ 2

  γ : coHom 2 ℤ/2 RP²∨S¹
  γ = ∣ γ-raw ∣₂

γ↦1 : fst (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2) γ ≡ 1
γ↦1 = γ↦1' _ refl
  where
  -- silly lemma for faster type checking
  γ↦1' : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2)))
    → (p ≡ Iso.inv Iso-Ω²K₂-ℤ/2 1)
    → fst (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2) (∣ RP²∨S¹→K₂-fun p ∣₂) ≡ 1
  γ↦1' p q =
      H²[RP²,ℤ/2]→ℤ/2-Id p
    ∙ cong (Iso.fun Iso-Ω²K₂-ℤ/2) q
    ∙ Iso.rightInv Iso-Ω²K₂-ℤ/2 1

private
  cp : EM ℤ/2 1 → EM ℤ/2 1 → EM (ℤ/2 ⨂ ℤ/2) 2
  cp = _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}

β²-raw⨂ : (x : RP²∨S¹) → cp (β-raw x) (β-raw x) ≡ 0ₖ 2
β²-raw⨂ (inl x) = refl
β²-raw⨂ (inr base) = refl
β²-raw⨂ (inr (loop i)) j = cong₂-⌣ (emloop 1) j i
β²-raw⨂ (push a i) = refl

αβ-raw⨂ : (x : RP²∨S¹) → cp (α-raw x) (β-raw x) ≡ 0ₖ 2
αβ-raw⨂ (inl x) = ⌣ₖ-0ₖ⊗ 1 1 (gen-H¹RP²-raw x)
αβ-raw⨂ (inr x) = 0ₖ-⌣ₖ⊗ 1 1 (S¹Fun embase (emloop (fsuc fzero)) x)
αβ-raw⨂ (push a i) = refl

βα-raw⨂ : (x : RP²∨S¹) → cp (β-raw x) (α-raw x) ≡ 0ₖ 2
βα-raw⨂ (inl x) = 0ₖ-⌣ₖ⊗ 1 1 (gen-H¹RP²-raw x)
βα-raw⨂ (inr x) = ⌣ₖ-0ₖ⊗ 1 1 (S¹Fun embase (emloop (fsuc fzero)) x)
βα-raw⨂ (push a i) = refl

α²-raw⨂ : (x : RP²∨S¹) → cp (α-raw x) (α-raw x) ≡ γ-raw⨂ x
α²-raw⨂ (inl point) = refl
α²-raw⨂ (inl (line i)) j = cong₂-⌣ (emloop 1) j i
α²-raw⨂ (inl (square i j)) k = filler i j k
  where
  Typ : (p : fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))) → Type
  Typ p =
    Cube (λ j k → cong₂-⌣ (emloop 1) k j)
         (λ j k → cong₂-⌣ (emloop (fsuc fzero)) k (~ j))
         (λ _ _ → ∣ north ∣) (λ _ _ → ∣ north ∣)
         (λ i j → cp (emloop-inv (ℤGroup/ 2) 1 i j)
                    (emloop-inv (ℤGroup/ 2) 1 i j))
         p

  filler : Typ (ℤ/2→Ω²K₂⨂ (fsuc fzero))
  filler = subst Typ (sym (ℤ/2→Flip₁ 1 1)) λ i j k → ▣₇ j (~ i) k
α²-raw⨂ (inr x) = refl
α²-raw⨂ (push a i) = refl

α²-raw : (x : RP²∨S¹) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} (α-raw x) (α-raw x)
                  ≡ γ-raw x
α²-raw x = cong (EMTensorMult 2) (α²-raw⨂ x)
     ∙ lem x
     ∙ γ-raw≡ x
  where
  γ-raw' : RP²∨S¹ → EM ℤ/2 2
  γ-raw' (inl point) = 0ₖ 2
  γ-raw' (inl (line i)) = 0ₖ 2
  γ-raw' (inl (square i j)) = ℤ/2→Ω²K₂' 1 i j
  γ-raw' (inr x) = 0ₖ 2
  γ-raw' (push a i) = 0ₖ 2

  γ-raw≡ : (x : _) → γ-raw' x ≡ γ-raw x
  γ-raw≡ (inl point) = refl
  γ-raw≡ (inl (line i)) = refl
  γ-raw≡ (inl (square i j)) k = ℤ/2→Ω²K₂'≡ (~ k) i j
  γ-raw≡ (inr x) = refl
  γ-raw≡ (push a i) = refl

  lem : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 (γ-raw⨂ x) ≡ γ-raw' x
  lem (inl point) = refl
  lem (inl (line i)) = refl
  lem (inl (square i j)) k =
    hcomp (λ r
      → λ {(i = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (EM→ΩEM+1-0ₖ 1 (r ∨ k) j)
          ; (i = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (EM→ΩEM+1-0ₖ 1 (r ∨ k) j)
          ; (j = i0) → 0ₖ 2
          ; (j = i1) → 0ₖ 2
          ; (k = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (doubleCompPath-filler
                           (sym (EM→ΩEM+1-0ₖ 1))
                           (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1)))
                           (EM→ΩEM+1-0ₖ 1) r i j)
          ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
      (hcomp (λ r
        → λ {(i = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ rCancel-filler (merid embase) r k j ∣ₕ
            ; (i = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ rCancel-filler (merid embase) r k j ∣ₕ
            ; (j = i0) → 0ₖ 2
            ; (j = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ merid embase (~ r ∧ ~ k) ∣ₕ
            ; (k = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ compPath-filler (merid (EM→ΩEM+1 0 (1 ⊗ 1) i))
                                             (sym (merid embase)) r j ∣ₕ
            ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
        (hcomp (λ r
          → λ {(i = i0) → ∣ rCancel-filler (merid embase) (~ r) k j ∣ₕ
              ; (i = i1) → ∣ rCancel-filler (merid embase) (~ r) k j ∣ₕ
              ; (j = i0) → 0ₖ 2
              ; (j = i1) → ∣ merid embase (~ k ∧ r) ∣ₕ
              ; (k = i0) → ∣ compPath-filler (merid (EM→ΩEM+1 0 1 i))
                                             (sym (merid embase)) (~ r) j ∣ₕ
              ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
         (doubleCompPath-filler
           (sym (EM→ΩEM+1-0ₖ 1))
           (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 1))
           (EM→ΩEM+1-0ₖ 1) k i j)))
  lem (inr x) = refl
  lem (push a i) = refl

open CbnCupProduct RP²∨S¹

-- He can't seem to be able to find P and AGP in some case especially with cong
-- Sometimes it works, sometimes not, the reason is currently unknown
baseH* : (n : ℕ) → (a : coHom n ℤ/2 RP²∨S¹) → H*ℤ/2 RP²∨S¹
baseH* n a = base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP²∨S¹} {AGP = λ n → snd (coHomGr n ℤ/2 RP²∨S¹)} n a

baseP : (n : Vec ℕ 2) → (a : fst ℤ/2) → ℤ/2[x,y]
baseP n a = base {Idx = Vec ℕ 2} {P = λ n → fst ℤ/2} {AGP = λ n → snd ℤ/2} n a

{- Convention over ℤ[X,Y]
   X : (1,0)
   Y : (0,1)
-}

<Y³,XY,X²> : FinVec ℤ/2[x,y] 3
<Y³,XY,X²> zero  = base (0 ∷ 3 ∷ []) 1
<Y³,XY,X²> one   = base (1 ∷ 1 ∷ []) 1
<Y³,XY,X²> two   = base (2 ∷ 0 ∷ []) 1

ℤ/2[X,Y]/<Y³,XY,X²> : CommRing ℓ-zero
ℤ/2[X,Y]/<Y³,XY,X²> = PolyCommRing-Quotient ℤ/2CommRing <Y³,XY,X²>

ℤ/2[x,y]/<y³,xy,x²> : Type ℓ-zero
ℤ/2[x,y]/<y³,xy,x²> = fst ℤ/2[X,Y]/<Y³,XY,X²>

module Equiv-RP²∨S¹-Properties
  (e₀ : AbGroupIso ℤ/2 (coHomGr 0 ℤ/2 RP²∨S¹))
  (e₁ : AbGroupIso (dirProdAb ℤ/2 ℤ/2) (coHomGr 1 ℤ/2 RP²∨S¹))
  (e₂ : AbGroupIso ℤ/2 (coHomGr 2 ℤ/2 RP²∨S¹))
  (eₙ₊₃ : (n : ℕ) → (3 ≤ n) → AbGroupIso (coHomGr n ℤ/2 RP²∨S¹) (UnitAbGroup {ℓ = ℓ-zero}))
  where


-----------------------------------------------------------------------------
-- Definitions, Import with notations

  -- Import with notation
  open IsGroupHom
  open AbGroupStr

  open CommRingStr (snd ℤ/2CommRing) using ()
    renaming
    ( 0r        to 0ℤ/2
    ; 1r        to 1ℤ/2
    ; _+_       to _+ℤ/2_
    ; -_        to -ℤ/2_
    ; _·_       to _·ℤ/2_
    ; +Assoc    to +ℤ/2Assoc
    ; +IdL      to +ℤ/2IdL
    ; +IdR      to +ℤ/2IdR
    ; +Comm     to +ℤ/2Comm
    ; ·Assoc    to ·ℤ/2Assoc
    ; ·IdL      to ·ℤ/2IdL
    ; ·IdR      to ·ℤ/2IdR
    ; ·DistR+   to ·ℤ/2DistR+
    ; ·Comm     to ·ℤ/2Comm
    ; is-set    to isSetℤ/2     )

  open RingStr (snd (H*Rℤ/2 RP²∨S¹)) using ()
    renaming
    ( 0r        to 0H*
    ; 1r        to 1H*
    ; _+_       to _+H*_
    ; -_        to -H*_
    ; _·_       to _cup_
    ; +Assoc    to +H*Assoc
    ; +IdL      to +H*IdL
    ; +IdR      to +H*IdR
    ; +Comm     to +H*Comm
    ; ·Assoc    to ·H*Assoc
    ; ·IdL      to ·H*IdL
    ; ·IdR      to ·H*IdR
    ; ·DistR+   to ·H*DistR+
    ; is-set    to isSetH*     )

  open CommRingStr (snd ℤ/2[X,Y]) using ()
    renaming
    ( 0r        to 0Pℤ/2
    ; 1r        to 1Pℤ/2
    ; _+_       to _+Pℤ/2_
    ; -_        to -Pℤ/2_
    ; _·_       to _·Pℤ/2_
    ; +Assoc    to +Pℤ/2Assoc
    ; +IdL      to +Pℤ/2IdL
    ; +IdR      to +Pℤ/2IdR
    ; +Comm     to +Pℤ/2Comm
    ; ·Assoc    to ·Pℤ/2Assoc
    ; ·IdL      to ·Pℤ/2IdL
    ; ·IdR      to ·Pℤ/2IdR
    ; ·Comm     to ·Pℤ/2Comm
    ; ·DistR+   to ·Pℤ/2DistR+
    ; is-set    to isSetPℤ/2     )

  open CommRingStr (snd ℤ/2[X,Y]/<Y³,XY,X²>) using ()
    renaming
    ( 0r        to 0Pℤ/2I
    ; 1r        to 1Pℤ/2I
    ; _+_       to _+Pℤ/2I_
    ; -_        to -Pℤ/2I_
    ; _·_       to _·Pℤ/2I_
    ; +Assoc    to +Pℤ/2IAssoc
    ; +IdL      to +Pℤ/2IIdL
    ; +IdR      to +Pℤ/2IIdR
    ; +Comm     to +Pℤ/2IComm
    ; ·Assoc    to ·Pℤ/2IAssoc
    ; ·IdL      to ·Pℤ/2IIdL
    ; ·IdR      to ·Pℤ/2IIdR
    ; ·DistR+   to ·Pℤ/2IDistR+
    ; is-set    to isSetPℤ/2I     )


  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  ϕ₁ = fun (fst e₁)
  ϕ₁str = snd e₁
  ϕ₁⁻¹ = inv (fst e₁)
  ϕ₁⁻¹str = snd (invGroupIso e₁)
  ϕ₁-sect = rightInv (fst e₁)
  ϕ₁-retr = leftInv (fst e₁)

  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  ϕ₁left : fst ℤ/2 → coHom 1 ℤ/2 RP²∨S¹
  ϕ₁left a = ϕ₁ (a , 0ℤ/2)

  ϕ₁leftStr : IsGroupHom (snd (AbGroup→Group ℤ/2)) ϕ₁left (snd (AbGroup→Group (coHomGr 1 ℤ/2 RP²∨S¹)))
  ϕ₁leftStr = makeIsGroupHom (λ a b → pres· ϕ₁str _ _)

  ϕ₁right : fst ℤ/2 → coHom 1 ℤ/2 RP²∨S¹
  ϕ₁right b = ϕ₁ (0ℤ/2 , b)

  ϕ₁rightStr : IsGroupHom (snd (AbGroup→Group ℤ/2)) ϕ₁right (snd (AbGroup→Group (coHomGr 1 ℤ/2 RP²∨S¹)))
  ϕ₁rightStr = makeIsGroupHom (λ a b → pres· ϕ₁str _ _)

  module CompPoperties
    (ϕ₀-pres1 : ϕ₀ 1ℤ/2 ≡ 1ₕ {G'' = ℤ/2Ring})
    (ϕ₁-1010-notTrivial : (ϕ₁ (1ℤ/2 , 0ℤ/2)) ⌣ℤ/2 (ϕ₁ (1ℤ/2 , 0ℤ/2)) ≡ ϕ₂ 1ℤ/2)
    (ϕ₁-0101-trivial : (ϕ₁ (0ℤ/2 , 1ℤ/2) ⌣ℤ/2 ϕ₁ (0ℤ/2 , 1ℤ/2)) ≡ (0ₕ 2))
    (ϕ₁-1001-trivial : (ϕ₁ (1ℤ/2 , 0ℤ/2) ⌣ℤ/2 ϕ₁ (0ℤ/2 , 1ℤ/2)) ≡ (0ₕ 2))
    (ϕ₁-0110-trivial : (ϕ₁ (0ℤ/2 , 1ℤ/2) ⌣ℤ/2 ϕ₁ (1ℤ/2 , 0ℤ/2)) ≡ (0ₕ 2))
    where

  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ/2[x,y]

    ℤ/2[x,y]→H*-RP²∨S¹ : ℤ/2[x,y] → (H*ℤ/2  RP²∨S¹)
    ℤ/2[x,y]→H*-RP²∨S¹ = DS-Rec-Set.f _ _ _ _ isSetH*
                        0H*
                        ϕ
                        _+H*_
                        +H*Assoc
                        +H*IdR
                        +H*Comm
                        base-neutral-eq
                        base-add-eq
     where
     ϕ : _
     ϕ (zero        ∷ zero              ∷ []) a = base 0 (ϕ₀ a)
     ϕ (zero        ∷ one               ∷ []) a = base 1 (ϕ₁ (a , 0ℤ/2))
     ϕ (zero        ∷ two               ∷ []) a = base 2 (ϕ₂ a)
     ϕ (zero        ∷ suc (suc (suc m)) ∷ []) a = 0H*
     ϕ (one         ∷ zero              ∷ []) a = base 1 (ϕ₁ (0ℤ/2 , a))
     ϕ (one         ∷ suc m             ∷ []) a = 0H*
     ϕ (suc (suc n) ∷ m                 ∷ []) a = 0H*

     base-neutral-eq : _
     base-neutral-eq (zero        ∷ zero              ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ one               ∷ []) = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ two               ∷ []) = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ suc (suc (suc m)) ∷ []) = refl
     base-neutral-eq (one         ∷ zero              ∷ []) = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
     base-neutral-eq (one         ∷ suc m             ∷ []) = refl
     base-neutral-eq (suc (suc n) ∷ m                 ∷ []) = refl

     base-add-eq : _
     base-add-eq (zero        ∷ zero              ∷ []) a b = base-add _ _ _
                                                              ∙ cong (base 0) (sym ((pres· ϕ₀str _ _)))
     base-add-eq (zero        ∷ one               ∷ []) a b = base-add _ _ _
                                                              ∙ cong (baseH* 1) ((sym (pres· ϕ₁str _ _)))
     base-add-eq (zero        ∷ two               ∷ []) a b = base-add 2 (ϕ₂ a) (ϕ₂ b)
                                                              ∙ cong (baseH* 2) (sym (pres· ϕ₂str _ _))
     base-add-eq (zero        ∷ suc (suc (suc m)) ∷ []) a b = +H*IdR _
     base-add-eq (one         ∷ zero              ∷ []) a b = base-add _ _ _
                                                              ∙ cong (baseH* 1) ((sym (pres· ϕ₁str _ _)))
     base-add-eq (one         ∷ suc m             ∷ []) a b = +H*IdR _
     base-add-eq (suc (suc n) ∷ m                 ∷ []) a b = +H*IdR _



  -----------------------------------------------------------------------------
  -- Morphism on ℤ/2[x]

    ℤ/2[x,y]→H*-RP²∨S¹-pres1 : ℤ/2[x,y]→H*-RP²∨S¹ (1Pℤ/2) ≡ 1H*
    ℤ/2[x,y]→H*-RP²∨S¹-pres1 = cong (base 0) ϕ₀-pres1

    ℤ/2[x,y]→H*-RP²∨S¹-pres+ : (x y : ℤ/2[x,y]) →
                                    ℤ/2[x,y]→H*-RP²∨S¹ (x +Pℤ/2 y)
                                  ≡ ℤ/2[x,y]→H*-RP²∨S¹ x +H* ℤ/2[x,y]→H*-RP²∨S¹ y
    ℤ/2[x,y]→H*-RP²∨S¹-pres+ x y = refl

--                Explanation of the product proof
--
--                ---------------------------------------------------------------
--                | (0,0) | (0,1) | (0,2) | (0,m+2) | (1,0) | (1,m+1) | (n+2,m) |
--      -------------------------------------------------------------------------
--      | (0,0)   |   H⁰  |   H⁰  |   H⁰  |   triv  |  H⁰   |  triv   |  triv   |
--      -------------------------------------------------------------------------
--      | (0,1)   |  H⁰   |   β²  |   0₃  |   triv  |  βα   |  triv   |  triv   |
--      -------------------------------------------------------------------------
--      | (0,2)   |  H⁰   |   0₄  |   0₄  |   triv  |  0₂   |  triv   |  triv   |
--      -------------------------------------------------------------------------
--      | (0,m+2) | ====================================================> triv  |
--      -------------------------------------------------------------------------
--      | (1,0)   |  H⁰   |   αβ  |   0₃  |   triv  |   α   |  triv   |  triv   |
--      -------------------------------------------------------------------------
--      | (1,m+1) | ==================================================> triv    |
--      -------------------------------------------------------------------------
--      | (n+2,m) | ==================================================> triv    |
--      -------------------------------------------------------------------------


    ϕ₀⌣IdL : {n : ℕ} → (f : coHom n ℤ/2 RP²∨S¹) → ϕ₀ (1ℤ/2) ⌣ℤ/2 f ≡ f
    ϕ₀⌣IdL f = cong (λ X → X ⌣ℤ/2 f) ϕ₀-pres1 ∙ 1ₕ-⌣ {G'' = ℤ/2Ring} _ f

    lem-ϕ₀⌣ : (a b : fst ℤ/2) → {n : ℕ} → (ϕₙ : fst ℤ/2 → coHom n ℤ/2 RP²∨S¹) →
              (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 RP²∨S¹))))
               → ϕ₀ a ⌣ℤ/2 ϕₙ b ≡ ϕₙ (a ·ℤ/2 b)
    lem-ϕ₀⌣ a b ϕₙ ϕₙstr = ℤ/2-elim {A = λ a → ϕ₀ a ⌣ℤ/2 ϕₙ b ≡ ϕₙ (a ·ℤ/2 b)}
                          (cong (λ X → X ⌣ℤ/2 ϕₙ b) (pres1 ϕ₀str)
                            ∙ 0ₕ-⌣ _ _ _
                            ∙ sym (pres1 ϕₙstr)
                            ∙ cong ϕₙ (sym (0LeftAnnihilates ℤ/2Ring _)))
                          (ϕ₀⌣IdL _ ∙ cong ϕₙ (sym (·ℤ/2IdL _)))
                          a

    pres·-int : (n m : ℕ) → (a : fst ℤ/2) → (k l : ℕ) → (b : fst ℤ/2) →
                   ℤ/2[x,y]→H*-RP²∨S¹ (base (n ∷ m ∷ []) a ·Pℤ/2 base (k ∷ l ∷ []) b)
                ≡ ℤ/2[x,y]→H*-RP²∨S¹ (base (n ∷ m ∷ []) a) cup ℤ/2[x,y]→H*-RP²∨S¹ (base (k ∷ l ∷ []) b)
    -- non trivial case (0,0)
    pres·-int zero zero a zero zero b = cong (baseH* 0) (sym (lem-ϕ₀⌣ _ _ ϕ₀ ϕ₀str))
    pres·-int zero zero a zero one b = cong (baseH* 1) (sym (lem-ϕ₀⌣ _ _ ϕ₁left ϕ₁leftStr))
    pres·-int zero zero a zero two b = cong (baseH* 2) (sym (lem-ϕ₀⌣ _ _ ϕ₂ ϕ₂str))
    pres·-int zero zero a zero (suc (suc (suc l))) b = refl
    pres·-int zero zero a one zero b = cong (baseH* 1) (sym (lem-ϕ₀⌣ _ _ (λ b → ϕ₁ (0ℤ/2 , b))
                                                      (makeIsGroupHom (λ a b → pres· ϕ₁str _ _))))
    pres·-int zero zero a one (suc l) b = refl
    pres·-int zero zero a (suc (suc k)) l b = refl
    -- case (0,1) not trivial
    pres·-int zero one a zero zero b = cong (baseH* 1) (sym (ϕₙ⌣ϕₘ-notTrivial
                                       ϕ₁left ϕ₁leftStr ϕ₀ ϕ₀str ϕ₁left ϕ₁leftStr
                                       ((cong (λ X → ϕ₁left 1ℤ/2 ⌣ℤ/2 X) ϕ₀-pres1)
                                         ∙ ⌣-1ₕ {G'' = ℤ/2Ring} _ _
                                         ∙ cong (λ X → subst (λ Y → coHom Y ℤ/2 RP²∨S¹) X (ϕ₁ (1ℤ/2 , 0ℤ/2)))
                                                (isSetℕ _ _ (+'-comm zero 1) (refl {x = 1}))
                                         ∙ substRefl _)
                                       _ _))
      -- case α²
    pres·-int zero one a zero one b = cong (baseH* 2) (sym (ϕₙ⌣ϕₘ-notTrivial
                                                            ϕ₁left ϕ₁leftStr ϕ₁left ϕ₁leftStr ϕ₂ ϕ₂str
                                                            ϕ₁-1010-notTrivial a b))
    pres·-int zero one a zero two b = sym (base-neutral _) ∙ cong (baseH* 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero one a zero (suc (suc (suc l))) b = refl
      -- case αβ
    pres·-int zero one a one zero b = sym (cong (baseH* 2) (ϕₙ⌣ϕₘ-Trivial
                                                            ϕ₁left ϕ₁leftStr ϕ₁right ϕ₁rightStr
                                                            ϕ₁-1001-trivial a b)
                                          ∙ base-neutral 2)
    pres·-int zero one a one (suc l) b = refl
    pres·-int zero one a (suc (suc k)) l b = refl
    -- case (0,2) trivial right, by trivial goups
    pres·-int zero two a zero zero b = cong (baseH* 2) (sym (ϕₙ⌣ϕₘ-notTrivial
                                       ϕ₂ ϕ₂str ϕ₀ ϕ₀str ϕ₂ ϕ₂str
                                       ((cong (λ X → ϕ₂ 1ℤ/2 ⌣ℤ/2 X) ϕ₀-pres1)
                                         ∙ ⌣-1ₕ {G'' = ℤ/2Ring} _ _
                                         ∙ cong (λ X → subst (λ Y → coHom Y ℤ/2 RP²∨S¹) X (ϕ₂ 1ℤ/2))
                                                (isSetℕ _ _ (+'-comm zero 2) (refl {x = 2}))
                                         ∙ substRefl _)
                                       _ _))
    pres·-int zero two a zero one b = sym (base-neutral _) ∙ cong (baseH* 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero two a zero two b = sym (base-neutral _) ∙ cong (baseH* 4) (unitGroupEq (eₙ₊₃ 4 (1 , refl)) _ _)
    pres·-int zero two a zero (suc (suc (suc l))) b = refl
    pres·-int zero two a one zero b = sym (base-neutral _) ∙ cong (baseH* 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero two a one (suc l) b = refl
    pres·-int zero two a (suc (suc k)) l b = refl
    -- case (0,m+2) trivial left, by def
    pres·-int zero (suc (suc (suc m))) a zero zero b = refl
    pres·-int zero (suc (suc (suc m))) a zero one b = refl
    pres·-int zero (suc (suc (suc m))) a zero two b = refl
    pres·-int zero (suc (suc (suc m))) a zero (suc (suc (suc l))) b = refl
    pres·-int zero (suc (suc (suc m))) a one zero b = refl
    pres·-int zero (suc (suc (suc m))) a one (suc l) b = refl
    pres·-int zero (suc (suc (suc m))) a (suc (suc k)) l b = refl
    -- case (1,0) not trivial
    pres·-int one zero a zero zero b = cong (baseH* 1) (sym (ϕₙ⌣ϕₘ-notTrivial
                                       ϕ₁right ϕ₁rightStr ϕ₀ ϕ₀str ϕ₁right ϕ₁rightStr
                                       (cong (λ X → ϕ₁right 1ℤ/2 ⌣ℤ/2 X) ϕ₀-pres1
                                       ∙ ⌣-1ₕ {G'' = ℤ/2Ring} _ (ϕ₁right 1ℤ/2)
                                       ∙ cong (λ X → subst (λ Y → coHom Y ℤ/2 RP²∨S¹) X (ϕ₁right 1ℤ/2))
                                              (isSetℕ _ _ (+'-comm zero 1) (refl {x = 1}))
                                       ∙ substRefl _)
                                       a b))
      -- case βα
    pres·-int one zero a zero one b = sym (cong (baseH* 2)
                                                (ϕₙ⌣ϕₘ-Trivial ϕ₁right ϕ₁rightStr ϕ₁left ϕ₁leftStr ϕ₁-0110-trivial a b)
                                      ∙ base-neutral _)
    pres·-int one zero a zero two b = sym (base-neutral _) ∙ cong (baseH* 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int one zero a zero (suc (suc (suc l))) b = refl
      -- case β²
    pres·-int one zero a one zero b = sym (cong (baseH* 2)
                                                (ϕₙ⌣ϕₘ-Trivial ϕ₁right ϕ₁rightStr ϕ₁right ϕ₁rightStr ϕ₁-0101-trivial a b)
                                          ∙ base-neutral _)
    pres·-int one zero a one (suc l) b = refl
    pres·-int one zero a (suc (suc k)) l b = refl
    -- case (1,m+1) trivial left, by def
    pres·-int one (suc m) a zero l b = refl
    pres·-int one (suc m) a (suc k) l b = refl
    -- case (1,m+1) trivial left, by def
    pres·-int (suc (suc n)) m a k l b = refl

    pres·-base-case-vec : (v : Vec ℕ 2) → (a : fst ℤ/2) → (v' : Vec ℕ 2) → (b : fst ℤ/2) →
                             ℤ/2[x,y]→H*-RP²∨S¹ (base v a ·Pℤ/2 base v' b)
                          ≡ ℤ/2[x,y]→H*-RP²∨S¹ (base v a) cup ℤ/2[x,y]→H*-RP²∨S¹ (base v' b)
    pres·-base-case-vec (n ∷ m ∷ []) a (k ∷ l ∷ []) b = pres·-int n m a k l b

    -- proof of the morphism
    ℤ/2[x,y]→H*-RP²∨S¹-pres· : (x y : ℤ/2[x,y]) →
                                   ℤ/2[x,y]→H*-RP²∨S¹ (x ·Pℤ/2 y)
                                 ≡ ℤ/2[x,y]→H*-RP²∨S¹ x cup ℤ/2[x,y]→H*-RP²∨S¹ y
    ℤ/2[x,y]→H*-RP²∨S¹-pres· = DS-Ind-Prop.f _ _ _ _
                           (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                           (λ y → refl)
                           base-case
                           λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
      where
      base-case : _
      base-case v a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                             (sym (RingTheory.0RightAnnihilates (H*Rℤ/2 RP²∨S¹) _))
                             (λ v' b → pres·-base-case-vec v a v' b )
                             λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


  -----------------------------------------------------------------------------
  -- Function on ℤ/2[x]/x + morphism

    ℤ/2[x,y]→H*-RP²∨S¹-cancel : (x : FinI 3) → ℤ/2[x,y]→H*-RP²∨S¹ (<Y³,XY,X²> x) ≡ 0H*
    ℤ/2[x,y]→H*-RP²∨S¹-cancel zero = refl
    ℤ/2[x,y]→H*-RP²∨S¹-cancel one = refl
    ℤ/2[x,y]→H*-RP²∨S¹-cancel two = refl

    ℤ/2[X,Y]→H*-RP²∨S¹ : RingHom (CommRing→Ring ℤ/2[X,Y]) (H*Rℤ/2 RP²∨S¹)
    fst ℤ/2[X,Y]→H*-RP²∨S¹ = ℤ/2[x,y]→H*-RP²∨S¹
    snd ℤ/2[X,Y]→H*-RP²∨S¹ = makeIsRingHom ℤ/2[x,y]→H*-RP²∨S¹-pres1
                                       ℤ/2[x,y]→H*-RP²∨S¹-pres+
                                       ℤ/2[x,y]→H*-RP²∨S¹-pres·

    -- hence not a trivial pres+, yet pres0 still is
    ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹ : RingHom (CommRing→Ring ℤ/2[X,Y]/<Y³,XY,X²>) (H*Rℤ/2 RP²∨S¹)
    ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹ = Quotient-FGideal-CommRing-Ring.inducedHom
                                    ℤ/2[X,Y] (H*Rℤ/2 RP²∨S¹) ℤ/2[X,Y]→H*-RP²∨S¹
                                    <Y³,XY,X²> ℤ/2[x,y]→H*-RP²∨S¹-cancel

    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ : ℤ/2[x,y]/<y³,xy,x²> → H*ℤ/2 RP²∨S¹
    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ = fst ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹

    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹-pres0 : ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ 0Pℤ/2I ≡ 0H*
    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹-pres0 = refl

    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹-pres+ : (x y : ℤ/2[x,y]/<y³,xy,x²>) →
                                             ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ ( x +Pℤ/2I y)
                                          ≡ ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ x +H* ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ y
    ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹-pres+ x y = IsRingHom.pres+ (snd ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹) x y


  -----------------------------------------------------------------------------
  -- Converse direction on H* → ℤ/2[X,Y]

    ϕ⁻¹ : (k : ℕ) → (a : coHom k ℤ/2 RP²∨S¹) → ℤ/2[x,y]
    ϕ⁻¹ zero a = base (0 ∷ 0 ∷ []) (ϕ₀⁻¹ a)
    ϕ⁻¹ one a = (base (0 ∷ 1 ∷ []) (fst (ϕ₁⁻¹ a))) +Pℤ/2 base (1 ∷ 0 ∷ []) (snd (ϕ₁⁻¹ a))
    ϕ⁻¹ two a = base (0 ∷ 2 ∷ []) (ϕ₂⁻¹ a)
    ϕ⁻¹ (suc (suc (suc k))) a = 0Pℤ/2

    H*-RP²∨S¹→ℤ/2[x,y] : H*ℤ/2 RP²∨S¹ → ℤ/2[x,y]
    H*-RP²∨S¹→ℤ/2[x,y] = DS-Rec-Set.f _ _ _ _ isSetPℤ/2
         0Pℤ/2
         ϕ⁻¹
         _+Pℤ/2_
         +Pℤ/2Assoc
         +Pℤ/2IdR
         +Pℤ/2Comm
         base-neutral-eq
         base-add-eq
      where

      base-neutral-eq : _
      base-neutral-eq zero = cong (baseP (0 ∷ 0 ∷ [])) (pres1 ϕ₀⁻¹str) ∙ base-neutral _
      base-neutral-eq one = cong₂ _+Pℤ/2_
                                  (cong (baseP (0 ∷ 1 ∷ [])) (cong fst (pres1 ϕ₁⁻¹str)) ∙ base-neutral _)
                                  (cong (baseP (1 ∷ 0 ∷ [])) (cong snd (pres1 ϕ₁⁻¹str)) ∙ base-neutral _)
                            ∙ +Pℤ/2IdR 0Pℤ/2
      base-neutral-eq two = cong (baseP (0 ∷ 2 ∷ [])) (pres1 ϕ₂⁻¹str) ∙ base-neutral _
      base-neutral-eq (suc (suc (suc k))) = refl

      base-add-eq : _
      base-add-eq zero a b = base-add _ _ _ ∙ cong (baseP (0 ∷ 0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _))
      base-add-eq one a b = +ShufflePairs (CommRing→Ring ℤ/2[X,Y]) _ _ _ _
                            ∙ cong₂ _+Pℤ/2_
                                    (base-add _ _ _ ∙ cong (baseP (0 ∷ 1 ∷ [])) (cong fst ((sym (pres· ϕ₁⁻¹str _ _)))))
                                    (base-add _ _ _ ∙ cong (baseP (1 ∷ 0 ∷ [])) (cong snd ((sym (pres· ϕ₁⁻¹str _ _)))))
      base-add-eq two a b = base-add _ _ _ ∙ cong (baseP (0 ∷ 2 ∷ [])) (sym (pres· ϕ₂⁻¹str _ _))
      base-add-eq (suc (suc (suc k))) a b = +Pℤ/2IdR _


    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> : H*ℤ/2 RP²∨S¹ → ℤ/2[x,y]/<y³,xy,x²>
    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> = [_] ∘ H*-RP²∨S¹→ℤ/2[x,y]

    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²>-pres0 : H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> 0H* ≡ 0Pℤ/2I
    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²>-pres0 = refl

    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²>-pres+ : (x y : H*ℤ/2 RP²∨S¹) →
                                               H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> (x +H* y)
                                           ≡ (H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> x) +Pℤ/2I (H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> y)
    H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²>-pres+ x y = refl


  -----------------------------------------------------------------------------
  -- Section

    e-sect-base : (k : ℕ) → (a : coHom k ℤ/2 RP²∨S¹) →
                  ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ ([ ϕ⁻¹ k a ]) ≡ base k a
    e-sect-base zero a = cong (baseH* 0) (ϕ₀-sect a)
    e-sect-base one a = base-add _ _ _
                        ∙ cong (baseH* 1) (sym (pres· ϕ₁str _ _)
                                          ∙ cong ϕ₁ (cong₂ _,_ (+ℤ/2IdR _) (+ℤ/2IdL _))
                                          ∙ ϕ₁-sect a)
    e-sect-base two a = cong (baseH* 2) (ϕ₂-sect a)
    e-sect-base (suc (suc (suc k))) a = sym (base-neutral (suc (suc (suc k))))
                                        ∙ cong (baseH* (suc (suc (suc k))))
                                               (unitGroupEq (eₙ₊₃ (suc (suc (suc k))) (k , (+-comm _ _))) _ _)


    e-sect : (x : H*ℤ/2 RP²∨S¹) → ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ (H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> x) ≡ x
    e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
             refl
             e-sect-base
             λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V

  -----------------------------------------------------------------------------
  -- Retraction

    e-retr-base : (v : Vec ℕ 2) → (a : fst ℤ/2) →
                  H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> (ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ [ base v a ]) ≡ [ base v a ]
    e-retr-base (zero ∷ zero ∷ []) a = cong [_] (cong (baseP (0 ∷ 0 ∷ [])) (ϕ₀-retr a))
    e-retr-base (zero ∷ one ∷ []) a =
      cong [_] (cong₂ _+Pℤ/2_
                     (cong (baseP (0 ∷ 1 ∷ [])) (cong fst (ϕ₁-retr _)))
                     (cong (baseP (1 ∷ 0 ∷ [])) (cong snd (ϕ₁-retr _)) ∙ base-neutral _)
              ∙ +Pℤ/2IdR _)
    e-retr-base (zero ∷ two ∷ []) a = cong [_] (cong (baseP (0 ∷ 2 ∷ [])) (ϕ₂-retr a))
    e-retr-base (zero ∷ suc (suc (suc m)) ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
      where
      v = λ { zero → base (0 ∷ m ∷ []) (-ℤ/2 a) ; one → 0Pℤ/2 ; two → 0Pℤ/2 }
      helper : _
      helper = +Pℤ/2IdL _ ∙ sym (cong₂ _+Pℤ/2_
                                       (cong₂ baseP (cong (λ X → 0 ∷ X ∷ []) (+-comm _ _))
                                       (·ℤ/2IdR _)) (+Pℤ/2IdL _ ∙ +Pℤ/2IdL _) ∙ +Pℤ/2IdR _)
    e-retr-base (one ∷ zero ∷ []) a =
      cong [_] (cong₂ _+Pℤ/2_
                     (cong (baseP (0 ∷ 1 ∷ [])) (cong fst (ϕ₁-retr _)) ∙ base-neutral _)
                     (cong (baseP (1 ∷ 0 ∷ [])) (cong snd (ϕ₁-retr _)))
              ∙ +Pℤ/2IdL _)
    e-retr-base (one ∷ suc m ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
      where
      v = λ { zero → 0Pℤ/2 ; one → base (0 ∷ m ∷ []) (-ℤ/2 a) ; two → 0Pℤ/2 }
      helper : _
      helper = +Pℤ/2IdL _ ∙
               sym (+Pℤ/2IdL _ ∙ cong₂ _+Pℤ/2_ (cong₂ baseP (cong (λ X → 1 ∷ X ∷ []) (+-comm _ _))
                                                (·ℤ/2IdR _)) (+Pℤ/2IdR _) ∙ +Pℤ/2IdR _)
    e-retr-base (suc (suc n) ∷ m ∷ []) a = eq/ _ _ ∣ v , helper ∣₁
      where
      v = λ { zero → 0Pℤ/2 ; one → 0Pℤ/2 ; two → base (n ∷ m ∷ []) (-ℤ/2 a) }
      helper : _
      helper = +Pℤ/2IdL _ ∙ sym (+Pℤ/2IdL _ ∙ +Pℤ/2IdL _ ∙ +Pℤ/2IdR _
                                 ∙ cong₂ baseP (cong₂ (λ X Y → X ∷ Y ∷ []) (+-comm _ _) (+-comm _ _))
                                               (·ℤ/2IdR _))

    e-retr : (x : ℤ/2[x,y]/<y³,xy,x²>) → H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²> (ℤ/2[x,y]/<y³,xy,x²>→H*-RP²∨S¹ x) ≡ x
    e-retr = SQ.elimProp (λ _ → isSetPℤ/2I _ _)
             (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤ/2I _ _)
             refl
             e-retr-base
             λ {U V} ind-U ind-V → cong₂ _+Pℤ/2I_ ind-U ind-V)


  -- Computation of the Cohomology Ring

module _ where
  open Equiv-RP²∨S¹-Properties
         (invGroupIso (GroupEquiv→GroupIso H⁰[RP²∨S¹,ℤ/2]≅ℤ/2))
         (invGroupIso (GroupEquiv→GroupIso H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2))
         (invGroupIso (GroupEquiv→GroupIso H²[RP²∨S¹,ℤ/2]≅ℤ/2))
         (λ n → uncurry λ x → J (λ n _ → AbGroupIso (coHomGr n ℤ/2 RP²∨S¹) UnitAbGroup)
            (subst (λ m → AbGroupIso (coHomGr m ℤ/2 RP²∨S¹) UnitAbGroup) (+-comm 3 x)
              (GroupEquiv→GroupIso (H³⁺ⁿ[RP²∨S¹,ℤ/2]≅Unit x))))

  ϕ₁Idα : ϕ₁ (1 , 0) ≡ α
  ϕ₁Idα = cong (invEq (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2)) (sym α↦1)
        ∙ retEq (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) α

  ϕ₁Idβ : ϕ₁ (0 , 1) ≡ β
  ϕ₁Idβ = cong (invEq (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2)) (sym β↦1)
        ∙ retEq (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) β

  ϕ₁≡₁ : ϕ₁ (1 , 0) ⌣ℤ/2 ϕ₁ (0 , 1) ≡ 0ₕ 2
  ϕ₁≡₁ = cong₂ _⌣ℤ/2_ ϕ₁Idα ϕ₁Idβ
       ∙ cong ∣_∣₂ (funExt λ x → cong (EMTensorMult 2) (αβ-raw⨂ x))

  ϕ₁≡₂ : ϕ₁ (0 , 1) ⌣ℤ/2 ϕ₁ (1 , 0) ≡ 0ₕ 2
  ϕ₁≡₂ = cong₂ _⌣ℤ/2_ ϕ₁Idβ ϕ₁Idα
       ∙ cong ∣_∣₂ (funExt λ x → cong (EMTensorMult 2) (βα-raw⨂ x))

  ϕ₁≡₃ : ϕ₁ (0 , 1) ⌣ℤ/2 ϕ₁ (0 , 1) ≡ 0ₕ 2
  ϕ₁≡₃ = cong₂ _⌣ℤ/2_ ϕ₁Idβ ϕ₁Idβ
       ∙ cong ∣_∣₂ (funExt λ x → cong (EMTensorMult 2) (β²-raw⨂ x))

  ϕ₁≡₄ : ϕ₁ (1 , 0) ⌣ℤ/2 ϕ₁ (1 , 0) ≡ ϕ₂ 1
  ϕ₁≡₄ = (cong₂ _⌣ℤ/2_ ϕ₁Idα ϕ₁Idα
        ∙ cong ∣_∣₂ (funExt α²-raw))
    ∙ sym (retEq (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2) γ)
    ∙ cong (invEq (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2)) γ↦1

  open CompPoperties refl ϕ₁≡₄ ϕ₁≡₃ ϕ₁≡₁ ϕ₁≡₂

  RP²∨S¹-CohomologyRing : RingEquiv (CommRing→Ring ℤ/2[X,Y]/<Y³,XY,X²>) (H*R ℤ/2Ring RP²∨S¹)
  fst RP²∨S¹-CohomologyRing = isoToEquiv is
    where
    is : Iso _ _
    fun is = ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹ .fst
    inv is = H*-RP²∨S¹→ℤ/2[x,y]/<y³,xy,x²>
    rightInv is = e-sect
    leftInv is = e-retr
  snd RP²∨S¹-CohomologyRing = ℤ/2[X,Y]/<Y³,XY,X²>→H*R-RP²∨S¹ .snd

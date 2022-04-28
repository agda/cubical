{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv-PolynQuotient-A where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Empty renaming (rec to rec-⊥ ; elim to elim-⊥)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient

open import Cubical.Relation.Nullary

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetQuotients renaming (elimProp to elimProp-sq ; rec to rec-sq ; _/_ to _/sq_)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- Functions

module Properties-Equiv-QuotientXn-A
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  open CommRingStr Astr using ()
    renaming
    ( 0r        to 0A
    ; 1r        to 1A
    ; _+_       to _+A_
    ; -_        to -A_
    ; _·_       to _·A_
    ; +Assoc    to +AAssoc
    ; +Identity to +AIdentity
    ; +Lid      to +ALid
    ; +Rid      to +ARid
    ; +Inv      to +AInv
    ; +Linv     to +ALinv
    ; +Rinv     to +ARinv
    ; +Comm     to +AComm
    ; ·Assoc    to ·AAssoc
    ; ·Identity to ·AIdentity
    ; ·Lid      to ·ALid
    ; ·Rid      to ·ARid
    ; ·Rdist+   to ·ARdist+
    ; ·Ldist+   to ·ALdist+
    ; is-set    to isSetA     )

  open CommRingStr (snd (A[X1,···,Xn] Ar n) ) using ()
    renaming
    ( 0r        to 0PA
    ; 1r        to 1PA
    ; _+_       to _+PA_
    ; -_        to -PA_
    ; _·_       to _·PA_
    ; +Assoc    to +PAAssoc
    ; +Identity to +PAIdentity
    ; +Lid      to +PALid
    ; +Rid      to +PARid
    ; +Inv      to +PAInv
    ; +Linv     to +PALinv
    ; +Rinv     to +PARinv
    ; +Comm     to +PAComm
    ; ·Assoc    to ·PAAssoc
    ; ·Identity to ·PAIdentity
    ; ·Lid      to ·PALid
    ; ·Rid      to ·PARid
    ; ·Comm     to ·PAComm
    ; ·Rdist+   to ·PARdist+
    ; ·Ldist+   to ·PALdist+
    ; is-set    to isSetPA     )

  open CommRingStr (snd (A[X1,···,Xn]/<X1,···,Xn> Ar n)) using ()
    renaming
    ( 0r        to 0PAI
    ; 1r        to 1PAI
    ; _+_       to _+PAI_
    ; -_        to -PAI_
    ; _·_       to _·PAI_
    ; +Assoc    to +PAIAssoc
    ; +Identity to +PAIIdentity
    ; +Lid      to +PAILid
    ; +Rid      to +PAIRid
    ; +Inv      to +PAIInv
    ; +Linv     to +PAILinv
    ; +Rinv     to +PAIRinv
    ; +Comm     to +PAIComm
    ; ·Assoc    to ·PAIAssoc
    ; ·Identity to ·PAIIdentity
    ; ·Lid      to ·PAILid
    ; ·Rid      to ·PAIRid
    ; ·Rdist+   to ·PAIRdist+
    ; ·Ldist+   to ·PAILdist+
    ; is-set    to isSetPAI     )

  open RingTheory

  discreteVecℕn = VecPath.discreteA→discreteVecA discreteℕ n


-----------------------------------------------------------------------------
-- Direct sens
  A→PA : A → A[x1,···,xn] Ar n
  A→PA a = (base (replicate 0) a)

  A→PA-map1 : A→PA 1A ≡ 1PA
  A→PA-map1 = refl

  A→PA-map+ : (a a' : A) → A→PA (a +A a') ≡ (A→PA a) +PA (A→PA a')
  A→PA-map+ a a' = sym (base-Poly+ _ _ _)

  A→PA-map· : (a a' : A) → A→PA (a ·A a') ≡ (A→PA a) ·PA (A→PA a')
  A→PA-map· a a' = cong (λ X → base X (a ·A a')) (sym (+n-vec-rid _))

-----------------------------------------------------------------------------
-- Converse sens
  PA→A : A[x1,···,xn] Ar n → A
  PA→A = Poly-Rec-Set.f Ar n _ isSetA
          0A
          base-trad
          _+A_
          +AAssoc
          +ARid
          +AComm
          base-0P-eq
          base-Poly+-eq
        where
        base-trad : (v : Vec ℕ n) → (a : A) → A
        base-trad v a with (discreteVecℕn v (replicate 0))
        ... | yes p = a
        ... | no ¬p = 0A

        base-0P-eq : (v : Vec ℕ n) → base-trad v 0A ≡ 0A
        base-0P-eq v with (discreteVecℕn v (replicate 0))
        ... | yes p = refl
        ... | no ¬p = refl

        base-Poly+-eq : (v : Vec ℕ n) → (a b : A) → base-trad v a +A base-trad v b ≡ base-trad v (a +A b)
        base-Poly+-eq v a b with (discreteVecℕn v (replicate 0))
        ... | yes p = refl
        ... | no ¬p = +ARid _

  PA→A-map1 :  PA→A 1PA ≡ 1A
  PA→A-map1 with (discreteVecℕn (replicate 0) (replicate 0))
  ... | yes p = refl
  ... | no ¬p = rec-⊥ (¬p refl)

  PA→A-map+ : (P Q : A[x1,···,xn] Ar n) → PA→A (P +PA Q) ≡ PA→A P +A PA→A Q
  PA→A-map+ P Q = refl

  PA→A-map· : (P Q : A[x1,···,xn] Ar n) → PA→A (P ·PA Q) ≡ PA→A P ·A PA→A Q
  PA→A-map· = Poly-Ind-Prop.f _ _ _
               (λ P u v i Q → isSetA _ _ (u Q) (v Q) i)
               (λ Q → sym (0LeftAnnihilates (CommRing→Ring Ar) _))
               (λ v a → Poly-Ind-Prop.f _ _ _ (λ Q → isSetA _ _)
                         (sym (0RightAnnihilates (CommRing→Ring Ar) _))
                         (λ v' a' → base-base-eq a a' v v')
                         λ {U V} ind-U ind-V → cong₂ _+A_ ind-U ind-V ∙ sym (·ARdist+ _ _ _))
               λ {U V} ind-U ind-V Q → cong₂ _+A_ (ind-U Q) (ind-V Q) ∙ sym (·ALdist+ _ _ _)
               where
               base-base-eq : (a a' : A) → (v v' : Vec ℕ n) →
                              PA→A (base v a ·PA base v' a') ≡ PA→A (base v a) ·A PA→A (base v' a')
               base-base-eq a a' v v' with (discreteVecℕn (v +n-vec v') (replicate 0))
                                           | (discreteVecℕn v (replicate 0))
                                           | (discreteVecℕn v' (replicate 0))
               ... | yes r | yes p | yes e = refl
               ... | yes r | yes p | no ¬q = rec-⊥ (¬q (snd (v+n-vecv'≡0→v≡0×v'≡0 v v' r)))
               ... | yes r | no ¬p | q     = rec-⊥ (¬p (fst (v+n-vecv'≡0→v≡0×v'≡0 v v' r)))
               ... | no ¬r | yes p | yes q = rec-⊥ (¬r (cong₂ _+n-vec_ p q ∙ +n-vec-rid _))
               ... | no ¬r | yes p | no ¬q = sym (0RightAnnihilates (CommRing→Ring Ar) _)
               ... | no ¬r | no ¬p | yes q = sym (0LeftAnnihilates (CommRing→Ring Ar) _)
               ... | no ¬r | no ¬p | no ¬q = sym (0RightAnnihilates (CommRing→Ring Ar) _)

  -- PA→A-cancel : (k : Fin n) → PA→A (<X1,···,Xn> Ar n k) ≡ 0A
  -- PA→A-cancel k with (discreteVecℕn (OnekZeroElse n (toℕ k)) (replicate 0))
  -- ... | yes p = {!!} -- so annoying
  -- ... | no ¬p = refl

  -- ℤ[x]→H*-Sⁿ-cancelX : (k : Fin 1) → ℤ[x]→H*-Sⁿ (<X²> k) ≡ 0H*
  -- ℤ[x]→H*-Sⁿ-cancelX zero = refl

  -- ℤ[X]→H*-Sⁿ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ (suc n)))
  -- fst ℤ[X]→H*-Sⁿ = ℤ[x]→H*-Sⁿ
  -- snd ℤ[X]→H*-Sⁿ = makeIsRingHom ℤ[x]→H*-Sⁿ-map1 ℤ[x]→H*-Sⁿ-map+ ℤ[x]→H*-Sⁿ-rmorph

  -- ℤ[X]/X²→H*R-Sⁿ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ (suc n)))
  -- ℤ[X]/X²→H*R-Sⁿ = Rec-Quotient-FGIdeal-Ring.f ℤ[X] (H*R (S₊ (suc n))) ℤ[X]→H*-Sⁿ <X²> ℤ[x]→H*-Sⁿ-cancelX

  -- ℤ[x]/x²→H*-Sⁿ : ℤ[x]/x² → H* (S₊ (suc n))
  -- ℤ[x]/x²→H*-Sⁿ = fst ℤ[X]/X²→H*R-Sⁿ

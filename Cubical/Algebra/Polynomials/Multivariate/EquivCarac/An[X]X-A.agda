{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[X]X-A where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient


open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
     renaming (PolyCommRing to A[X1,···,Xn] ; Poly to A[x1,···,xn])
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient

open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

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
    ; +IdL      to +AIdL
    ; +IdR      to +AIdR
    ; +InvL     to +AInvL
    ; +InvR     to +AInvR
    ; +Comm     to +AComm
    ; ·Assoc    to ·AAssoc
    ; ·IdL      to ·AIdL
    ; ·IdR      to ·AIdR
    ; ·DistR+   to ·ADistR+
    ; ·DistL+   to ·ADistL+
    ; is-set    to isSetA     )

  open CommRingStr (snd (A[X1,···,Xn] Ar n) ) using ()
    renaming
    ( 0r        to 0PA
    ; 1r        to 1PA
    ; _+_       to _+PA_
    ; -_        to -PA_
    ; _·_       to _·PA_
    ; +Assoc    to +PAAssoc
    ; +IdL      to +PAIdL
    ; +IdR      to +PAIdR
    ; +InvL     to +PAInvL
    ; +InvR     to +PAInvR
    ; +Comm     to +PAComm
    ; ·Assoc    to ·PAAssoc
    ; ·IdL      to ·PAIdL
    ; ·IdR      to ·PAIdR
    ; ·Comm     to ·PAComm
    ; ·DistR+   to ·PADistR+
    ; ·DistL+   to ·PADistL+
    ; is-set    to isSetPA     )

  open CommRingStr (snd (A[X1,···,Xn]/<X1,···,Xn> Ar n)) using ()
    renaming
    ( 0r        to 0PAI
    ; 1r        to 1PAI
    ; _+_       to _+PAI_
    ; -_        to -PAI_
    ; _·_       to _·PAI_
    ; +Assoc    to +PAIAssoc
    ; +IdL      to +PAIIdL
    ; +IdR      to +PAIIdR
    ; +InvL     to +PAIInvL
    ; +InvR     to +PAIInvR
    ; +Comm     to +PAIComm
    ; ·Assoc    to ·PAIAssoc
    ; ·IdL      to ·PAIIdL
    ; ·IdR      to ·PAIIdR
    ; ·DistR+   to ·PAIDistR+
    ; ·DistL+   to ·PAIDistL+
    ; is-set    to isSetPAI     )

  open RingTheory

  discreteVecℕn = VecPath.discreteA→discreteVecA discreteℕ n



-----------------------------------------------------------------------------
-- Direct sens

  PA→A : A[x1,···,xn] Ar n → A
  PA→A = DS-Rec-Set.f _ _ _ _ isSetA
          0A
          base-trad
          _+A_
          +AAssoc
          +AIdR
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
        ... | no ¬p = +AIdR _

  PA→A-pres1 :  PA→A 1PA ≡ 1A
  PA→A-pres1 with (discreteVecℕn (replicate 0) (replicate 0))
  ... | yes p = refl
  ... | no ¬p = ⊥.rec (¬p refl)

  PA→A-pres+ : (P Q : A[x1,···,xn] Ar n) → PA→A (P +PA Q) ≡ PA→A P +A PA→A Q
  PA→A-pres+ P Q = refl

  PA→A-pres· : (P Q : A[x1,···,xn] Ar n) → PA→A (P ·PA Q) ≡ PA→A P ·A PA→A Q
  PA→A-pres· = DS-Ind-Prop.f _ _ _ _
               (λ P u v i Q → isSetA _ _ (u Q) (v Q) i)
               (λ Q → sym (0LeftAnnihilates (CommRing→Ring Ar) _))
               (λ v a → DS-Ind-Prop.f _ _ _ _ (λ Q → isSetA _ _)
                         (sym (0RightAnnihilates (CommRing→Ring Ar) _))
                         (λ v' a' → base-base-eq a a' v v')
                         λ {U V} ind-U ind-V → cong₂ _+A_ ind-U ind-V ∙ sym (·ADistR+ _ _ _))
               λ {U V} ind-U ind-V Q → cong₂ _+A_ (ind-U Q) (ind-V Q) ∙ sym (·ADistL+ _ _ _)
               where
               base-base-eq : (a a' : A) → (v v' : Vec ℕ n) →
                              PA→A (base v a ·PA base v' a') ≡ PA→A (base v a) ·A PA→A (base v' a')
               base-base-eq a a' v v' with (discreteVecℕn (v +n-vec v') (replicate 0))
                                           | (discreteVecℕn v (replicate 0))
                                           | (discreteVecℕn v' (replicate 0))
               ... | yes r | yes p | yes e = refl
               ... | yes r | yes p | no ¬q = ⊥.rec (¬q (snd (+n-vecSplitReplicate0 v v' r)))
               ... | yes r | no ¬p | q     = ⊥.rec (¬p (fst (+n-vecSplitReplicate0 v v' r)))
               ... | no ¬r | yes p | yes q = ⊥.rec (¬r (cong₂ _+n-vec_ p q ∙ +n-vec-rid _))
               ... | no ¬r | yes p | no ¬q = sym (0RightAnnihilates (CommRing→Ring Ar) _)
               ... | no ¬r | no ¬p | yes q = sym (0LeftAnnihilates (CommRing→Ring Ar) _)
               ... | no ¬r | no ¬p | no ¬q = sym (0RightAnnihilates (CommRing→Ring Ar) _)

  PA→A-cancel : (k : Fin n) → PA→A (<X1,···,Xn> Ar n k) ≡ 0A
  PA→A-cancel k with (discreteVecℕn (δℕ-Vec n (toℕ k)) (replicate 0))
  ... | yes p = ⊥.rec (δℕ-Vec-k<n→≢ n (toℕ k) (toℕ<n k) p)
  ... | no ¬p = refl

  PAr→Ar : CommRingHom (A[X1,···,Xn] Ar n) Ar
  fst PAr→Ar = PA→A
  snd PAr→Ar = makeIsRingHom PA→A-pres1 PA→A-pres+ PA→A-pres·

  PAIr→Ar : CommRingHom (A[X1,···,Xn]/<X1,···,Xn> Ar n) Ar
  PAIr→Ar = Quotient-FGideal-CommRing-CommRing.inducedHom (A[X1,···,Xn] Ar n) Ar PAr→Ar (<X1,···,Xn> Ar n) PA→A-cancel

  PAI→A : A[x1,···,xn]/<x1,···,xn> Ar n → A
  PAI→A = fst PAIr→Ar



-----------------------------------------------------------------------------
-- Converse sens

  A→PA : A → A[x1,···,xn] Ar n
  A→PA a = (base (replicate 0) a)

  A→PA-pres1 : A→PA 1A ≡ 1PA
  A→PA-pres1 = refl

  A→PA-pres+ : (a a' : A) → A→PA (a +A a') ≡ (A→PA a) +PA (A→PA a')
  A→PA-pres+ a a' = sym (base-add _ _ _)

  A→PA-pres· : (a a' : A) → A→PA (a ·A a') ≡ (A→PA a) ·PA (A→PA a')
  A→PA-pres· a a' = cong (λ X → base X (a ·A a')) (sym (+n-vec-rid _))

  A→PAI : A → (A[x1,···,xn]/<x1,···,xn> Ar n)
  A→PAI = [_] ∘ A→PA



-----------------------------------------------------------------------------
-- Section

  e-sect : (a : A) → PAI→A (A→PAI a) ≡ a
  e-sect a with (discreteVecℕn (replicate 0) (replicate 0))
  ... | yes p = refl
  ... | no ¬p = ⊥.rec (¬p refl)



-----------------------------------------------------------------------------
-- Retraction

  open RingStr
  open IsRing

  e-retr : (x : A[x1,···,xn]/<x1,···,xn> Ar n) → A→PAI (PAI→A x) ≡ x
  e-retr = SQ.elimProp (λ _ → isSetPAI _ _)
           (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPAI _ _)
           base0-eq
           base-eq
           λ {U V} ind-U ind-V → cong [_] (A→PA-pres+ _ _) ∙ cong₂ _+PAI_ ind-U ind-V)
           where
           base0-eq : A→PAI (PAI→A [ 0PA ]) ≡ [ 0PA ]
           base0-eq = cong [_] (base-neutral (replicate 0))

           base-eq : (v : Vec ℕ n) → (a : A ) → [ A→PA (PA→A (base v a)) ] ≡ [ base v a ]
           base-eq v a with (discreteVecℕn v (replicate 0))
           ... | yes p = cong [_] (cong (λ X → base X a) (sym p))
           ... | no ¬p with (pred-vec-≢0 v ¬p)
           ... | k , v' , infkn , eqvv' = eq/ (base (replicate 0) 0A)
                                             (base v a) ∣ ((genδ-FinVec n k (base v' (-A a)) 0PA) , helper) ∣₁
               where
               helper : _
               helper = cong (λ X → X +PA base v (-A a)) (base-neutral (replicate 0))
                        ∙ +PAIdL (base v (-A a))
                        ∙ sym (
                          genδ-FinVec-ℕLinearCombi ((A[X1,···,Xn] Ar n)) n k infkn (base v' (-A a)) (<X1,···,Xn> Ar n)
                          ∙ cong₂ base (cong (λ X → v' +n-vec δℕ-Vec n X) (toFromId' n k infkn)) (·AIdR _)
                          ∙ cong (λ X → base X (-A a)) (sym eqvv'))



-----------------------------------------------------------------------------
-- Equiv

module _
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  open Iso
  open Properties-Equiv-QuotientXn-A Ar n

  Equiv-QuotientX-A : CommRingEquiv (A[X1,···,Xn]/<X1,···,Xn> Ar n) Ar
  fst Equiv-QuotientX-A = isoToEquiv is
    where
    is : Iso (A[x1,···,xn]/<x1,···,xn> Ar n) A
    fun is = PAI→A
    inv is = A→PAI
    rightInv is = e-sect
    leftInv is = e-retr
  snd Equiv-QuotientX-A = snd PAIr→Ar

-- Warning this doesn't prove Z[X]/X ≅ ℤ because you get two definition,
-- see notation Multivariate-Quotient-notationZ for more details

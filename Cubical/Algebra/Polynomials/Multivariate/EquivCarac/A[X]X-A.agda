{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.A[X]X-A where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient

open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly
     renaming (PolyCommRing to A[X1,···,Xn] ; Poly to A[x1,···,xn])
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-notationZ

open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- Functions


module Properties-Equiv-QuotientXn-A
  (Ar@(A , Astr) : CommRing ℓ)
  where

  private
    A[X] : CommRing ℓ
    A[X] = A[X1,···,Xn] Ar 1

    A[x] : Type ℓ
    A[x] = A[x1,···,xn] Ar 1

    A[X]/X : CommRing ℓ
    A[X]/X = A[X1,···,Xn]/<Xkʲ> Ar 1 0 1

    A[x]/x : Type ℓ
    A[x]/x = A[x1,···,xn]/<xkʲ> Ar 1 0 1

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

  open CommRingStr (snd A[X] ) using ()
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

  open CommRingStr (snd A[X]/X) using ()
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


-----------------------------------------------------------------------------
-- Direct sens

  A[x]→A : A[x] → A
  A[x]→A = DS-Rec-Set.f _ _ _ _ isSetA
          0A
          base-trad
          _+A_
          +AAssoc
          +AIdR
          +AComm
          base-neutral-eq
          base-add-eq

       where
       base-trad : _
       base-trad (zero ∷ []) a = a
       base-trad (suc k ∷ []) a = 0A

       base-neutral-eq : _
       base-neutral-eq (zero ∷ []) = refl
       base-neutral-eq (suc k ∷ []) = refl

       base-add-eq : _
       base-add-eq (zero ∷ []) a b = refl
       base-add-eq (suc k ∷ []) a b = +AIdR _

  A[x]→A-pres1 : A[x]→A 1PA ≡ 1A
  A[x]→A-pres1 = refl

  A[x]→A-pres+ : (x y : A[x]) → (A[x]→A (x +PA y)) ≡ A[x]→A x +A A[x]→A y
  A[x]→A-pres+ x y = refl

  A[x]→A-pres· : (x y : A[x]) → (A[x]→A (x ·PA y)) ≡ A[x]→A x ·A A[x]→A y
  A[x]→A-pres· = DS-Ind-Prop.f _ _ _ _
               (λ x u v i y → isSetA _ _ (u y) (v y) i)
               (λ y → sym (0LeftAnnihilates (CommRing→Ring Ar) _))
               (λ v a → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetA _ _)
                         (sym (0RightAnnihilates (CommRing→Ring Ar) _))
                         (λ v' a' → base-eq a a' v v')
                         (λ {U V} ind-U ind-V → cong₂ _+A_ ind-U ind-V ∙ sym (·ADistR+ _ _ _)))
               λ {U V} ind-U ind-V y → cong₂ _+A_ (ind-U y) (ind-V y) ∙ sym (·ADistL+ _ _ _)
            where
            base-eq : (a a' : A) → (v v' : Vec ℕ 1) → (A[x]→A (base v a ·PA base v' a')) ≡ A[x]→A (base v a) ·A A[x]→A (base v' a')
            base-eq a a' (zero ∷ []) (zero ∷ []) = refl
            base-eq a a' (zero ∷ []) (suc k' ∷ []) = sym (0RightAnnihilates (CommRing→Ring Ar) _)
            base-eq a a' (suc k ∷ []) (k' ∷ []) = sym (0LeftAnnihilates (CommRing→Ring Ar) _)

  A[X]→A : CommRingHom A[X] Ar
  fst A[X]→A = A[x]→A
  snd A[X]→A = makeIsCommRingHom A[x]→A-pres1 A[x]→A-pres+ A[x]→A-pres·

  A[x]→A-cancel : (k : Fin 1) → A[x]→A (<Xkʲ> Ar 1 0 1 k) ≡ 0A
  A[x]→A-cancel zero = refl

  A[X]/X→A : CommRingHom A[X]/X Ar
  A[X]/X→A = Quotient-FGideal-CommRing-CommRing.inducedHom A[X] Ar A[X]→A (<Xkʲ> Ar 1 0 1) A[x]→A-cancel

  A[x]/x→A : A[x]/x → A
  A[x]/x→A = fst A[X]/X→A



-----------------------------------------------------------------------------
-- Converse sens

  A→A[x] : A → A[x]
  A→A[x] a = base (0 ∷ []) a

  A→A[x]-pres+ : (a a' : A) → A→A[x] (a +A a') ≡ A→A[x] a +PA A→A[x] a'
  A→A[x]-pres+ a a' = sym (base-add (0 ∷ []) a a')

  A→A[x]/x : A → A[x]/x
  A→A[x]/x = [_] ∘ A→A[x]

  A→A[x]/x-pres+ : (a a' : A) → A→A[x]/x (a +A a') ≡ A→A[x]/x a +PAI A→A[x]/x a'
  A→A[x]/x-pres+ a a' = cong [_] (A→A[x]-pres+ a a')


-----------------------------------------------------------------------------
-- Section sens

  e-sect : (a : A) → A[x]→A (A→A[x] a) ≡ a
  e-sect a = refl


-----------------------------------------------------------------------------
-- Retraction sens

  open IsRing

  e-retr : (x : A[x]/x) → A→A[x]/x (A[x]/x→A x) ≡ x
  e-retr = SQ.elimProp (λ x → isSetPAI _ _)
           (DS-Ind-Prop.f _ _ _ _ (λ x → isSetPAI _ _)
           (cong [_] (base-neutral _))
           (λ v a → base-eq a v)
           λ {U V} ind-U ind-V → cong [_] ((A→A[x]-pres+ _ _)) ∙ cong₂ _+PAI_ ind-U ind-V)

         where
         base-eq : (a : A) → (v : Vec ℕ 1) → A→A[x]/x (A[x]/x→A [ (base v a) ]) ≡ [ (base v a) ]
         base-eq a (zero ∷ []) = cong [_] refl
         base-eq a (suc k ∷ []) = eq/ (base (0 ∷ []) 0A) (base (suc k ∷ []) a) ∣ ((λ x → base (k ∷ []) (-A a)) , helper) ∣₁
           where
           helper : _
           helper = cong (λ X → X +PA base (suc k ∷ []) (-A a)) (base-neutral _)
                     ∙ +PAIdL _
                     ∙ sym (+PAIdR _
                            ∙ cong₂ base
                                    (cong (λ X → X ∷ []) (+-suc _ _ ∙ +-zero _))
                                    (·AIdR _))


module _
  (Ar@(A , Astr) : CommRing ℓ)
  where

  open Iso
  open Properties-Equiv-QuotientXn-A Ar

  Equiv-A[X]/X-A : CommRingEquiv (A[X1,···,Xn]/<Xkʲ> Ar 1 0 1) Ar
  fst Equiv-A[X]/X-A = isoToEquiv is
    where
    is : Iso (A[x1,···,xn]/<xkʲ> Ar 1 0 1) A
    fun is = A[x]/x→A
    inv is = A→A[x]/x
    rightInv is = e-sect
    leftInv is = e-retr
  snd Equiv-A[X]/X-A = snd A[X]/X→A

Equiv-ℤ[X]/X-ℤ : RingEquiv (CommRing→Ring ℤ[X]/X) (CommRing→Ring ℤCR)
Equiv-ℤ[X]/X-ℤ = CommRingEquiv→RingEquiv $ Equiv-A[X]/X-A ℤCR

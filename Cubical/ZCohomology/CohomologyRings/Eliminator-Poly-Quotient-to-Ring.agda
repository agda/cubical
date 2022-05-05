{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Eliminator-Poly-Quotient-to-Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.FGIdeal

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/sq_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.HITs.PropositionalTruncation as PT

private variable
  ℓ ℓ' : Level


-----------------------------------------------------------------------------

module Rec-Quotient-FGIdeal-Ring
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : Ring ℓ)
  (g'@(g , gr) : RingHom (CommRing→Ring A') B')
  where

  open CommRingStr (snd A')
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

  open RingStr (snd B')

    renaming
    ( 0r        to 0B
    ; 1r        to 1B
    ; _+_       to _+B_
    ; -_        to -B_
    ; _·_       to _·B_
    ; +Assoc    to +BAssoc
    ; +Identity to +BIdentity
    ; +Lid      to +BLid
    ; +Rid      to +BRid
    ; +Inv      to +BInv
    ; +Linv     to +BLinv
    ; +Rinv     to +BRinv
    ; +Comm     to +BComm
    ; ·Assoc    to ·BAssoc
    ; ·Identity to ·BIdentity
    ; ·Lid      to ·BLid
    ; ·Rid      to ·BRid
    ; ·Rdist+   to ·BRdist+
    ; ·Ldist+   to ·BLdist+
    ; is-set    to isSetB     )


  open IsRingHom

  cancel-linear-combi-ring : (n : ℕ) → (a v : FinVec A n) → (gnull : (k : Fin n) → g (v k) ≡ 0B)
                        → g (linearCombination A' a v) ≡ 0B
  cancel-linear-combi-ring zero a v gnull = pres0 gr
  cancel-linear-combi-ring (suc n) a v gnull = g ((a zero ·A v zero) +A rec-call)
                                                ≡⟨ pres+ gr _ _ ⟩
                                          ((g (a zero ·A v zero)) +B (g rec-call))
                                                ≡⟨ cong₂ _+B_ (pres· gr _ _) (cancel-linear-combi-ring n (a ∘ suc) (v ∘ suc) (gnull ∘ suc)) ⟩
                                          (g (a zero) ·B g (v zero) +B 0B)
                                               ≡⟨ +BRid _ ⟩
                                          (g (a zero) ·B g (v zero))
                                               ≡⟨ cong (λ X → (g (a zero)) ·B X) (gnull zero) ⟩
                                          (g (a zero) ·B 0B) ≡⟨ RingTheory.0RightAnnihilates B' _ ⟩
                                          0B ∎

    where
    rec-call = foldrFin _+A_ 0A (λ x → a (suc x) ·A v (suc x))


  module _
    {n : ℕ}
    (v : FinVec A n)
    (gnull : (k : Fin n) → g ( v k) ≡ 0B)
    where

    f : RingHom (CommRing→Ring (A' / (generatedIdeal _ v))) B'
    fst f = SQ.rec isSetB
            g
            λ a b → PT.rec (isSetB _ _)
                     λ x → g a                                   ≡⟨ cong g (sym (+ARid a)) ⟩
                     g (a +A 0A)                                  ≡⟨ cong (λ X → g (a +A X)) (sym (snd (+AInv b))) ⟩
                     g (a +A ((-A b) +A b))                       ≡⟨ cong g (+AAssoc a (-A b) b) ⟩
                     g ((a +A -A b) +A b)                         ≡⟨ pres+ gr (a +A -A b) b ⟩
                     (g(a +A -A b) +B g b)                        ≡⟨ cong (λ X → g X +B g b) (snd x) ⟩
                     (g (linearCombination A' (fst x) v) +B g b)  ≡⟨ cong (λ X → X +B g b) (cancel-linear-combi-ring n (fst x) v gnull) ⟩
                     0B +B g b                                    ≡⟨ +BLid (g b) ⟩
                     g b ∎
    snd f = makeIsRingHom
            (pres1 gr)
            (elimProp (λ x p q i y j → isSetB _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → isSetB _ _)
                             λ a' → pres+ gr a a')
            (elimProp (λ x p q i y j → isSetB _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → isSetB _ _)
                             λ a' → pres· gr a a')

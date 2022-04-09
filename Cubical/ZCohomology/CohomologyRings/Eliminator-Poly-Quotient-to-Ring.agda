{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Eliminator-Poly-Quotient-to-Ring where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.FGIdeal

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/sq_)
open import Cubical.HITs.SetQuotients.Properties renaming (rec to rec-sq)
open import Cubical.HITs.PropositionalTruncation renaming (rec to rec-prop)

private variable
  ℓ ℓ' : Level


-----------------------------------------------------------------------------

module Rec-Quotient-FGIdeal-Ring
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : Ring ℓ)
  (f'@(f , fr) : RingHom (CommRing→Ring A') B')
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

  cancel-linear-combi'' : (n : ℕ) → (a v : FinVec A n) → (fnull : (k : Fin n) → f (v k) ≡ 0B)
                        → f (linearCombination A' a v) ≡ 0B
  cancel-linear-combi'' zero a v fnull = pres0 fr
  cancel-linear-combi'' (suc n) a v fnull = f ((a zero ·A v zero) +A rec-call)
                                                ≡⟨ pres+ fr _ _ ⟩
                                          ((f (a zero ·A v zero)) +B (f rec-call))
                                                ≡⟨ cong₂ _+B_ (pres· fr _ _) (cancel-linear-combi'' n (a ∘ suc) (v ∘ suc) (fnull ∘ suc)) ⟩
                                          (f (a zero) ·B f (v zero) +B 0B)
                                               ≡⟨ +BRid _ ⟩
                                          (f (a zero) ·B f (v zero))
                                               ≡⟨ cong (λ X → (f (a zero)) ·B X) (fnull zero) ⟩
                                          (f (a zero) ·B 0B) ≡⟨ RingTheory.0RightAnnihilates B' _ ⟩
                                          0B ∎

    where
    rec-call = foldrFin _+A_ 0A (λ x → a (suc x) ·A v (suc x))


  module _
    {n : ℕ}
    (v : FinVec A n)
    (fnull : (k : Fin n) → f ( v k) ≡ 0B)
    where

    g : RingHom (CommRing→Ring (A' / (generatedIdeal _ v))) B'
    fst g = rec-sq isSetB
            f
            λ a b → rec-prop (isSetB _ _)
                     λ x → f a                                   ≡⟨ cong f (sym (+ARid a)) ⟩
                     f (a +A 0A)                                  ≡⟨ cong (λ X → f (a +A X)) (sym (snd (+AInv b))) ⟩
                     f (a +A ((-A b) +A b))                       ≡⟨ cong f (+AAssoc a (-A b) b) ⟩
                     f ((a +A -A b) +A b)                         ≡⟨ pres+ fr (a +A -A b) b ⟩
                     (f(a +A -A b) +B f b)                        ≡⟨ cong (λ X → f X +B f b) (snd x) ⟩
                     (f (linearCombination A' (fst x) v) +B f b)  ≡⟨ cong (λ X → X +B f b) (cancel-linear-combi'' n (fst x) v fnull) ⟩
                     0B +B f b                                    ≡⟨ +BLid (f b) ⟩
                     f b ∎
    snd g = makeIsRingHom
            (pres1 fr)
            (elimProp (λ x p q i y j → isSetB _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → isSetB _ _)
                             λ a' → pres+ fr a a')
            (elimProp (λ x p q i y j → isSetB _ _ (p y) (q y) i j)
                      λ a → elimProp (λ _ → isSetB _ _)
                             λ a' → pres· fr a a')

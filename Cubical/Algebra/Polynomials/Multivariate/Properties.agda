{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Multivariate.Base


private variable
  ℓ ℓ' : Level

module Nth-Poly-structure (A' : CommRing ℓ) (n : ℕ) where

  private
    A = fst A'
    Ar = CommRing→Ring A'

  open CommRingStr (snd A')
  open RingTheory Ar

-----------------------------------------------------------------------------

  poly-com-adv : (P Q R S : Poly A' n) →  ((P poly+ Q) poly+ (R poly+ S) ≡ (P poly+ R) poly+ (Q poly+ S))
  poly-com-adv P Q R S = ((P poly+ Q) poly+ (R poly+ S)  ≡⟨ poly+Assoc (P poly+ Q) R S ⟩
                         (((P poly+ Q) poly+ R) poly+ S) ≡⟨ cong (λ X → X poly+ S) (sym (poly+Assoc P Q R)) ⟩
                         ((P poly+ (Q poly+ R)) poly+ S) ≡⟨ cong (λ X → (P poly+ X) poly+ S) (poly+Comm Q R) ⟩
                         ((P poly+ (R poly+ Q)) poly+ S) ≡⟨ cong (λ X → X poly+ S) (poly+Assoc P R Q) ⟩
                         (((P poly+ R) poly+ Q) poly+ S) ≡⟨ sym (poly+Assoc (P poly+ R) Q S) ⟩
                         ((P poly+ R) poly+ (Q poly+ S)) ∎)


  poly+IdL : (P : Poly A' n) → 0P poly+ P ≡ P
  poly+IdL P = (poly+Comm 0P P) ∙ (poly+IdR P)


  polyInv : Poly A' n → Poly A' n
  polyInv = Poly-Rec-Set.f A' n (Poly A' n) trunc
            0P
            (λ v a → base v (- a))
            (λ PS RS → PS poly+ RS)
            poly+Assoc
            poly+IdR
            poly+Comm
            (λ v → base v (- 0r) ≡⟨ cong (base v) 0Selfinverse ⟩ base v 0r ≡⟨ base-0P v ⟩ 0P ∎)
            λ v a b → (base-poly+ v (- a) (- b)) ∙ (cong (base v) (-Dist a b))


  polyInvol : (P : Poly A' n) → polyInv (polyInv P) ≡ P
  polyInvol = Poly-Ind-Prop.f A' n (λ P → polyInv (polyInv P) ≡ P) (λ _ → trunc _ _)
              refl
              (λ v a → cong (base v) (-Idempotent a))
              λ {P Q} ind-P ind-Q → cong₂ _poly+_ ind-P ind-Q


  poly+InvR : (P : Poly A' n ) → P poly+ (polyInv P) ≡ 0P
  poly+InvR = Poly-Ind-Prop.f A' n (λ P → (P poly+ polyInv P) ≡ 0P) (λ _ → trunc _ _)
              (poly+IdR 0P)
              (λ v a → (base-poly+ v a (- a)) ∙ cong (base v) (+Rinv a) ∙ base-0P v)
              λ {P Q} ind-P ind-Q → ((P poly+ Q) poly+ ((polyInv P) poly+ (polyInv Q)))
                                              ≡⟨ poly-com-adv P Q (polyInv P) (polyInv Q) ⟩
                                     ((P poly+ polyInv P) poly+ (Q poly+ polyInv Q))
                                              ≡⟨ cong₂ _poly+_ ind-P ind-Q ⟩
                                     (0P poly+ 0P)
                                              ≡⟨ poly+IdR 0P ⟩
                                     0P ∎

  poly+InvL : (P  : Poly A' n) → (polyInv P) poly+ P ≡ 0P
  poly+InvL = Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
              (poly+IdR 0P)
              (λ v a → (base-poly+ v (- a) a) ∙ cong (base v) (snd (+Inv a)) ∙ base-0P v)
              λ {U V} ind-U ind-V → poly-com-adv (polyInv U) (polyInv V) U V
                                     ∙ cong₂ _poly+_ ind-U ind-V
                                     ∙ poly+IdR 0P


-----------------------------------------------------------------------------

  _poly*_ : Poly A' n → Poly A' n → Poly A' n
  _poly*_ = -- Induction Left Argument
            Poly-Rec-Set.f A' n (Poly A' n → Poly A' n)
            (λ f g p q i j Q → trunc (f Q) (g Q) (λ X → p X Q) (λ X → q X Q) i j )
            (λ Q    → 0P)
            (λ v a  → -- Induction Right Argument
                       Poly-Rec-Set.f A' n (Poly A' n) trunc
                       0P
                       (λ v' a' → base (v +n-vec v') (a · a'))
                       _poly+_
                       poly+Assoc
                       poly+IdR
                       poly+Comm
                       (λ v' → (cong (base (v +n-vec v')) (0RightAnnihilates a)) ∙ (base-0P (v +n-vec v')))
                       λ v' b c → (base-poly+ (v +n-vec v') (a · b) (a · c))
                                   ∙ (cong (base (v +n-vec v')) (sym (·Rdist+ a b c))))
                       -- End Right induction
            (λ PS QS Q → (PS Q) poly+ (QS Q) )
            (λ PS QS RS i Q → poly+Assoc (PS Q) (QS Q) (RS Q) i)
            (λ PS i Q       → poly+IdR (PS Q) i)
            (λ PS QS i Q    → poly+Comm (PS Q) (QS Q) i)
            (λ v    → funExt (
                             -- Induction Right Argument
                             Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                             refl
                             (λ v' a' → (cong (base (v +n-vec v')) (0LeftAnnihilates a')) ∙ (base-0P (v +n-vec v')))
                             λ {P Q} ind-P ind-Q → (cong₂ _poly+_ ind-P ind-Q) ∙ (poly+IdR 0P) ))
                             -- End Right Induction
            λ v a b → funExt (
                             -- Induction Right Argument
                             Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                             (poly+IdR 0P)
                             (λ v' c → (base-poly+ (v +n-vec v') (a · c) (b · c))
                                        ∙ (cong (base (v +n-vec v')) (sym (·Ldist+ a b c))))
                             λ {P Q} ind-P ind-Q → (poly-com-adv _ _ _ _) ∙ (cong₂ _poly+_ ind-P ind-Q))
                             -- End Right Induction
            -- End Left Induction



  poly*Assoc : (P Q R : Poly A' n) → P poly* (Q poly* R) ≡ (P poly* Q) poly* R
  poly*Assoc = Poly-Ind-Prop.f A' n _
                (λ P p q i Q R j → trunc (P poly* (Q poly* R)) ((P poly* Q) poly* R) (p Q R) (q Q R) i j)
                (λ _ _ → refl)
                (λ v a → Poly-Ind-Prop.f A' n _
                          (λ Q p q i R j → trunc (base v a poly* (Q poly* R)) ((base v a poly* Q) poly* R) (p R) (q R) i j)
                          (λ _ → refl)
                          (λ v' a' → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                                      refl
                                      (λ v'' a'' → cong₂ base (+n-vec-assoc v v' v'') (·Assoc a a' a''))
                                      (λ {U V} ind-U ind-V → cong₂ _poly+_ ind-U ind-V))
                          (λ {U V} ind-U ind-V R → cong₂ _poly+_ (ind-U R) (ind-V R)))
                λ {U V} ind-U ind-V Q R → cong₂ _poly+_ (ind-U Q R) (ind-V Q R)

  poly*AnnihilL : (P : Poly A' n) → 0P poly* P ≡ 0P
  poly*AnnihilL P = refl


  poly*AnnihilR : (P : Poly A' n) → P poly* 0P ≡ 0P
  poly*AnnihilR = Poly-Ind-Prop.f A' n (λ P → (P poly* 0P) ≡ 0P) (λ _ → trunc _ _)
                           refl
                           (λ _ _ → refl)
                           λ {P Q} ind-P ind-Q → (cong₂ _poly+_ ind-P ind-Q) ∙ (poly+IdR 0P)


  1P : Poly A' n
  1P = base (replicate zero) 1r


  poly*IdR : (P : Poly A' n) → P poly* 1P ≡ P
  poly*IdR = Poly-Ind-Prop.f A' n (λ P → (P poly* 1P) ≡ P) (λ _ → trunc _ _)
              refl
              (λ v a → cong₂ base (+n-vec-rid v) (·Rid a))
              (λ {P Q} ind-P ind-Q → cong₂ _poly+_ ind-P ind-Q)


  poly*IdL : (P : Poly A' n) → 1P poly* P ≡ P
  poly*IdL = Poly-Ind-Prop.f A' n (λ P → (1P poly* P) ≡ P) (λ _ → trunc _ _)
              refl
              (λ v a → cong₂ base (+n-vec-lid v) (·Lid a))
              λ {P Q} ind-P ind-Q → cong₂ _poly+_ ind-P ind-Q


  poly*DistR : (P Q R : Poly A' n) → P poly* (Q poly+ R) ≡ (P poly* Q) poly+ (P poly* R)
  poly*DistR = Poly-Ind-Prop.f A' n _
               (λ P p q i Q R j → trunc (P poly* (Q poly+ R)) ((P poly* Q) poly+ (P poly* R)) (p Q R) (q Q R) i j)
               (λ _ _ → sym (poly+IdR 0P))
               (λ v a → λ Q R → refl)
               λ {U V} ind-U ind-V Q R → (cong₂ _poly+_ (ind-U Q R) (ind-V Q R)) ∙ poly-com-adv (U poly* Q) (U poly* R) (V poly* Q) (V poly* R)


  poly*DistL : (P Q R : Poly A' n) → (P poly+ Q) poly* R ≡ (P poly* R) poly+ (Q poly* R)
  poly*DistL P Q R = refl


  poly*Comm : (P Q : Poly A' n) → P poly* Q ≡ Q poly* P
  poly*Comm = Poly-Ind-Prop.f A' n _
              (λ P p q i Q j → trunc (P poly* Q) (Q poly* P) (p Q) (q Q) i j)
              (λ Q → sym (poly*AnnihilR Q))
              (λ v a → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                        refl
                        (λ v' a' → cong₂ base (+n-vec-comm v v') (·Comm a a'))
                        (λ {U V} ind-U ind-V → cong₂ _poly+_ ind-U ind-V))
              λ {U V} ind-U ind-V Q → ((cong₂ _poly+_ (ind-U Q) (ind-V Q)) ∙ sym (poly*DistR Q U V))

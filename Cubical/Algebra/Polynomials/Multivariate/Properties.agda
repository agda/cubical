{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec

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

  Poly-com-adv : (P Q R S : Poly A' n) →  ((P Poly+ Q) Poly+ (R Poly+ S) ≡ (P Poly+ R) Poly+ (Q Poly+ S))
  Poly-com-adv P Q R S = ((P Poly+ Q) Poly+ (R Poly+ S) ≡⟨ Poly+-assoc (P Poly+ Q) R S ⟩
                     (((P Poly+ Q) Poly+ R) Poly+ S) ≡⟨ cong (λ X → X Poly+ S) (sym (Poly+-assoc P Q R)) ⟩
                     ((P Poly+ (Q Poly+ R)) Poly+ S) ≡⟨ cong (λ X → (P Poly+ X) Poly+ S) (Poly+-comm Q R) ⟩
                     ((P Poly+ (R Poly+ Q)) Poly+ S) ≡⟨ cong (λ X → X Poly+ S) (Poly+-assoc P R Q) ⟩
                     (((P Poly+ R) Poly+ Q) Poly+ S) ≡⟨ sym (Poly+-assoc (P Poly+ R) Q S) ⟩
                     ((P Poly+ R) Poly+ (Q Poly+ S)) ∎)


  Poly+-Lid : (P : Poly A' n) → 0P Poly+ P ≡ P
  Poly+-Lid P = (Poly+-comm 0P P) ∙ (Poly+-Rid P)


  Poly-inv : Poly A' n → Poly A' n
  Poly-inv = Poly-Rec-Set.f A' n (Poly A' n) trunc
             0P
             (λ v a → base v (- a))
             (λ PS RS → PS Poly+ RS)
             Poly+-assoc
             Poly+-Rid
             Poly+-comm
             (λ v → base v (- 0r) ≡⟨ cong (base v) 0Selfinverse ⟩ base v 0r ≡⟨ base-0P v ⟩ 0P ∎)
             λ v a b → (base-Poly+ v (- a) (- b)) ∙ (cong (base v) (-Dist a b))


  Poly-invinv : (P : Poly A' n) → Poly-inv (Poly-inv P) ≡ P
  Poly-invinv = Poly-Ind-Prop.f A' n (λ P → Poly-inv (Poly-inv P) ≡ P) (λ _ → trunc _ _)
                refl
                (λ v a → cong (base v) (-Idempotent a))
                λ {P Q} ind-P ind-Q → cong₂ _Poly+_ ind-P ind-Q


  Poly+-rinv : (P : Poly A' n ) → P Poly+ (Poly-inv P) ≡ 0P
  Poly+-rinv = Poly-Ind-Prop.f A' n (λ P → (P Poly+ Poly-inv P) ≡ 0P) (λ _ → trunc _ _)
               (Poly+-Rid 0P)
               (λ v a → (base-Poly+ v a (- a)) ∙ cong (base v) (+Rinv a) ∙ base-0P v)
               λ {P Q} ind-P ind-Q → ((P Poly+ Q) Poly+ ((Poly-inv P) Poly+ (Poly-inv Q)))
                                               ≡⟨ Poly-com-adv P Q (Poly-inv P) (Poly-inv Q) ⟩
                                      ((P Poly+ Poly-inv P) Poly+ (Q Poly+ Poly-inv Q))
                                               ≡⟨ cong₂ _Poly+_ ind-P ind-Q ⟩
                                      (0P Poly+ 0P)
                                               ≡⟨ Poly+-Rid 0P ⟩
                                      0P ∎

  Poly+-linv : (P  : Poly A' n) → (Poly-inv P) Poly+ P ≡ 0P
  Poly+-linv = Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
               (Poly+-Rid 0P)
               (λ v a → (base-Poly+ v (- a) a) ∙ cong (base v) (snd (+Inv a)) ∙ base-0P v)
               λ {U V} ind-U ind-V → Poly-com-adv (Poly-inv U) (Poly-inv V) U V ∙ cong₂ _Poly+_ ind-U ind-V ∙ Poly+-Rid 0P


-----------------------------------------------------------------------------

  _Poly*_ : Poly A' n → Poly A' n → Poly A' n
  _Poly*_ = -- Induction Left Argument
            Poly-Rec-Set.f A' n (Poly A' n → Poly A' n)
            (λ f g p q i j Q → trunc (f Q) (g Q) (λ X → p X Q) (λ X → q X Q) i j )
            (λ Q    → 0P)
            (λ v a  → -- Induction Right Argument
                       Poly-Rec-Set.f A' n (Poly A' n) trunc
                       0P
                       (λ v' a' → base (v +n-vec v') (a · a'))
                       _Poly+_
                       Poly+-assoc
                       Poly+-Rid
                       Poly+-comm
                       (λ v' → (cong (base (v +n-vec v')) (0RightAnnihilates a)) ∙ (base-0P (v +n-vec v')))
                       λ v' b c → (base-Poly+ (v +n-vec v') (a · b) (a · c)) ∙ (cong (base (v +n-vec v')) (sym (·Rdist+ a b c))))
                       -- End Right induction
            (λ PS QS Q → (PS Q) Poly+ (QS Q) )
            (λ PS QS RS i Q → Poly+-assoc (PS Q) (QS Q) (RS Q) i)
            (λ PS i Q       → Poly+-Rid (PS Q) i)
            (λ PS QS i Q    → Poly+-comm (PS Q) (QS Q) i)
            (λ v    → funExt (
                             -- Induction Right Argument
                             Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                             refl
                             (λ v' a' → (cong (base (v +n-vec v')) (0LeftAnnihilates a')) ∙ (base-0P (v +n-vec v')))
                             λ {P Q} ind-P ind-Q → (cong₂ _Poly+_ ind-P ind-Q) ∙ (Poly+-Rid 0P) ))
                             -- End Right Induction
            λ v a b → funExt (
                             -- Induction Right Argument
                             Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                             (Poly+-Rid 0P)
                             (λ v' c → (base-Poly+ (v +n-vec v') (a · c) (b · c)) ∙ (cong (base (v +n-vec v')) (sym (·Ldist+ a b c))))
                             λ {P Q} ind-P ind-Q → (Poly-com-adv _ _ _ _) ∙ (cong₂ _Poly+_ ind-P ind-Q))
                             -- End Right Induction
            -- End Left Induction



  Poly*-assoc : (P Q R : Poly A' n) → P Poly* (Q Poly* R) ≡ (P Poly* Q) Poly* R
  Poly*-assoc = Poly-Ind-Prop.f A' n _
                (λ P p q i Q R j → trunc (P Poly* (Q Poly* R)) ((P Poly* Q) Poly* R) (p Q R) (q Q R) i j)
                (λ _ _ → refl)
                (λ v a → Poly-Ind-Prop.f A' n _
                          (λ Q p q i R j → trunc (base v a Poly* (Q Poly* R)) ((base v a Poly* Q) Poly* R) (p R) (q R) i j)
                          (λ _ → refl)
                          (λ v' a' → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                                      refl
                                      (λ v'' a'' → cong₂ base (+n-vec-assoc v v' v'') (·Assoc a a' a''))
                                      (λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V))
                          (λ {U V} ind-U ind-V R → cong₂ _Poly+_ (ind-U R) (ind-V R)))
                λ {U V} ind-U ind-V Q R → cong₂ _Poly+_ (ind-U Q R) (ind-V Q R)

  0PLeftAnnihilatesPoly : (P : Poly A' n) → 0P Poly* P ≡ 0P
  0PLeftAnnihilatesPoly P = refl


  0PRightAnnihilatesPoly : (P : Poly A' n) → P Poly* 0P ≡ 0P
  0PRightAnnihilatesPoly = Poly-Ind-Prop.f A' n (λ P → (P Poly* 0P) ≡ 0P) (λ _ → trunc _ _)
                           refl
                           (λ _ _ → refl)
                           λ {P Q} ind-P ind-Q → (cong₂ _Poly+_ ind-P ind-Q) ∙ (Poly+-Rid 0P)


  1P : Poly A' n
  1P = base (replicate zero) 1r


  Poly*-Rid : (P : Poly A' n) → P Poly* 1P ≡ P
  Poly*-Rid = Poly-Ind-Prop.f A' n (λ P → (P Poly* 1P) ≡ P) (λ _ → trunc _ _)
              refl
              (λ v a → cong₂ base (+n-vec-rid v) (·Rid a))
              (λ {P Q} ind-P ind-Q → cong₂ _Poly+_ ind-P ind-Q)


  Poly*-Lid : (P : Poly A' n) → 1P Poly* P ≡ P
  Poly*-Lid = Poly-Ind-Prop.f A' n (λ P → (1P Poly* P) ≡ P) (λ _ → trunc _ _)
              refl
              (λ v a → cong₂ base (+n-vec-lid v) (·Lid a))
              λ {P Q} ind-P ind-Q → cong₂ _Poly+_ ind-P ind-Q


  Poly*-Rdist : (P Q R : Poly A' n) → P Poly* (Q Poly+ R) ≡ (P Poly* Q) Poly+ (P Poly* R)
  Poly*-Rdist = Poly-Ind-Prop.f A' n _
                (λ P p q i Q R j → trunc (P Poly* (Q Poly+ R)) ((P Poly* Q) Poly+ (P Poly* R)) (p Q R) (q Q R) i j)
                (λ _ _ → sym (Poly+-Rid 0P))
                (λ v a → λ Q R → refl)
                λ {U V} ind-U ind-V Q R → (cong₂ _Poly+_ (ind-U Q R) (ind-V Q R)) ∙ Poly-com-adv (U Poly* Q) (U Poly* R) (V Poly* Q) (V Poly* R)


  Poly*-Ldist : (P Q R : Poly A' n) → (P Poly+ Q) Poly* R ≡ (P Poly* R) Poly+ (Q Poly* R)
  Poly*-Ldist P Q R = refl


  Poly*-comm : (P Q : Poly A' n) → P Poly* Q ≡ Q Poly* P
  Poly*-comm = Poly-Ind-Prop.f A' n _
               (λ P p q i Q j → trunc (P Poly* Q) (Q Poly* P) (p Q) (q Q) i j)
               (λ Q → sym (0PRightAnnihilatesPoly Q))
               (λ v a → Poly-Ind-Prop.f A' n _ (λ _ → trunc _ _)
                          refl
                          (λ v' a' → cong₂ base (+n-vec-comm v v') (·Comm a a'))
                          (λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V))
               λ {U V} ind-U ind-V Q → ((cong₂ _Poly+_ (ind-U Q) (ind-V Q)) ∙ sym (Poly*-Rdist Q U V))

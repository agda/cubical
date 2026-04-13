module Cubical.Tactics.CommRingSolver.EvalHom where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool as 𝟚
open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver.Utility
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.HornerEval

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ ℓ' : Level

module HomomorphismProperties (R@(⟨R⟩ , _) : CommRing ℓ)
                         -- (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where
 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HornerEval R R' hom public


 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)

 private
  module RT' = RingTheory (CommRing→Ring R')

 EvalHom+0 : {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
     → eval (0ₕ +ₕ P) xs ≡ eval P xs
 EvalHom+0 {n = ℕ.zero} (const x) [] = cong scalar‵ (+IdL ( x))
 EvalHom+0 {n = ℕ.suc _} P xs = refl

 Eval0H : {n : ℕ} (xs : Vec ⟨R'⟩ n)
        → eval 0ₕ xs ≡ 0r‵
 Eval0H  [] = pres0
 Eval0H (x ∷ xs) = refl

 Eval1ₕ : {n : ℕ} (xs : Vec ⟨R'⟩ n)
        → eval  1ₕ xs ≡ 1r‵
 Eval1ₕ [] = pres1
 Eval1ₕ (x ∷ xs) =
   eval  0H (x ∷ xs) ·‵ x +‵ eval 1ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 1ₕ xs)
                                                                  (Eval0H (x ∷ xs)) ⟩
   0r‵ ·‵ x +‵ eval 1ₕ xs                          ≡⟨ cong (λ u → 0r‵ ·‵ x +‵ u)
                                                       (Eval1ₕ xs) ⟩
   0r‵ ·‵ x +‵ 1r‵                                  ≡⟨ cong (λ u → u +‵ 1r‵)
                                                        (R‵.0LeftAnnihilates _) ⟩
   0r‵ +‵ 1r‵                                      ≡⟨ R‵.+IdL _ ⟩
   1r‵ ∎

 -EvalDist :
   {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (-ₕ P) xs ≡ -‵ eval P xs
 -EvalDist (const x) []   = pres- _
 -EvalDist 0H  xs =  Eval0H xs ∙
   sym (R‵.0Selfinverse)
   ∙ cong -‵_ (sym (Eval0H xs)) --
 -EvalDist (P ·X+ Q) (x ∷ xs) =
     (eval (-ₕ P) (x ∷ xs)) ·‵ x +‵ eval (-ₕ Q) xs
   ≡⟨ cong (λ u → u ·‵ x +‵ eval (-ₕ Q) xs) (-EvalDist P _) ⟩
     (-‵ eval P (x ∷ xs)) ·‵ x +‵ eval (-ₕ Q) xs
   ≡⟨ cong (λ u → (-‵ eval P (x ∷ xs)) ·‵ x +‵ u) (-EvalDist Q _) ⟩
     (-‵ eval P (x ∷ xs)) ·‵ x +‵ -‵ eval Q xs
   ≡[ i ]⟨ R‵.-DistL· (eval P (x ∷ xs)) x i +‵  -‵ eval Q xs ⟩
     -‵ ((eval P (x ∷ xs)) ·‵ x) +‵ (-‵ eval Q xs)
   ≡⟨ R‵.-Dist _ _ ⟩
     -‵ eval (P ·X+ Q) (x ∷ xs) ∎

 -- combineCases+ : {n : ℕ} (P Q : IteratedHornerForms (ℕ.suc n))
 --                 (r s : IteratedHornerForms n)
 --                 (x : fst R') (xs : Vec (fst R') n)
 --                 → eval ((P ·X+ r) +ₕ (Q ·X+ s)) (x ∷ xs)
 --                 ≡ eval ((P +ₕ Q) ·X+ (r +ₕ s)) (x ∷ xs)
 -- combineCases+ {n = n} P Q r s x xs with (isZero (P +ₕ Q) and isZero (r +ₕ s)) 𝟚.≟ true
 -- ... | yes p = compute+ₕEvalBothZero n P Q r s x xs p
 -- ... | no p = compute+ₕEvalNotBothZero n P Q r s x xs (𝟚.¬true→false _ p)

 +Homeval :
   {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (P +ₕ Q) xs ≡ (eval P xs) +‵ (eval Q xs)
 +Homeval (const x) (const y) [] = pres+ _ _
 +Homeval 0H Q xs =
   eval (0H +ₕ Q) xs            ≡⟨ refl ⟩
   eval Q xs                    ≡⟨ sym (R‵.+IdL _) ⟩
   0r‵ +‵ eval Q xs               ≡⟨ cong (λ u → u +‵ eval Q xs) (sym (Eval0H xs)) ⟩
   eval 0H xs +‵ eval Q xs ∎
 +Homeval (P ·X+ Q) 0H xs =
   eval ((P ·X+ Q) +ₕ 0H) xs                    ≡⟨ refl ⟩
   eval (P ·X+ Q) xs                            ≡⟨ sym (R‵.+IdR _) ⟩
   eval (P ·X+ Q) xs +‵ 0r‵
  ≡⟨ cong (λ u → eval (P ·X+ Q) xs +‵ u) (sym (Eval0H xs)) ⟩
   eval (P ·X+ Q) xs +‵ eval 0H xs ∎
 +Homeval (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
   (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ eval (Q +ₕ T) xs
  ≡⟨ cong (λ u → (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ u) (+Homeval Q T xs) ⟩
   (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ cong (λ u → u ·‵ x +‵ (eval Q xs +‵ eval T xs)) (+Homeval P S (x ∷ xs)) ⟩
   (eval P (x ∷ xs) +‵ eval S (x ∷ xs)) ·‵ x
   +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ cong (λ u → u +‵ (eval Q xs +‵ eval T xs)) (R‵.·DistL+ _ _ _) ⟩
   (eval P (x ∷ xs)) ·‵ x +‵ (eval S (x ∷ xs)) ·‵ x
   +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ R‵.+ShufflePairs _ _ _ _ ⟩
   ((eval P (x ∷ xs)) ·‵ x +‵ eval Q xs)
   +‵ ((eval S (x ∷ xs)) ·‵ x +‵ eval T xs) ∎

 ⋆Homeval : {n : ℕ}
            (r : IteratedHornerForms n)
            (P : IteratedHornerForms (ℕ.suc n)) (x : ⟨R'⟩) (xs : Vec ⟨R'⟩ n)
          → eval (r ⋆ P) (x ∷ xs) ≡ eval r xs ·‵ eval P (x ∷ xs)

 ⋆0LeftAnnihilates :
   {n : ℕ} (P : IteratedHornerForms (ℕ.suc n)) (xs : Vec ⟨R'⟩ (ℕ.suc n))
   → eval (0ₕ ⋆ P) xs ≡ 0r‵
 ⋆0LeftAnnihilates 0H xs = Eval0H xs
 ⋆0LeftAnnihilates {n = ℕ.zero} (P HornerForms.·X+ HornerForms.const x₁) (x ∷ xs) =
   cong₂ _+‵_  ((RT'.0LeftAnnihilates' _ _ (⋆0LeftAnnihilates P (x ∷ xs))))
     (cong (λ u → eval (IteratedHornerForms.const u) xs) (0LeftAnnihilates x₁)
      ∙ Eval0H xs) ∙ RT'.0Idempotent

 ⋆0LeftAnnihilates {n = ℕ.suc _} (P ·X+ Q) (x ∷ xs) =
   cong₂ _+‵_ (RT'.0LeftAnnihilates' _ _ (⋆0LeftAnnihilates P (x ∷ xs)))
        (Eval0H xs) ∙ RT'.0Idempotent

 ·0LeftAnnihilates :
   {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (0ₕ ·ₕ P) xs ≡ 0r‵
 ·0LeftAnnihilates (const x) xs =
   cong (λ x → eval (const x) xs) (0LeftAnnihilates x) ∙ Eval0H xs
 ·0LeftAnnihilates 0H xs = Eval0H xs
 ·0LeftAnnihilates (P ·X+ P₁) xs = Eval0H xs

 ·Homeval : {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (P ·ₕ Q) xs ≡ (eval P xs) ·‵ (eval Q xs)

 ⋆Homeval r 0H x xs =
   eval (r ⋆ 0H) (x ∷ xs)                ≡⟨ refl ⟩
   0r‵                                    ≡⟨ sym (R‵.0RightAnnihilates _) ⟩
   eval r xs ·‵ 0r‵                        ≡⟨ refl ⟩
   eval r xs ·‵ eval  0H (x ∷ xs) ∎
 ⋆Homeval r (P ·X+ Q) x xs =
     eval ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)
   ≡⟨ cong (λ u → u ·‵ x +‵ eval (r ·ₕ Q) xs) (⋆Homeval r P x xs) ⟩
     (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ eval (r ·ₕ Q) xs
   ≡⟨ cong (λ u → (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ u) (·Homeval r Q xs) ⟩
     (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ eval r xs ·‵ eval Q xs
   ≡⟨ cong (λ u → u  +‵ eval r xs ·‵ eval Q xs) (sym (R‵.·Assoc _ _ _)) ⟩
     eval r xs ·‵ (eval P (x ∷ xs) ·‵ x) +‵ eval r xs ·‵ eval Q xs
   ≡⟨ sym (R‵.·DistR+ _ _ _) ⟩

     eval r xs ·‵ eval (P ·X+ Q) (x ∷ xs) ∎

 ·Homeval (const x) (const y) [] = pres· _ _
 ·Homeval 0H Q xs =
   eval (0H ·ₕ Q) xs       ≡⟨ Eval0H xs ⟩
   0r‵                     ≡⟨ sym (R‵.0LeftAnnihilates _) ⟩
   0r‵ ·‵ eval Q xs         ≡⟨ cong (λ u → u ·‵ eval Q xs) (sym (Eval0H xs)) ⟩
   eval 0H xs ·‵ eval Q xs ∎
 ·Homeval (P ·X+ Q) S (x ∷ xs) =

     eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
   ≡⟨ +Homeval ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
     (eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ eval 0ₕ xs) +‵ eval (Q ⋆ S) (x ∷ xs)
   ≡⟨ cong (λ u → u +‵ eval (Q ⋆ S) (x ∷ xs))
         ((eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ eval 0ₕ xs)
        ≡⟨ cong (λ u → eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ u) (Eval0H xs) ⟩
          (eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ 0r‵)
        ≡⟨ R‵.+IdR _ ⟩
          (eval (P ·ₕ S) (x ∷ xs) ·‵ x)
        ≡⟨ cong (λ u → u ·‵ x) (·Homeval P S (x ∷ xs)) ⟩
          ((eval P (x ∷ xs) ·‵ eval S (x ∷ xs)) ·‵ x)
        ≡⟨ sym (R‵.·Assoc _ _ _) ⟩
          (eval P (x ∷ xs) ·‵ (eval S (x ∷ xs) ·‵ x))
        ≡⟨ cong (λ u → eval P (x ∷ xs) ·‵ u) (R‵.·Comm _ _) ⟩
          (eval P (x ∷ xs) ·‵ (x ·‵ eval S (x ∷ xs)))
        ≡⟨ R‵.·Assoc _ _ _ ⟩
          (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs)
         ∎) ⟩
     (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ eval (Q ⋆ S) (x ∷ xs)
   ≡⟨ cong (λ u → (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ u)
           (⋆Homeval Q S x xs) ⟩
     (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ eval Q xs ·‵ eval S (x ∷ xs)
   ≡⟨ sym (R‵.·DistL+ _ _ _) ⟩

     eval (P ·X+ Q) (x ∷ xs) ·‵ eval S (x ∷ xs) ∎

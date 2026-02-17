module Cubical.Tactics.CommRingSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import Cubical.Reflection.Sugar

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.EvalHom

private
  variable
    ℓ ℓ' : Level

module EqualityToNormalform (R@(⟨R⟩ , _) : CommRing ℓ)
                         (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where

 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HomomorphismProperties R _≟_ R' hom
 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)


 RExpr : (n : ℕ) → Type _
 RExpr = Expr RRng (fst R')

 normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 normalize {n = n} (K r) = Constant n r
 normalize {n = n} (∣ k) = Variable n k
 normalize (x +' y) =
   (normalize x) +ₕ (normalize y)
 normalize (x ·' y) =
   (normalize x) ·ₕ (normalize y)
 normalize (-' x) =  -ₕ (normalize x)

 isEqualToNormalform :
      {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n)
    → eval (normalize e) xs ≡ ⟦ e ⟧ xs

 isEqualToNormalform (K r) [] = refl
 isEqualToNormalform {n = ℕ.suc n} (K r) (x ∷ xs) =
   zz (r ≟ 0r)

   where
   zz : ∀ rr → eval (decRec (λ _ → 0ₕ) (λ _ → 0ₕ ·X+ Constant n r) rr) (x ∷ xs) ≡ scalar‵ r
   zz (yes p) = sym (cong scalar‵ p ∙ pres0)
   zz (no _) =
    eval (0ₕ ·X+ Constant n r) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Constant n r) x xs ⟩
    eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Constant n r) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Constant n r) xs)
                                                            (Eval0H (x ∷ xs)) ⟩
    0r‵ ·‵ x +‵ eval (Constant n r) xs               ≡⟨ cong
                                                         (λ u → u +‵ eval (Constant n r) xs)
                                                         (R‵.0LeftAnnihilates _) ⟩
    0r‵ +‵ eval (Constant n r) xs                   ≡⟨ R‵.+IdL _ ⟩
    eval (Constant n r) xs                        ≡⟨ isEqualToNormalform (K r) xs ⟩
    _ ∎
 isEqualToNormalform (∣ zero) (x ∷ xs) =
   eval (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ combineCasesEval 1ₕ 0ₕ x xs ⟩
   eval 1ₕ (x ∷ xs) ·‵ x +‵ eval 0ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 0ₕ xs)
                                             (Eval1ₕ (x ∷ xs)) ⟩
   1r‵ ·‵ x +‵ eval 0ₕ xs                 ≡⟨ cong (λ u → 1r‵  ·‵ x +‵ u ) (Eval0H xs) ⟩
   1r‵ ·‵ x +‵ 0r‵                        ≡⟨ R‵.+IdR _ ⟩
   1r‵ ·‵ x                             ≡⟨ R‵.·IdL _ ⟩
   x ∎
 isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
     eval (0ₕ ·X+ Variable n k) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Variable n k) x xs ⟩
     eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Variable n k) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Variable n k) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r‵ ·‵ x +‵ eval (Variable n k) xs              ≡⟨ cong (λ u → u +‵ eval (Variable n k) xs)
                                                             (R‵.0LeftAnnihilates _) ⟩
     0r‵ +‵ eval (Variable n k) xs                  ≡⟨ R‵.+IdL _ ⟩
     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 isEqualToNormalform (-' e) [] =
   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
   -‵ eval (normalize e) []    ≡⟨ cong -‵_ (isEqualToNormalform e [] ) ⟩
   -‵ ⟦ e ⟧ [] ∎
 isEqualToNormalform (-' e) (x ∷ xs) =
   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
   -‵ eval (normalize e) (x ∷ xs)    ≡⟨ cong -‵_ (isEqualToNormalform e (x ∷ xs) ) ⟩
   -‵ ⟦ e ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e +' e₁) [] =
       eval (normalize e +ₕ normalize e₁) []
     ≡⟨ +Homeval (normalize e) _ [] ⟩
       eval (normalize e) []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] +‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] +‵ ⟦ e₁ ⟧ [] ∎
 isEqualToNormalform (e +' e₁) (x ∷ xs) =
       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e ·' e₁) [] =
       eval (normalize e ·ₕ normalize e₁) []
     ≡⟨ ·Homeval (normalize e) _ [] ⟩
       eval (normalize e) [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] ·‵ ⟦ e₁ ⟧ [] ∎

 isEqualToNormalform (e ·' e₁) (x ∷ xs) =
       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) → (Σ (Type ℓ) λ X → ((X → e₁ ≡ e₂) × Dec X))
 IHR? (const x) (const x') = (x ≡ x') , cong const , (x ≟ x')
 IHR? 0H 0H = ℕ.Unit* , (λ _ → refl) , yes _
 IHR? (e₁ ·X+ e₂) (e₁' ·X+ e₂') =
   let X , f , d = IHR? e₁ e₁'
       X' , f' , d' = IHR? e₂ e₂'
   in X × X'
       , (λ (x , x') → cong₂ _·X+_ (f x) (f' x'))
       , Dec× d d'
 IHR? _ _ = ⊥* , (λ ()) , no λ ()

 IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → fst (IHR? e e)
 IHR?-refl (HornerForms.const x) = refl
 IHR?-refl HornerForms.0H = lift ℕ.tt
 IHR?-refl (e HornerForms.·X+ e₁) = IHR?-refl e , IHR?-refl e₁

 HF-refl : ∀ {n} (e : RExpr n) → fst (IHR? (normalize e) (normalize e))
 HF-refl e = IHR?-refl (normalize e)



 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨
    cong eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) ≡$ xs ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎


 solveByDec :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → 𝟚.True (snd (snd (IHR? (normalize e₁) (normalize e₂))))
   → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solveByDec e₁ e₂ xs z = solve e₁ e₂ xs (𝟚.toWitness z)

 HF-unit : ∀ {n : ℕ} (e : RExpr n) → Unit
 HF-unit _ = _


 congSolve :
   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 congSolve e₁ e₂ {xs} {xs'} p z =
   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨
    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
   ⟦ e₂ ⟧ xs' ∎

 solveByPath :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solveByPath e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
    eval (normalize e₁) xs ≡⟨ p ⟩
    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎

{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.RadicalIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_ ; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

module _ (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'
 open BinomialThm R'
 open CommIdeal R'
 open isCommIdeal


 √ : ℙ R → ℙ R --\surd
 √ I x = (∃[ n ∈ ℕ ] x ^ n ∈ I) , isPropPropTrunc

 ^∈√→∈√ : ∀ (I : ℙ R) (x : R) (n : ℕ) → x ^ n ∈ √ I → x ∈ √ I
 ^∈√→∈√ I x n =
         map (λ { (m , [xⁿ]ᵐ∈I) → (n ·ℕ m) , subst-∈ I (sym (^-rdist-·ℕ x n m)) [xⁿ]ᵐ∈I })

 ∈→∈√ : ∀ (I : ℙ R) (x : R) → x ∈ I → x ∈ √ I
 ∈→∈√ I _ x∈I = ∣ 1 , subst-∈ I (sym (·Rid _)) x∈I ∣

 √OfIdealIsIdeal : ∀ (I : ℙ R) → isCommIdeal I → isCommIdeal (√ I)
 +Closed (√OfIdealIsIdeal I ici) {x = x} {y = y} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ n ∈ ℕ ] x ^ n ∈ I → Σ[ n ∈ ℕ ] y ^ n ∈ I → Σ[ n ∈ ℕ ] (x + y) ^ n ∈ I
  +ClosedΣ (n , xⁿ∈I) (m , yᵐ∈I) = (n +ℕ m)
                                  , subst-∈ I (sym (BinomialThm (n +ℕ m) _ _)) ∑Binomial∈I
   where
   binomialCoeff∈I : ∀ i → ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i) ∈ I
   binomialCoeff∈I i with ≤-+-split n m (toℕ i) (pred-≤-pred (toℕ<n i))
   ... | inl n≤i = subst-∈ I (sym path) (·Closed ici _ xⁿ∈I)
    where
    useSolver : ∀ a b c d → a · (b · c) · d ≡ a · b · d · c
    useSolver = solve R'
    path : ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡ ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n
    path = ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ k → ((n +ℕ m) choose toℕ i) · x ^ k · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (≤-∸-+-cancel n≤i)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ ((toℕ i ∸ n) +ℕ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ z → ((n +ℕ m) choose toℕ i) · z · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (·-of-^-is-^-of-+ x (toℕ i ∸ n) n)) ⟩
           ((n +ℕ m) choose toℕ i) · (x ^ (toℕ i ∸ n) · x ^ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ useSolver _ _ _ _ ⟩
           ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n ∎

   ... | inr m≤n+m-i = subst-∈ I (sym path) (·Closed ici _ yᵐ∈I)
    where
    path : ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡ ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m
    path = ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ k → ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ k)
                 (sym (≤-∸-+-cancel m≤n+m-i)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (((n +ℕ m ∸ toℕ i) ∸ m) +ℕ m)
         ≡⟨ cong (((n +ℕ m) choose toℕ i) · x ^ toℕ i ·_)
                 (sym (·-of-^-is-^-of-+ y ((n +ℕ m ∸ toℕ i) ∸ m) m)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · (y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m)
         ≡⟨ ·Assoc _ _ _ ⟩
           ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ ((n +ℕ m ∸ toℕ i) ∸ m) · y ^ m ∎

   ∑Binomial∈I : ∑ (BinomialVec (n +ℕ m) x y) ∈ I
   ∑Binomial∈I = ∑Closed (I , ici) (BinomialVec (n +ℕ m) _ _) binomialCoeff∈I
 contains0 (√OfIdealIsIdeal I ici) =
   ∣ 1 , subst-∈ I (sym (0LeftAnnihilates 1r)) (ici .contains0) ∣
 ·Closed (√OfIdealIsIdeal I ici) r =
   map λ { (n , xⁿ∈I) → n , subst-∈ I (sym (^-ldist-· r _ n)) (ici .·Closed (r ^ n) xⁿ∈I) }

 √i : CommIdeal → CommIdeal
 √i I = √ (I .fst) , √OfIdealIsIdeal (I .fst) (I .snd)

 -- important lemma for characterization of the Zariski lattice
 √FGIdealChar : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
                → √ (fst ⟨ V ⟩[ R' ]) ⊆ √ (fst I) ≃ (∀ i → V i ∈ √ (fst I))
 √FGIdealChar V I = propBiimpl→Equiv (⊆-isProp (√ (fst ⟨ V ⟩[ R' ])) (√ (fst I)))
                                     (isPropΠ (λ _ → √ (fst I) _ .snd))
                                     ltrImpl rtlImpl
  where
  open KroneckerDelta (CommRing→Ring R')
  ltrImpl : √ (fst ⟨ V ⟩[ R' ]) ⊆ √ (fst I) → (∀ i → V i ∈ √ (fst I))
  ltrImpl √⟨V⟩⊆√I i = √⟨V⟩⊆√I _ (∈→∈√ (fst ⟨ V ⟩[ R' ]) (V i)
                                        ∣ (λ j → δ i j) , sym (∑Mul1r _ _ i) ∣)

  rtlImpl : (∀ i → V i ∈ √ (fst I)) → √ (fst ⟨ V ⟩[ R' ]) ⊆ √ (fst I)
  rtlImpl ∀i→Vi∈√I x = PT.elim (λ _ → √ (fst I) x .snd)
                                λ { (n , xⁿ∈⟨V⟩) → ^∈√→∈√ (fst I) x n (elimHelper _ xⁿ∈⟨V⟩) }
   where
   isCommIdeal√I = √OfIdealIsIdeal (fst I) (snd I)
   elimHelper : ∀ (y : R) → y ∈ (fst ⟨ V ⟩[ R' ]) → y ∈ √ (fst I)
   elimHelper y = PT.elim (λ _ → √ (fst I) y .snd)
                   λ { (α , y≡∑αV) → subst-∈ (√ (fst I)) (sym y≡∑αV)
                                           (∑Closed (√ (fst I) , isCommIdeal√I)
                                           (λ i → α i · V i)
                                           (λ i → isCommIdeal√I .·Closed (α i) (∀i→Vi∈√I i))) }

 √+Contr : (I J : CommIdeal) → √i (I +i √i J) ≡ √i (I +i J)
 √+Contr I J = CommIdeal≡Char incl1 incl2
  where
  incl1 : √i (I +i √i J) .fst ⊆ √i (I +i J) .fst
  incl1 x = PT.elim (λ _ → isPropPropTrunc)
              (uncurry (λ n → PT.elim (λ _ → isPropPropTrunc)
                (uncurry3 (curriedIncl1 n))))
   where
   curriedIncl1 : (n : ℕ) (y : R × R)
                → (y .fst ∈ I .fst)
                → (y . snd ∈ √ (J .fst))
                → (x ^ n ≡ y .fst + y .snd)
                → x ∈ √i (I +i J) .fst
   curriedIncl1 n (y , z) y∈I = PT.elim (λ _ → isPropΠ λ _ → isPropPropTrunc) Σhelper
    where
    yVec : (m : ℕ) → FinVec R m
    yVec m = (BinomialVec m y z) ∘ suc

    ∑yVec∈I : ∀ m → ∑ (yVec m) ∈ I .fst
    ∑yVec∈I zero = I .snd .contains0
    ∑yVec∈I (suc m) = ∑Closed I (yVec (suc m))
                         λ _ → subst-∈ (I .fst) (useSolver _ _ _ _) (I .snd .·Closed _ y∈I)
     where
     useSolver : (bc y y^i z^m-i : R) → (bc · y^i · z^m-i) · y ≡ bc · (y · y^i) · z^m-i
     useSolver = solve R'

    path : (m : ℕ) → x ^ n ≡ y + z → x ^ (n ·ℕ m) ≡ ∑ (yVec m) + z ^ m
    path m p = x ^ (n ·ℕ m) ≡⟨ ^-rdist-·ℕ x n m ⟩
               (x ^ n) ^ m ≡⟨ cong (_^ m) p ⟩
               (y + z) ^ m ≡⟨ BinomialThm m y z ⟩
               ∑ (BinomialVec m y z) ≡⟨ useSolver _ _ ⟩
               ∑ (yVec m) + z ^ m ∎
     where
     useSolver : (zm ∑yVec : R) → 1r · 1r · zm + ∑yVec ≡ ∑yVec + zm
     useSolver = solve R'

    Σhelper : Σ[ m ∈ ℕ ] (z ^ m ∈ J .fst) → x ^ n ≡ y + z → x ∈ √i (I +i J) .fst
    Σhelper (m , z^m∈J) x^n≡y+z =
      ∣ n ·ℕ m , ∣ (∑ (yVec m) , z ^ m) , ∑yVec∈I m  , z^m∈J , path m x^n≡y+z ∣ ∣

  incl2 : √ ((I +i J) .fst) ⊆ √ ((I +i √i J) .fst)
  incl2 x = PT.elim (λ _ → isPropPropTrunc) (uncurry curriedIncl2)
   where
   curriedIncl2 : (n : ℕ) → (x ^ n ∈ (I +i J) .fst) → x ∈ √ ((I +i √i J) .fst)
   curriedIncl2 n = map λ ((y , z) , y∈I , z∈J , x≡y+z)
                           → n , ∣ (y , z) , y∈I , ∈→∈√ (J .fst) z z∈J , x≡y+z ∣


 √·Contr : (I J : CommIdeal) → √i (I ·i √i J) ≡ √i (I ·i J)
 √·Contr I J = CommIdeal≡Char incl1 incl2
  where
  incl1 : √i (I ·i √i J) .fst ⊆ √i (I ·i J) .fst
  incl1 x = PT.elim (λ _ → isPropPropTrunc)
              (uncurry (λ n → PT.elim (λ _ → isPropPropTrunc)
                (uncurry4 (curriedIncl1 n))))
   where
   curriedIncl1 : (n m : ℕ) (α : FinVec R m × FinVec R m)
                → (∀ i → α .fst i ∈ I .fst)
                → (∀ i → α .snd i ∈ √ (J .fst))
                → (x ^ n ≡ linearCombination R' (α .fst) (α .snd))
                → x ∈ √i (I ·i J) .fst
   curriedIncl1 n m (α , β) α∈I β∈√J xⁿ≡∑αβ = ^∈√→∈√ ((I ·i J) .fst) x n
    (subst-∈ (√i (I ·i J) .fst) (sym xⁿ≡∑αβ)
    (∑Closed (√i (I ·i J)) (λ i → α i · β i) λ i → prodHelper i (β∈√J i)))
    where
    curriedHelper : ∀ x y → x ∈ I .fst → ∀ l → y ^ l ∈ J .fst → (x · y)  ∈ √ ((I ·i J) .fst)
    curriedHelper x y x∈I zero 1∈J = subst (λ K → (x · y) ∈ √ (K .fst))
                                       (sym (·iRContains1id I J 1∈J)) --1∈J → √IJ ≡ √I ⊃ I
                                       (∈→∈√ (I .fst) _ (·RClosed (I .snd) y x∈I))
    curriedHelper x y x∈I (suc l) y^l+1∈J = -- (xy)^l+1 ≡ x^l · x (∈I) · y^l+1 (∈J)
      ∣ suc l , subst-∈ ((I ·i J) .fst) (sym (^-ldist-· _ _ (suc l)))
      (prodInProd I J _ _ (subst-∈ (I .fst) (·-comm _ _) (I .snd .·Closed (x ^ l) x∈I)) y^l+1∈J) ∣

    prodHelper : ∀ i → β i ∈ √ (J .fst) → α i · β i ∈ √ ((I ·i J) .fst)
    prodHelper i = PT.elim (λ _ → isPropPropTrunc) (uncurry (curriedHelper (α i) (β i) (α∈I i)))

  incl2 : √ ((I ·i J) .fst) ⊆ √ ((I ·i √i J) .fst)
  incl2 x =  PT.elim (λ _ → isPropPropTrunc) (uncurry curriedIncl2)
   where
   curriedIncl2 : (n : ℕ) → (x ^ n ∈ (I ·i J) .fst) → x ∈ √ ((I ·i √i J) .fst)
   curriedIncl2 n = map λ (m , (α , β) , α∈I , β∈J , xⁿ≡∑αβ)
                    → n , ∣ m , (α , β) , α∈I , (λ i → ∈→∈√ (J .fst) (β i) (β∈J i)) , xⁿ≡∑αβ ∣

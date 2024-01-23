{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.RadicalIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset using (⊆-isProp)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_ ; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ : Level

module RadicalIdeal (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'
 open BinomialThm R'
 open CommIdeal R'
 open isCommIdeal
 open IdealSum R'

 √ : CommIdeal → CommIdeal
 fst (√ I) x = (∃[ n ∈ ℕ ] x ^ n ∈ I) , isPropPropTrunc
 +Closed (snd (√ I)) {x = x} {y = y} = map2 +ClosedΣ
  where
  +ClosedΣ : Σ[ n ∈ ℕ ] x ^ n ∈ I → Σ[ n ∈ ℕ ] y ^ n ∈ I → Σ[ n ∈ ℕ ] (x + y) ^ n ∈ I
  +ClosedΣ (n , xⁿ∈I) (m , yᵐ∈I) = (n +ℕ m)
                                  , subst-∈ I (sym (BinomialThm (n +ℕ m) _ _)) ∑Binomial∈I
   where
   binomialCoeff∈I : ∀ i → ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i) ∈ I
   binomialCoeff∈I i with ≤-+-split n m (toℕ i) (pred-≤-pred (toℕ<n i))
   ... | inl n≤i = subst-∈ I (sym path) (·Closed (I .snd) _ xⁿ∈I)
    where
    path : ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡ ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n
    path = ((n +ℕ m) choose toℕ i) · x ^ toℕ i · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ k → ((n +ℕ m) choose toℕ i) · x ^ k · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (≤-∸-+-cancel n≤i)) ⟩
           ((n +ℕ m) choose toℕ i) · x ^ ((toℕ i ∸ n) +ℕ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ cong (λ z → ((n +ℕ m) choose toℕ i) · z · y ^ (n +ℕ m ∸ toℕ i))
                 (sym (·-of-^-is-^-of-+ x (toℕ i ∸ n) n)) ⟩
           ((n +ℕ m) choose toℕ i) · (x ^ (toℕ i ∸ n) · x ^ n) · y ^ (n +ℕ m ∸ toℕ i)
         ≡⟨ solve! R' ⟩
           ((n +ℕ m) choose toℕ i) · x ^ (toℕ i ∸ n) · y ^ (n +ℕ m ∸ toℕ i) · x ^ n ∎

   ... | inr m≤n+m-i = subst-∈ I (sym path) (·Closed (I .snd) _ yᵐ∈I)
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
   ∑Binomial∈I = ∑Closed I (BinomialVec (n +ℕ m) _ _) binomialCoeff∈I
 contains0 (snd (√ I)) =
   ∣ 1 , subst-∈ I (sym (0LeftAnnihilates 1r)) ((I .snd) .contains0) ∣₁
 ·Closed (snd (√ I)) r =
   map λ { (n , xⁿ∈I) → n , subst-∈ I (sym (^-ldist-· r _ n)) ((I .snd) .·Closed (r ^ n) xⁿ∈I) }


 ^∈√→∈√ : ∀ (I : CommIdeal) (x : R) (n : ℕ) → x ^ n ∈ √ I → x ∈ √ I
 ^∈√→∈√ I x n =
         map (λ { (m , [xⁿ]ᵐ∈I) → (n ·ℕ m) , subst-∈ I (sym (^-rdist-·ℕ x n m)) [xⁿ]ᵐ∈I })

 ∈→∈√ : ∀ (I : CommIdeal) (x : R) → x ∈ I → x ∈ √ I
 ∈→∈√ I _ x∈I = ∣ 1 , subst-∈ I (sym (·IdR _)) x∈I ∣₁



 -- important lemma for characterization of the Zariski lattice
 open KroneckerDelta (CommRing→Ring R')
 √FGIdealCharLImpl : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
         → √ ⟨ V ⟩[ R' ] ⊆ √ I → (∀ i → V i ∈ √ I)
 √FGIdealCharLImpl V I √⟨V⟩⊆√I i = √⟨V⟩⊆√I _ (∈→∈√ ⟨ V ⟩[ R' ] (V i)
                                       ∣ (λ j → δ i j) , sym (∑Mul1r _ _ i) ∣₁)

 √FGIdealCharRImpl : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
         → (∀ i → V i ∈ √ I) → √ ⟨ V ⟩[ R' ] ⊆ √ I
 √FGIdealCharRImpl V I ∀i→Vi∈√I x = PT.elim (λ _ → √ I .fst x .snd)
                               λ { (n , xⁿ∈⟨V⟩) → ^∈√→∈√ I x n (elimHelper _ xⁿ∈⟨V⟩) }
  where
  elimHelper : ∀ (y : R) → y ∈ ⟨ V ⟩[ R' ] → y ∈ √ I
  elimHelper y = PT.elim (λ _ → √ I .fst y .snd)
                  λ { (α , y≡∑αV) → subst-∈ (√ I) (sym y≡∑αV)
                                          (∑Closed (√ I)
                                          (λ i → α i · V i)
                                          (λ i → √ I .snd .·Closed (α i) (∀i→Vi∈√I i))) }

 √FGIdealChar : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
                → √ ⟨ V ⟩[ R' ] ⊆ √ I ≃ (∀ i → V i ∈ √ I)
 √FGIdealChar V I = propBiimpl→Equiv (⊆-isProp (√ ⟨ V ⟩[ R' ] .fst) (√ I .fst))
                                     (isPropΠ (λ _ → √ I .fst _ .snd))
                                     (√FGIdealCharLImpl V I)
                                     (√FGIdealCharRImpl V I)

 √+RContrLIncl : (I J : CommIdeal) → √ (I +i √ J) ⊆ √ (I +i J)
 √+RContrLIncl I J x = PT.elim (λ _ → isPropPropTrunc)
             (uncurry (λ n → PT.elim (λ _ → isPropPropTrunc)
               (uncurry3 (curriedIncl1 n))))
  where
  curriedIncl1 : (n : ℕ) (y : R × R)
               → (y .fst ∈ I)
               → (y . snd ∈ √ J)
               → (x ^ n ≡ y .fst + y .snd)
               → x ∈ √ (I +i J)
  curriedIncl1 n (y , z) y∈I = PT.elim (λ _ → isPropΠ λ _ → isPropPropTrunc) Σhelper
   where
   yVec : (m : ℕ) → FinVec R m
   yVec m = (BinomialVec m y z) ∘ suc

   ∑yVec∈I : ∀ m → ∑ (yVec m) ∈ I
   ∑yVec∈I zero = I .snd .contains0
   ∑yVec∈I (suc m) = ∑Closed I (yVec (suc m))
                        λ _ → subst-∈ I (useSolver _ _ _ _) (I .snd .·Closed _ y∈I)
    where
    useSolver : (bc y y^i z^m-i : R) → (bc · y^i · z^m-i) · y ≡ bc · (y · y^i) · z^m-i
    useSolver bc y y^i z^m-i = solve! R'

   path : (m : ℕ) → x ^ n ≡ y + z → x ^ (n ·ℕ m) ≡ ∑ (yVec m) + z ^ m
   path m p = x ^ (n ·ℕ m) ≡⟨ ^-rdist-·ℕ x n m ⟩
              (x ^ n) ^ m ≡⟨ cong (_^ m) p ⟩
              (y + z) ^ m ≡⟨ BinomialThm m y z ⟩
              ∑ (BinomialVec m y z) ≡⟨ useSolver _ _ ⟩
              ∑ (yVec m) + z ^ m ∎
    where
    useSolver : (zm ∑yVec : R) → 1r · 1r · zm + ∑yVec ≡ ∑yVec + zm
    useSolver zm ∑yVec = solve! R'

   Σhelper : Σ[ m ∈ ℕ ] (z ^ m ∈ J) → x ^ n ≡ y + z → x ∈ √ (I +i J)
   Σhelper (m , z^m∈J) x^n≡y+z =
     ∣ n ·ℕ m , ∣ (∑ (yVec m) , z ^ m) , ∑yVec∈I m  , z^m∈J , path m x^n≡y+z ∣₁ ∣₁

 √+RContrRIncl : (I J : CommIdeal) → √ (I +i J) ⊆ √ (I +i √ J)
 √+RContrRIncl I J x = PT.elim (λ _ → isPropPropTrunc) (uncurry curriedIncl2)
  where
  curriedIncl2 : (n : ℕ) → (x ^ n ∈ (I +i J)) → x ∈ √ ((I +i √ J))
  curriedIncl2 n = map λ ((y , z) , y∈I , z∈J , x≡y+z)
                          → n , ∣ (y , z) , y∈I , ∈→∈√ J z z∈J , x≡y+z ∣₁

 √+RContr : (I J : CommIdeal) → √ (I +i √ J) ≡ √ (I +i J)
 √+RContr I J = CommIdeal≡Char (√+RContrLIncl I J) (√+RContrRIncl I J)

 √+LContr : (I J : CommIdeal) → √ (√ I +i J) ≡ √ (I +i J)
 √+LContr I J = cong √ (+iComm (√ I) J) ∙∙ √+RContr J I ∙∙ cong √ (+iComm J I)

 √·RContrLIncl : (I J : CommIdeal) → √ (I ·i √ J) ⊆ √ (I ·i J)
 √·RContrLIncl I J x = PT.elim (λ _ → isPropPropTrunc)
             (uncurry (λ n → PT.elim (λ _ → isPropPropTrunc)
               (uncurry4 (curriedIncl1 n))))
  where
  curriedIncl1 : (n m : ℕ) (α : FinVec R m × FinVec R m)
               → (∀ i → α .fst i ∈ I)
               → (∀ i → α .snd i ∈ √ J)
               → (x ^ n ≡ linearCombination R' (α .fst) (α .snd))
               → x ∈ √ (I ·i J)
  curriedIncl1 n m (α , β) α∈I β∈√J xⁿ≡∑αβ = ^∈√→∈√ (I ·i J) x n
   (subst-∈ (√ (I ·i J)) (sym xⁿ≡∑αβ)
   (∑Closed (√ (I ·i J)) (λ i → α i · β i) λ i → prodHelper i (β∈√J i)))
   where
   curriedHelper : ∀ x y → x ∈ I → ∀ l → y ^ l ∈ J → (x · y) ∈ √ (I ·i J)
   curriedHelper x y x∈I zero 1∈J = subst (λ K → (x · y) ∈ √ K)
                                      (sym (·iRContains1id I J 1∈J)) --1∈J → √J ≡ √ ⊃ I
                                      (∈→∈√ I _ (·RClosed (I .snd) y x∈I))
   curriedHelper x y x∈I (suc l) y^l+1∈J = -- (xy)^l+1 ≡ x^l · x (∈I) · y^l+1 (∈J)
     ∣ suc l , subst-∈ (I ·i J) (sym (^-ldist-· _ _ (suc l)))
     (prodInProd I J _ _ (subst-∈ I (·Comm _ _) (I .snd .·Closed (x ^ l) x∈I)) y^l+1∈J) ∣₁

   prodHelper : ∀ i → β i ∈ √ J → α i · β i ∈ √ (I ·i J)
   prodHelper i = PT.elim (λ _ → isPropPropTrunc) (uncurry (curriedHelper (α i) (β i) (α∈I i)))

 √·RContrRIncl : (I J : CommIdeal) → √ (I ·i J) ⊆ √ (I ·i √ J)
 √·RContrRIncl I J x =  PT.elim (λ _ → isPropPropTrunc) (uncurry curriedIncl2)
  where
  curriedIncl2 : (n : ℕ) → x ^ n ∈ (I ·i J) → x ∈ √ (I ·i √ J)
  curriedIncl2 n = map λ (m , (α , β) , α∈I , β∈J , xⁿ≡∑αβ)
                   → n , ∣ m , (α , β) , α∈I , (λ i → ∈→∈√ J (β i) (β∈J i)) , xⁿ≡∑αβ ∣₁

 √·RContr : (I J : CommIdeal) → √ (I ·i √ J) ≡ √ (I ·i J)
 √·RContr I J = CommIdeal≡Char (√·RContrLIncl I J) (√·RContrRIncl I J)

 √·LContr : (I J : CommIdeal) → √ (√ I ·i J) ≡ √ (I ·i J)
 √·LContr I J = cong √ (·iComm (√ I) J) ∙∙ √·RContr J I ∙∙ cong √ (·iComm J I)

 √·IdemLIncl : ∀ (I : CommIdeal) → √ (I ·i I) ⊆ √ I
 √·IdemLIncl I x = map λ (n , x^n∈II) → (n , ·iLincl I I _ x^n∈II)

 √·IdemRIncl : ∀ (I : CommIdeal) → √ I ⊆ √ (I ·i I)
 √·IdemRIncl I x = map λ (n , x^n∈I) → (n +ℕ n , subst-∈ (I ·i I)
                                (·-of-^-is-^-of-+ x n n) -- x²ⁿ≡xⁿ (∈I) · xⁿ (∈I)
                                (prodInProd I I _ _ x^n∈I x^n∈I))

 √·Idem : ∀ (I : CommIdeal) → √ (I ·i I) ≡ √ I
 √·Idem I = CommIdeal≡Char (√·IdemLIncl I) (√·IdemRIncl I)

 √·Absorb+LIncl : ∀ (I J : CommIdeal) → √ (I ·i (I +i J)) ⊆ √ I
 √·Absorb+LIncl I J x = map λ (n , x^n∈I[I+J]) → (n , ·iLincl I (I +i J) _ x^n∈I[I+J])

 √·Absorb+RIncl : ∀ (I J : CommIdeal) → √ I ⊆ √ (I ·i (I +i J))
 √·Absorb+RIncl I J x = map λ (n , x^n∈I) → (n +ℕ n , subst-∈ (I ·i (I +i J))
                                (·-of-^-is-^-of-+ x n n) -- x²ⁿ≡xⁿ (∈I) · xⁿ (∈I⊆I+J)
                                (prodInProd I (I +i J) _ _ x^n∈I (+iLincl I J _ x^n∈I)))

 √·Absorb+ : ∀ (I J : CommIdeal) → √ (I ·i (I +i J)) ≡ √ I
 √·Absorb+ I J = CommIdeal≡Char (√·Absorb+LIncl I J) (√·Absorb+RIncl I J)

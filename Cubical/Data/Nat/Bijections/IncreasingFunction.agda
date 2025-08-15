module Cubical.Data.Nat.Bijections.IncreasingFunction where

{- Consider an increasing function f : ℕ → ℕ with f 0 ≡ 0.
-- Note that we can partition ℕ into the pieces [f k , f (suc k) ) for k ∈ ℕ
-- 0=f0 ..... f1 ..... f2 ..... f3 ...
-- [          )[       )[       )[ ...
-- This module formalizes this idea.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open <-Reasoning

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to ex-falso)

private
  kIsUnique : (f : ℕ → ℕ ) → isStrictlyIncreasing f → (n : ℕ) →
              (k  : ℕ) →  ((f k  ≤ n) × (n < f (suc k ))) →
              (k' : ℕ) →  ((f k' ≤ n) × (n < f (suc k'))) →
              k ≡ k'
  kIsUnique f fInc n k (fk≤n , n<fsk ) k' (fk'≤n , n<fsk') = k=k' where
    compare : (l : ℕ) → (l' : ℕ) →
              n < f (suc l) → f l' ≤ n →
              ¬ l < l'
    compare l l' n<fsl fl'≤n l<l' = ¬m<m $
     n
       <≤⟨ n<fsl ⟩
     f (suc l)
       ≤⟨ strictlyIncreasing→Increasing fInc l<l' ⟩
     f l'
       ≤≡⟨ fl'≤n  ⟩
     n ∎

    k=k' : k ≡ k'
    k=k' with k ≟ k'
    ... | lt k<k' = ex-falso (compare k k' n<fsk fk'≤n k<k')
    ... | eq k=k' = k=k'
    ... | gt k'<k = ex-falso (compare k' k n<fsk' fk≤n k'<k)

  approxFunction : (f : ℕ → ℕ) → (f 0 ≡ 0) → isStrictlyIncreasing f →
                   (n : ℕ) → Σ[ k ∈ ℕ ]  (f k ≤ n) × (n < f (suc k))
  approxFunction f f0=0 fInc zero = 0 , f0≤0 , 0<f1 where

    f0≤0 : f 0 ≤ 0
    f0≤0 = ≤-reflexive f0=0

    f0<f1 : f 0 < f 1
    f0<f1 = fInc <-suc

    0<f1 : 0 < f 1
    0<f1 = 0 ≡<⟨ sym f0=0 ⟩ f 0 <≡⟨ f0<f1 ⟩ f 1 ∎

  approxFunction f f0=0 fInc (suc n) = newsol $ f (suc k) ≟ suc n where

    oldsol : Σ[ k ∈ ℕ ] ( (f k ≤ n) ×  (n < f (suc k)))
    oldsol = approxFunction f f0=0 fInc n

    k : ℕ
    k = fst oldsol

    fk≤n : f k ≤ n
    fk≤n = fst (snd oldsol)

    n<fsk : n < f (suc k)
    n<fsk = snd (snd oldsol)

    newsol : Trichotomy (f (suc k)) (suc n) → Σ[ k' ∈ ℕ ] (f k' ≤ suc n) × (suc n < f (suc k'))
    newsol (lt fsk<sn) = ex-falso (¬squeeze< (n<fsk , fsk<sn))
    newsol (eq fsk=sn) = suc k , ≤-reflexive fsk=sn , (
      suc n
        ≡<⟨ sym fsk=sn ⟩
      f (suc k)
        <≡⟨ fInc <-suc ⟩
      f (suc (suc k)) ∎ )
    newsol (gt fsk>sn) = k , (f k
                               ≤⟨ fk≤n ⟩
                              n
                               ≤≡⟨ <-weaken <-suc ⟩
                              suc n ∎) ,            fsk>sn

module _ (f : ℕ → ℕ) (f0=0 : f 0 ≡ 0) (fInc : isStrictlyIncreasing f) where
  nearestValues : (n : ℕ) → ∃![ k ∈ ℕ ] (f k ≤ n) × (n < f (suc k))
  nearestValues n = uniqueExists k p goalIsProp (kIsUnique f fInc n k p) where

    solution : Σ[ k ∈ ℕ ] ( (f k ≤ n) ×  (n < f (suc k)))
    solution = approxFunction f f0=0 fInc n

    k : ℕ
    k = fst solution

    p : (f k ≤ n) × (n < f (suc k))
    p = snd solution

    goalIsProp : (k : ℕ) → isProp ( (f k ≤ n ) × (n < f (suc k)))
    goalIsProp _ = isProp× isProp≤ isProp≤

  partition : Type
  partition = Σ[ k ∈ ℕ ] Σ[ i ∈ ℕ ] i + (f k) < f (suc k)

  partition≅ℕ : Iso partition ℕ
  Iso.fun partition≅ℕ (k , i , _) = i + f k
  Iso.inv partition≅ℕ n = k , i , (
    i + f k
      ≡<⟨ i+fk=n ⟩
    n
      <≡⟨ n<fsk ⟩
    f (suc k) ∎) where
      incApprox = nearestValues n

      k : ℕ
      k = fst (fst incApprox)

      i : ℕ
      i = fst (fst (snd (fst incApprox)))

      i+fk=n : i + f k ≡ n
      i+fk=n = snd (fst (snd (fst incApprox)))

      n<fsk : n < f (suc k)
      n<fsk = snd (snd (fst incApprox))

  Iso.rightInv partition≅ℕ n =
    snd (fst (snd (fst (nearestValues n))))

  Iso.leftInv  partition≅ℕ  y@(k , i , i+fk<fsk) =
    ΣPathP (k'=k , ΣPathPProp (λ a → isProp≤) i'=i) where

      inv = Iso.inv partition≅ℕ
      n   = i + f k

      k'  = fst (inv n)
      i'  = fst (snd (inv n))

      fk≤n : f k ≤ n
      fk≤n = ≤SumRight

      n<fsk : n < f (suc k )
      n<fsk = i+fk<fsk

      ans : (k' , (i' , _ ) , _ ) ≡ (k , (i , _ ) , _ )
      ans = snd (nearestValues n) (k , fk≤n , n<fsk)

      k'=k : k' ≡ k
      k'=k = fst (PathPΣ ans)

      i'=i : i' ≡ i
      i'=i = fst (PathPΣ (fst (PathPΣ (snd (PathPΣ ans)))))

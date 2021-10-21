{-# OPTIONS --safe #-}
module Cubical.Algebra.UpperNat.Base where
{-
  based on:
  https://github.com/DavidJaz/Cohesion/blob/master/UpperNaturals.agda

  and the slides here (for arithmetic operation):
  https://felix-cherubini.de/myers-slides-II.pdf
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Logic
open import Cubical.Functions.Embedding

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.OrderedCommMonoid
open import Cubical.Algebra.OrderedCommMonoid.PropCompletion
open import Cubical.Algebra.OrderedCommMonoid.Instances

open import Cubical.Data.Nat using (ℕ; ·-distribˡ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec)

private
  variable
    ℓ : Level

{- The Upper Naturals
   An upper natural is an upward closed proposition on natural numbers.
   The interpretation is that an upper natural is a natural ``defined by its upper bounds'', in the
   sense that for the proposition N holding of a natural n means that n is an upper bound of N.
   The important bit about upper naturals is that they satisfy the well-ordering principle,
   constructively.

   Example Application:
   The degree of a (constructive!) polynomial may be defined as an upper natural:

     deg(∑_{i=0}^{n} aᵢ · Xⁱ) :≡ λ (k : ℕ) → ∀ (k+1 ≤ i ≤ n) aᵢ≡0
-}

module Construction where
  ℕ↑-+ = PropCompletion ℕ≤+
  ℕ↑-· = PropCompletion ℕ≤·

  open CommMonoidStr (snd ℕ↑-+)
    using ()
    renaming (_·_ to _+_; assoc to +Assoc; comm to +Comm; rid to +Rid)

  open OrderedCommMonoidStr (snd ℕ≤·)
   using (isLMonotone; isRMonotone)

  open OrderedCommMonoidStr (snd ℕ≤+)
   using ()
   renaming (_·_ to _+ℕ_; isLMonotone to +isLMonotone; isRMonotone to +isRMonotone)

  open CommMonoidStr ⦃...⦄
    using (_·_)
    renaming (assoc to ·Assoc; comm to ·Comm; rid to ·Rid)

  private
    instance
      _ : CommMonoidStr _
      _  = snd ℕ↑-·
      _ : CommMonoidStr _
      _ = snd (OrderedCommMonoid→CommMonoid ℕ≤·)

  ℕ↑ : Type₁
  ℕ↑ = fst ℕ↑-+

  open PropCompletion ℓ-zero ℕ≤+
    using (typeAt; pathFromImplications)

  open <-Reasoning using (_≤⟨_⟩_)

  +LDist· : (x y z : ℕ↑) →
            x · (y + z) ≡ (x · y) + (x · z)
  +LDist· x y z =
    pathFromImplications
      (x · (y + z)) ((x · y) + (x · z))
      (⇒) ⇐
    where
      ⇒ : (n : ℕ) → typeAt n (x · (y + z))  → typeAt n ((x · y) + (x · z))
      ⇒ n = propTruncRec
             isPropPropTrunc
             λ {((a , b) , xa , (y+zb , a·b≤n)) →
                 propTruncRec
                   isPropPropTrunc
                   (λ {((a' , b') , ya' , (zb' , a'+b'≤b))
                     → ∣ ((a · a') , (a · b')) ,
                          ∣ (a , a') , (xa , (ya' , ≤-refl)) ∣ ,
                          (∣ (a , b') , (xa , (zb' , ≤-refl)) ∣ ,
                          subst (_≤ n) (sym (·-distribˡ a a' b'))
                            (≤-trans (isLMonotone {z = a} a'+b'≤b) a·b≤n)) ∣ })
                   y+zb}
      ⇐ : (n : ℕ) → _
      ⇐ n = propTruncRec
              isPropPropTrunc
              λ {((a , b) , x·ya , (x·zb , a+b≤n))
                → propTruncRec
                    isPropPropTrunc
                    (λ {((a' , b') , a'x , (b'y , a'·b'≤a))
                    → propTruncRec
                        isPropPropTrunc
                        (λ {((a″ , b″) , a″x , (zb″ , a″·b″≤b))
                          → ∣ ≤CaseInduction {n = a'} {m = a″}
                                (λ a'≤a″ → (a' , (b' +ℕ b″)) , a'x ,
                                           (∣ (b' , b″) , (b'y , (zb″ , ≤-refl)) ∣ ,
                                            (a' · (b' +ℕ b″)       ≤⟨ subst (_≤ (a' · b') +ℕ (a' · b″)) (·-distribˡ a' b' b″) ≤-refl ⟩
                                            (a' · b') +ℕ (a' · b″) ≤⟨ +isRMonotone a'·b'≤a ⟩
                                             a +ℕ (a' · b″)        ≤⟨ +isLMonotone (≤-trans (isRMonotone a'≤a″) a″·b″≤b) ⟩
                                             a+b≤n ))
                                )
                                (λ a″≤a' → (a″ , (b' +ℕ b″)) , (a″x ,
                                           (∣ (b' , b″) , (b'y , (zb″ , ≤-refl)) ∣ ,
                                             ((a″ · (b' +ℕ b″))      ≤⟨ subst (_≤ (a″ · b') +ℕ (a″ · b″)) (·-distribˡ a″ b' b″) ≤-refl ⟩
                                              (a″ · b') +ℕ (a″ · b″) ≤⟨ +isRMonotone ((a″ · b') ≤⟨ isRMonotone a″≤a' ⟩ a'·b'≤a) ⟩
                                              a +ℕ (a″ · b″)         ≤⟨ +isLMonotone a″·b″≤b  ⟩
                                              a+b≤n)))
                                )
                            ∣})
                        x·zb})
                    x·ya}

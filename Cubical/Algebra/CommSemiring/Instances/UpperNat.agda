{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Instances.UpperNat where
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
open import Cubical.Algebra.CommSemiring

open import Cubical.Data.Nat using (ℕ; ·-distribˡ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma

open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ : Level

{- The Upper Naturals
   An upper natural is an upward closed proposition on natural numbers.
   The interpretation is that an upper natural is a natural ``defined by its upper bounds'', in the
   sense that for the proposition N holding of a natural n means that n is an upper bound of N.
   The important bit about upper naturals is that they satisfy the well-ordering principle,
   constructively (no proof of that is given here).

   Example Application:
   The degree of a polynomial P=∑_{i=0}^{n} aᵢ · Xⁱ may be defined as an upper natural:

     deg(P) :≡ (λ n → all non-zero indices have index smaller n)

     Or: deg(∑_{i=0}^{n} aᵢ · Xⁱ) = λ (k : ℕ) → ∀ (k+1 ≤ i ≤ n) aᵢ≡0

   This works even if a constructive definition of polynomial is used.

   However the upper naturals are a bit too unconstraint and do not even form a semiring,
   since they include 'infinity' elements like the proposition that is always false.

   This is different for the subtype of *bounded* upper naturals ℕ↑b.
-}

module ConstructionUnbounded where
  ℕ↑-+ = PropCompletion ℕ≤+
  ℕ↑-· = PropCompletion ℕ≤·

  open OrderedCommMonoidStr (snd ℕ↑-+)
    hiding (_≤_; MonotoneL; MonotoneR)
    renaming (·Assoc to +Assoc; ·Comm to +Comm; ·IdR to +Rid;
              _·_ to _+_; ε to 0↑)

  open OrderedCommMonoidStr (snd ℕ≤·)
   using (MonotoneL; MonotoneR)

  open OrderedCommMonoidStr (snd ℕ≤+)
   hiding (_≤_)
   renaming (_·_ to _+ℕ_;
             MonotoneL to +MonotoneL; MonotoneR to +MonotoneR;
             ·Comm to ℕ+Comm)

  open OrderedCommMonoidStr ⦃...⦄
    using (_·_ ; ·Assoc ; ·Comm )
    renaming (·IdR to ·Rid)

  private
    instance
      _ : OrderedCommMonoidStr _ _
      _  = snd ℕ↑-·
      _ : OrderedCommMonoidStr _ _
      _ = snd ℕ≤·

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
      ⇒ n = PT.rec
             isPropPropTrunc
             λ {((a , b) , xa , (y+zb , a·b≤n)) →
                 PT.rec
                   isPropPropTrunc
                   (λ {((a' , b') , ya' , (zb' , a'+b'≤b))
                     → ∣ ((a · a') , (a · b')) ,
                          ∣ (a , a') , (xa , (ya' , ≤-refl)) ∣₁ ,
                          (∣ (a , b') , (xa , (zb' , ≤-refl)) ∣₁ ,
                          subst (_≤ n) (sym (·-distribˡ a a' b'))
                            (≤-trans (MonotoneL {z = a} a'+b'≤b) a·b≤n)) ∣₁ })
                   y+zb}

      ⇐ : (n : ℕ) → _
      ⇐ n =
        PT.rec
          isPropPropTrunc
          λ {((a , b) , x·ya , (x·zb , a+b≤n))
          → PT.rec
              isPropPropTrunc
              (λ {((a' , b') , a'x , (b'y , a'·b'≤a))
              → PT.rec
                  isPropPropTrunc
                  (λ {((a″ , b″) , a″x , (zb″ , a″·b″≤b))
                  → ∣ ≤CaseInduction {n = a'} {m = a″}
                        (λ a'≤a″ →
                          (a' , (b' +ℕ b″)) , a'x ,

                          (∣ (b' , b″) , (b'y , (zb″ , ≤-refl)) ∣₁ ,
                           (a' · (b' +ℕ b″)       ≤⟨ subst
                                                       (_≤ (a' · b') +ℕ (a' · b″))
                                                       (·-distribˡ a' b' b″) ≤-refl ⟩
                           (a' · b') +ℕ (a' · b″) ≤⟨ +MonotoneR a'·b'≤a ⟩
                            a +ℕ (a' · b″)        ≤⟨ +MonotoneL
                                                       (≤-trans (MonotoneR a'≤a″) a″·b″≤b) ⟩
                            a+b≤n ))
                        )
                        (λ a″≤a' →
                         (a″ , (b' +ℕ b″)) , (a″x ,
                         (∣ (b' , b″) , (b'y , (zb″ , ≤-refl)) ∣₁ ,
                           ((a″ · (b' +ℕ b″))      ≤⟨ subst
                                                        (_≤ (a″ · b') +ℕ (a″ · b″))
                                                        (·-distribˡ a″ b' b″) ≤-refl ⟩
                            (a″ · b') +ℕ (a″ · b″) ≤⟨ +MonotoneR
                                                        ((a″ · b') ≤⟨ MonotoneR a″≤a' ⟩ a'·b'≤a) ⟩
                            a +ℕ (a″ · b″)         ≤⟨ +MonotoneL a″·b″≤b  ⟩
                            a+b≤n)))
                        )
                    ∣₁})
                  x·zb})
              x·ya}


module ConstructionBounded where
  ℕ↑-+b = BoundedPropCompletion ℕ≤+
  ℕ↑-·b = BoundedPropCompletion ℕ≤·

  open OrderedCommMonoidStr (snd ℕ≤+)
    renaming (_·_ to _+ℕ_; ·IdR to +IdR; ·Comm to ℕ+Comm)
  open OrderedCommMonoidStr (snd ℕ↑-+b)
    renaming (_·_ to _+_; ε to 0↑)

  open OrderedCommMonoidStr (snd ℕ↑-·b)
    using (_·_)

  open PropCompletion ℓ-zero ℕ≤+
    using (typeAt; pathFromImplications)

  ℕ↑b : Type₁
  ℕ↑b = fst ℕ↑-+b

  AnnihilL : (x : ℕ↑b) → 0↑ · x ≡ 0↑
  AnnihilL x =
    Σ≡Prop (λ s → PropCompletion.isPropIsBounded ℓ-zero ℕ≤+ s)
           (pathFromImplications (fst (0↑ · x)) (fst 0↑) (⇒) ⇐)
    where
     ⇒ : (n : ℕ) → typeAt n (fst (0↑ · x)) → typeAt n (fst 0↑)
     ⇒ n _ = n , ℕ+Comm n 0
     ⇐ : (n : ℕ) → typeAt n (fst 0↑) → typeAt n (fst (0↑ · x))
     ⇐ n _ =
       PT.rec
         isPropPropTrunc
         (λ {(m , mIsUpperBound) → ∣ (0 , m) , ((0 , refl) , (mIsUpperBound , n ,  +IdR n)) ∣₁})
         (snd x)


  asCommSemiring : CommSemiring (ℓ-suc ℓ-zero)
  asCommSemiring .fst = ℕ↑b
  asCommSemiring .snd = str
    where
      module CS = CommSemiringStr
      open IsCommMonoid
      +IsCM = OrderedCommMonoidStr.isCommMonoid (snd ℕ↑-+b)
      ·IsCM = OrderedCommMonoidStr.isCommMonoid (snd ℕ↑-·b)

      str : CommSemiringStr ℕ↑b
      CS.0r str = 0↑
      CS.1r str = OrderedCommMonoidStr.ε (snd ℕ↑-·b)
      CS._+_ str = _+_
      CS._·_ str = _·_
      CS.isCommSemiring str =
        makeIsCommSemiring
          (is-set +IsCM)
          (·Assoc +IsCM) (·IdR +IsCM) (·Comm +IsCM)
          (·Assoc ·IsCM) (·IdR ·IsCM)
          (λ x y z → Σ≡Prop (λ s → PropCompletion.isPropIsBounded ℓ-zero ℕ≤+ s)
                     (ConstructionUnbounded.+LDist· (fst x) (fst y) (fst z)))
          AnnihilL
          (·Comm ·IsCM)

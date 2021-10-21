{-# OPTIONS --safe #-}
module Cubical.Algebra.OrderedCommMonoid.PropCompletion where
{-
  The completion of an ordered monoid, viewd as monoidal prop-enriched category.
  This is used in the construction of the upper naturals, which is an idea of David
  Jaz Myers presented here

  https://felix-cherubini.de/myers-slides-II.pdf

  It should be straight forward, but tedious,
  to generalize this to enriched monoidal categories.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Functions.Logic
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec)

open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.OrderedCommMonoid.Base

open import Cubical.Relation.Binary.Poset

private
  variable
    ℓ : Level

module PropCompletion (ℓ : Level) (M : OrderedCommMonoid ℓ ℓ) where
  open OrderedCommMonoidStr (snd M)
  _≤p_ : fst M → fst M → hProp ℓ
  n ≤p m = (n ≤ m) , (is-prop-valued _ _)

  isUpwardClosed : (s : fst M → hProp ℓ) → Type _
  isUpwardClosed s = (n m : fst M) → n ≤ m → fst (s n) → fst (s m)

  isPropUpwardClosed : (N : fst M → hProp ℓ) → isProp (isUpwardClosed N)
  isPropUpwardClosed N =
    isPropΠ4 (λ _ m _ _ → snd (N m))

  isSetM→Prop : isSet (fst M → hProp ℓ)
  isSetM→Prop = isOfHLevelΠ 2 λ _ → isSetHProp

  M↑ : Type _
  M↑ = Σ[ s ∈ (fst M → hProp ℓ)] isUpwardClosed s

  isSetM↑ : isSet M↑
  isSetM↑ = isOfHLevelΣ 2 isSetM→Prop λ s → isOfHLevelSuc 1 (isPropUpwardClosed s)

  _isUpperBoundOf_ : fst M → M↑ → hProp ℓ
  n isUpperBoundOf s = (fst s) n

  _^↑ : fst M → M↑
  n ^↑ = n ≤p_ , isUpwardClosed≤
    where
      isUpwardClosed≤ : {m : fst M} → isUpwardClosed (m ≤p_)
      isUpwardClosed≤ = λ {_ _ n≤k m≤n → is-trans _ _ _ m≤n n≤k}

  1↑ : M↑
  1↑ = 1m ^↑

  _·↑_ : M↑ → M↑ → M↑
  s ·↑ l = seq , seqIsUpwardClosed
         where
           seq : fst M → hProp ℓ
           seq n = (∃[ (a , b) ∈ (fst M) × (fst M) ] fst ((fst s a) ⊓ (fst l b) ⊓ ((a · b) ≤p n) )) ,
                   isPropPropTrunc
           seqIsUpwardClosed : isUpwardClosed seq
           seqIsUpwardClosed n m n≤m =
             propTruncRec
               isPropPropTrunc
               λ {((a , b) , wa , (wb , a·b≤n)) → ∣ (a , b) , wa , (wb , is-trans _ _ _ a·b≤n n≤m) ∣}

  {- convenience functions for the proof that ·↑ is the multiplication of a monoid -}
  typeAt : fst M → M↑ → Type _
  typeAt n s = fst (fst s n)

  M↑Path : {s l : M↑} → ((n : fst M) → typeAt n s ≡ typeAt n l) → s ≡ l
  M↑Path {s = s} {l = l} pwPath = path
     where
       seqPath : fst s ≡ fst l
       seqPath i n = subtypePathReflection (λ A → isProp A , isPropIsProp)
                                           (fst s n)
                                           (fst l n)
                                           (pwPath n) i
       path : s ≡ l
       path = subtypePathReflection (λ s → isUpwardClosed s , isPropUpwardClosed s) s l seqPath

  pathFromImplications : (s l : M↑)
           → ((n : fst M) → typeAt n s → typeAt n l)
           → ((n : fst M) → typeAt n l → typeAt n s)
           → s ≡ l
  pathFromImplications s l s→l l→s =
      M↑Path λ n → cong fst (propPath n)
            where propPath : (n : fst M) → fst s n ≡ fst l n
                  propPath n = ⇒∶ s→l n
                               ⇐∶ l→s n

  ·↑Comm : (s l : M↑) → s ·↑ l ≡ l ·↑ s
  ·↑Comm s l = M↑Path λ n → cong fst (propPath n)
    where implication : (s l : M↑) (n : fst M) → fst (fst (s ·↑ l) n) → fst (fst (l ·↑ s) n)
          implication s l n = propTruncRec
                             isPropPropTrunc
                             (λ {((a , b) , wa , (wb , a·b≤n))
                               → ∣ (b , a) , wb , (wa , subst (λ k → fst (k ≤p n)) (comm a b) a·b≤n) ∣ })
          propPath : (n : fst M) → fst (s ·↑ l) n ≡ fst (l ·↑ s) n
          propPath n = ⇒∶ implication s l n
                       ⇐∶ implication l s n

  ·↑Rid : (s : M↑) → s ·↑ 1↑ ≡ s
  ·↑Rid s = pathFromImplications (s ·↑ 1↑) s (⇒) ⇐
    where ⇒ : (n : fst M) → typeAt n (s ·↑ 1↑) → typeAt n s
          ⇒ n = propTruncRec (snd (fst s n))
                             (λ {((a , b) , sa , (1b , a·b≤n))
                                  → (snd s) a n ( subst (_≤ n) (rid a) (is-trans _ _ _ (isLMonotone 1b) a·b≤n)) sa })
          ⇐ : (n : fst M) → typeAt n s → typeAt n (s ·↑ 1↑)
          ⇐ n = λ sn → ∣ (n , 1m) , (sn , (is-refl _ , subst (_≤ n) (sym (rid n)) (is-refl _))) ∣

  ·↑Assoc : (s l k : M↑) → s ·↑ (l ·↑ k) ≡ (s ·↑ l) ·↑ k
  ·↑Assoc s l k = pathFromImplications (s ·↑ (l ·↑ k)) ((s ·↑ l) ·↑ k) (⇒) ⇐
    where ⇒ : (n : fst M) → typeAt n (s ·↑ (l ·↑ k)) → typeAt n ((s ·↑ l) ·↑ k)
          ⇒ n = propTruncRec
                isPropPropTrunc
                λ {((a , b) , sa , (l·kb , a·b≤n))
                     → propTruncRec
                         isPropPropTrunc
                         (λ {((a' , b') , la' , (kb' , a'·b'≤b))
                         → ∣ ((a · a') , b') , ∣ (a , a') , (sa , (la' , is-refl _)) ∣ , kb' ,
                             (let a·⟨a'·b'⟩≤n = (is-trans _ _ _ (isLMonotone a'·b'≤b) a·b≤n)
                              in subst (_≤ n) (assoc a a' b') a·⟨a'·b'⟩≤n) ∣
                            }) l·kb
                   }
          ⇐ : _
          ⇐ n = propTruncRec
                isPropPropTrunc
                λ {((a , b) , s·l≤a , (k≤b , a·b≤n))
                     → propTruncRec
                         isPropPropTrunc
                         (λ {((a' , b') , s≤a' , (l≤b' , a'·b'≤a))
                         → ∣ (a' , b' · b) , s≤a' , ( ∣ (b' , b) , l≤b' , (k≤b , is-refl _) ∣ ,
                             (let ⟨a'·b'⟩·b≤n = (is-trans _ _ _ (isRMonotone a'·b'≤a) a·b≤n)
                              in subst (_≤ n) (sym (assoc a' b' b)) ⟨a'·b'⟩·b≤n) ) ∣
                            }) s·l≤a
                   }

  asCommMonoid : CommMonoid (ℓ-suc ℓ)
  asCommMonoid = makeCommMonoid 1↑ _·↑_ isSetM↑ ·↑Assoc ·↑Rid ·↑Comm

  {-
    Poset structure on M↑
  -}
  _≤↑_ : (s l : M↑) → Type _
  s ≤↑ l = (m : fst M) → fst ((fst s) m) → fst ((fst l) m)

  ≤↑IsProp : (s l : M↑) → isProp (s ≤↑ l)
  ≤↑IsProp s l = isPropΠ2 (λ x p → snd (fst l x))

  ≤↑IsRefl : {s : M↑} → s ≤↑ s
  ≤↑IsRefl = λ m x → x

  ≤↑IsTrans : {s l t : M↑} → s ≤↑ l → l ≤↑ t → s ≤↑ t
  ≤↑IsTrans p q x = (q x) ∘ (p x)

  ≤↑IsAntisym : {s l : M↑} → s ≤↑ l → l ≤↑ s → s ≡ l
  ≤↑IsAntisym p q = pathFromImplications _ _ p q

PropCompletion : OrderedCommMonoid ℓ ℓ → CommMonoid (ℓ-suc ℓ)
PropCompletion M = PropCompletion.asCommMonoid _ M

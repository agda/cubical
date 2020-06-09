{-

Definition of the Klein bottle as a HIT

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.KleinBottle.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Int public renaming (_+_ to _+Int_ ; +-assoc to +Int-assoc; +-comm to +Int-comm)
open import Cubical.Data.Sigma
open import Cubical.HITs.S1
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.HITs.KleinBottle.Base

loop1 : S¹ → KleinBottle
loop1 base = point
loop1 (loop i) = line1 i

invS¹Loop : S¹ → Set
invS¹Loop base = S¹
invS¹Loop (loop i) = invS¹Path i

loop1Inv : (s : S¹) → loop1 (inv s) ≡ loop1 s
loop1Inv base = line2
loop1Inv (loop i) = square i

twist : (s : S¹) → PathP (λ i → invS¹Path i) s (inv s)
twist s i = glue (λ {(i = i0) → s; (i = i1) → inv s}) (inv s)

twistBaseLoop : (s : S¹) → invS¹Loop s
twistBaseLoop base = base
twistBaseLoop (loop i) = twist base i

kleinBottle≃Σ : KleinBottle ≃ Σ S¹ invS¹Loop
kleinBottle≃Σ = isoToEquiv (iso fro to froTo toFro)
  where
  fro : KleinBottle → Σ S¹ invS¹Loop
  fro point = (base , base)
  fro (line1 i) = (base , loop i)
  fro (line2 j) = (loop (~ j) , twist base (~ j))
  fro (square i j) = (loop (~ j) , twist (loop i) (~ j))

  toLoopFiller : (j : I) → ua invS¹Equiv j → I → KleinBottle
  toLoopFiller j g l =
    hfill
      (λ l → λ
        { (j = i0) → loop1Inv g l
        ; (j = i1) → loop1 g
        })
      (inS (loop1 (unglue (j ∨ ~ j) g)))
      l

  to : Σ S¹ invS¹Loop → KleinBottle
  to (base , s) = loop1 s
  to (loop j , g) = toLoopFiller j g i1

  toFro : (a : KleinBottle) → to (fro a) ≡ a
  toFro point = refl
  toFro (line1 i) = refl
  toFro (line2 j) k = lUnit line2 (~ k) j
  toFro (square i j) k = lUnit (square i) (~ k) j

  froLoop1 : (s : S¹) → fro (loop1 s) ≡ (base , s)
  froLoop1 base = refl
  froLoop1 (loop i) = refl

  froLoop1Inv :
    PathP (λ k → (s : S¹) → froLoop1 (inv s) k ≡ froLoop1 s k)
      (λ s l → fro (loop1Inv s l))
      (λ s l → loop (~ l) , twist s (~ l))
  froLoop1Inv k base l = loop (~ l) , twist base (~ l)
  froLoop1Inv k (loop i) l = loop (~ l) , twist (loop i) (~ l)

  froTo : (a : Σ S¹ invS¹Loop) → fro (to a) ≡ a
  froTo (base , s) = froLoop1 s
  froTo (loop j , g) k =
    hcomp
      (λ l → λ
        { (j = i0) → froLoop1Inv k g l
        ; (j = i1) → froLoop1 g k
        ; (k = i0) → fro (toLoopFiller j g l)
        ; (k = i1) →
          ( loop (j ∨ ~ l)
          , glue
             (λ
               { (j = i0) (l = i1) → g
               ; (j = i1) → g
               ; (l = i0) → unglue (j ∨ ~ j) g
               })
             (unglue (j ∨ ~ j) g)
          )
        })
      (froLoop1 (unglue (j ∨ ~ j) g) k)

isGroupoidKleinBottle : isGroupoid KleinBottle
isGroupoidKleinBottle =
  transport (λ i → isGroupoid (ua kleinBottle≃Σ (~ i)))
    (isOfHLevelΣ 3 isGroupoidS¹
      (λ s →
        PropTrunc.rec
          (isPropIsOfHLevel 3)
          (λ p → subst (λ s → isGroupoid (invS¹Loop s)) p isGroupoidS¹)
          (isConnectedS¹ s)))

-- Transport across the following is too slow :(

ΩKlein≡Int² : Path KleinBottle point point ≡ Int × Int
ΩKlein≡Int² =
  Path KleinBottle point point
    ≡⟨ (λ i → basePath i ≡ basePath i) ⟩
  Path (Σ S¹ invS¹Loop) (base , base) (base , base)
    ≡⟨ sym ΣPath≡PathΣ ⟩
  Σ ΩS¹ (λ p → PathP (λ j → invS¹Loop (p j)) base base)
    ≡⟨ (λ i → Σ ΩS¹ (λ p → PathP (λ j → invS¹Loop (p (j ∨ i))) (twistBaseLoop (p i)) base)) ⟩
  ΩS¹ × ΩS¹
    ≡⟨ (λ i → ΩS¹≡Int i × ΩS¹≡Int i) ⟩
  Int × Int ∎
  where
  basePath : PathP (λ i → ua kleinBottle≃Σ i) point (base , base)
  basePath i = glue (λ {(i = i0) → point; (i = i1) → base , base}) (base , base)

-- We can at least define the winding function directly and get results on small examples

windingKlein : Path KleinBottle point point → Int × Int
windingKlein p = (z₀ , z₁)
  where
  step₀ : Path (Σ S¹ invS¹Loop) (base , base) (base , base)
  step₀ = (λ i → kleinBottle≃Σ .fst (p i))

  z₀ : Int
  z₀ = winding (λ i → kleinBottle≃Σ .fst (p i) .fst)

  z₁ : Int
  z₁ = winding
    (transport
      (λ i → PathP (λ j → invS¹Loop (step₀ (j ∨ i) .fst)) (twistBaseLoop (step₀ i .fst)) base)
      (cong snd step₀))

_ : windingKlein line1 ≡ (pos 0 , pos 1)
_ = refl

_ : windingKlein line2 ≡ (negsuc 0 , pos 0)
_ = refl

_ : windingKlein (line1 ∙ line2) ≡ (negsuc 0 , negsuc 0)
_ = refl

_ : windingKlein (line1 ∙ line2 ∙ line1) ≡ (negsuc 0 , pos 0)
_ = refl

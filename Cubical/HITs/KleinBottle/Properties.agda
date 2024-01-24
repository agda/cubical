{-

Definition of the Klein bottle as a HIT

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.KleinBottle.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.HITs.S1 hiding (rec)
open import Cubical.HITs.PropositionalTruncation as PropTrunc hiding (rec)

open import Cubical.HITs.KleinBottle.Base

rec : ∀ {ℓ} {A : Type ℓ} (x : A)
     (l1 l2 : x ≡ x)
  → Square l2 l2 (sym l1) l1
  → KleinBottle → A
rec x l1 l2 sq point = x
rec x l1 l2 sq (line1 i) = l1 i
rec x l1 l2 sq (line2 i) = l2 i
rec x l1 l2 sq (square i i₁) = sq i i₁

elimSet : ∀ {ℓ} {A : KleinBottle → Type ℓ}
  → ((x : _) → isSet (A x))
  → (a₀ : A point)
  → (l1 : PathP (λ i → A (line1 i)) a₀ a₀)
  → (l2 : PathP (λ i → A (line2 i)) a₀ a₀)
  → (x : _) → A x
elimSet set a₀ l1 l2 point = a₀
elimSet set a₀ l1 l2 (line1 i) = l1 i
elimSet set a₀ l1 l2 (line2 i) = l2 i
elimSet {A = A} set a₀ l1 l2 (square i j) = h i j
  where
  h : SquareP (λ i j → A (square i j)) l2 l2 (symP l1) l1
  h = toPathP (isOfHLevelPathP' 1 (set _) _ _ _ _)

elimProp : ∀ {ℓ} {A : KleinBottle → Type ℓ}
  → ((x : _) → isProp (A x))
  → (a₀ : A point)
  → (x : _) → A x
elimProp prop a₀ =
  elimSet (λ _ → isProp→isSet (prop _))
    a₀
    (isProp→PathP (λ _ → prop _) _ _)
    (isProp→PathP (λ _ → prop _) _ _)

K²FunCharacIso : ∀ {ℓ} {A : KleinBottle → Type ℓ}
  → Iso ((x : KleinBottle) → A x)
         (Σ[ x ∈ A point ]
           Σ[ p ∈ PathP (λ i → A (line1 i)) x x ]
           (Σ[ q ∈ PathP (λ i → A (line2 i)) x x ]
             SquareP (λ i j → A (square i j))
               q q (λ i → p (~ i)) p))
Iso.fun K²FunCharacIso f =
  f point , cong f line1 , cong f line2 , λ i j → f (square i j)
Iso.inv K²FunCharacIso (a , p1 , p2 , sq) point = a
Iso.inv K²FunCharacIso (a , p1 , p2 , sq) (line1 i) = p1 i
Iso.inv K²FunCharacIso (a , p1 , p2 , sq) (line2 i) = p2 i
Iso.inv K²FunCharacIso (a , p1 , p2 , sq) (square i j) = sq i j
Iso.rightInv K²FunCharacIso _ = refl
Iso.leftInv K²FunCharacIso f =
  funExt λ { point → refl ; (line1 i) → refl
          ; (line2 i) → refl ; (square i i₁) → refl}

loop1 : S¹ → KleinBottle
loop1 base = point
loop1 (loop i) = line1 i

invS¹Loop : S¹ → Type
invS¹Loop base = S¹
invS¹Loop (loop i) = invS¹Path i

loop1Inv : (s : S¹) → loop1 (invLooper s) ≡ loop1 s
loop1Inv base = line2
loop1Inv (loop i) = square i

twist : (s : S¹) → PathP (λ i → invS¹Path i) s (invLooper s)
twist s i = glue (λ {(i = i0) → s; (i = i1) → invLooper s}) (invLooper s)

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
    PathP (λ k → (s : S¹) → froLoop1 (invLooper s) k ≡ froLoop1 s k)
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

ΩKlein≡ℤ² : Path KleinBottle point point ≡ ℤ × ℤ
ΩKlein≡ℤ² =
  Path KleinBottle point point
    ≡⟨ (λ i → basePath i ≡ basePath i) ⟩
  Path (Σ S¹ invS¹Loop) (base , base) (base , base)
    ≡⟨ sym ΣPath≡PathΣ ⟩
  Σ ΩS¹ (λ p → PathP (λ j → invS¹Loop (p j)) base base)
    ≡⟨ (λ i → Σ ΩS¹ (λ p → PathP (λ j → invS¹Loop (p (j ∨ i))) (twistBaseLoop (p i)) base)) ⟩
  ΩS¹ × ΩS¹
    ≡⟨ (λ i → ΩS¹≡ℤ i × ΩS¹≡ℤ i) ⟩
  ℤ × ℤ ∎
  where
  basePath : PathP (λ i → ua kleinBottle≃Σ i) point (base , base)
  basePath i = glue (λ {(i = i0) → point; (i = i1) → base , base}) (base , base)

-- We can at least define the winding function directly and get results on small examples

windingKlein : Path KleinBottle point point → ℤ × ℤ
windingKlein p = (z₀ , z₁)
  where
  step₀ : Path (Σ S¹ invS¹Loop) (base , base) (base , base)
  step₀ = (λ i → kleinBottle≃Σ .fst (p i))

  z₀ : ℤ
  z₀ = winding (λ i → kleinBottle≃Σ .fst (p i) .fst)

  z₁ : ℤ
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

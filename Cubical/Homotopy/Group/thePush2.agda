{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.thePush2 where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.HITs.Truncation renaming (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)
thePush = Pushout {A = S₊∙ 2 ⋁ S₊∙ 2} ⋁↪ fold⋁

open import Cubical.HITs.S2
open import Cubical.HITs.S3

suspFun3 : S² → typ (Ω (S³ , base))
suspFun3 base = refl
suspFun3 (surf i j) k = surf i j k

S²wedge : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → ((x y : _) → isOfHLevel 4 (P x y))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → l base ≡ r base
         → (x y : _) → P x y
S²wedge {P = P} hlev l r p base y = r y
S²wedge {P = P} hlev l r p (surf i i₁) y = help y i i₁
  where
  help : (y : S²) → SquareP (λ i j → P (surf i j) y)
                     (λ _ → r y) (λ _ → r y)
                     (λ _ → r y) λ _ → r y
  help =
    S²ToSetRec (λ _ → isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (hlev _ _) _ _) _ _)
               λ w j → hcomp (λ k → λ { (j = i0) → p k
                                        ; (j = i1) → p k
                                        ; (w = i0) → p k
                                        ; (w = i1) → p k})
                              (l (surf w j))

S²wedge≡ : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → (h : ((x y : _) → isOfHLevel 4 (P x y)))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → (p : l base ≡ r base)
         → (x : S²) → S²wedge h l r p x base ≡ l x
S²wedge≡ h l r p base = sym p
S²wedge≡ h l r p (surf i j) k =
  hcomp (λ w → λ {(i = i0) → p (~ k ∧ w)
                 ; (i = i1) → p (~ k ∧ w)
                 ; (j = i0) → p (~ k ∧ w)
                 ; (j = i1) → p (~ k ∧ w)
                 ; (k = i1) → l (surf i j)})
        (l (surf i j))

thePush' : Type
thePush' = Pushout {A = (S² , base) ⋁ (S² , base)} ⋁↪ fold⋁

thePush'∥ = hLevelTrunc 5 thePush'

ΩS³ = typ ((Ω^ 3) (S³ , base))

S²act : (x y : S²)
  → Square {A = thePush'∥} (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
S²act =
  S²wedge
    (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
    (λ x → λ i j → ∣ inl (x , surf i j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf i j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf i j)) (~ k)
                               ; (r = i1) → push (inl (surf i j)) (~ k)})
                     (inr (surf i j)) ∣ₕ

S²actId : (x : S²) → S²act x base ≡  λ i j → ∣ inl (x , surf i j) ∣ₕ
S²actId =
  S²wedge≡
    (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
    (λ x → λ i j → ∣ inl (x , surf i j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf i j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf i j)) (~ k)
                               ; (r = i1) → push (inl (surf i j)) (~ k)})
                     (inr (surf i j)) ∣ₕ

μ1 : (x y : S²) → thePush'∥
μ1 x y = ∣ inl (x , y) ∣ₕ

movep' : (y : S²) → Path thePush' (inl (y , base)) (inl (base , y))
movep' y i = (push (inl y) ∙ sym (push (inr y))) i

movep'∙ : movep' base ≡ refl
movep'∙ = (λ k i → (push (inl base) ∙ sym (push (push tt (~ k)))) i)
          ∙ rCancel (push (inl base))

movep-coh2 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) (r : p ≡ q)
           → Cube {A = A}
                   (λ j k → compPath-filler p (sym q) (~ k) j) (λ k j → q (k ∧ j))
                   (λ i k → x) (λ i k → q k)
                   (((λ k → p ∙ sym (r (~ k))) ∙ rCancel p))
                   r
movep-coh2 {A = A} {x = x} {y = y} =
  J (λ y p → (q : x ≡ y) (r : p ≡ q)
           → Cube {A = A}
                   (λ j k → compPath-filler p (sym q) (~ k) j) (λ k j → q (k ∧ j))
                   (λ i k → x) (λ i k → q k)
                   (((λ k → p ∙ sym (r (~ k))) ∙ rCancel p))
                   r)
    λ q → J (λ q r → Cube (λ j k → compPath-filler refl (λ i → q (~ i)) (~ k) j)
                            (λ k j → q (k ∧ j)) (λ i k → x) (λ i k → q k)
                            ((λ k → refl ∙ (λ i → r (~ k) (~ i))) ∙ rCancel refl) r)
             ((λ z j k → lUnit (sym (rUnit (λ _ → x))) z k j)
             ◁ (λ i j k → (refl ∙ (λ i₁ → rUnit (λ _ → x) (~ i₁))) (k ∨ i) j))

{-
i = i0 ⊢ ∣
         compPath-filler (push (inl base)) (λ i₁ → push (inr base) (~ i₁))
         (~ k) j
         ∣
i = i1 ⊢ ∣ push (inr base) (k ∧ j) ∣
j = i0 ⊢ ∣ inl (pt (S² , base) , pt (S² , base)) ∣
j = i1 ⊢ ∣ push (inr base) k ∣
k = i0 ⊢ ∣ movep'∙ i j ∣
k = i1 ⊢ ∣ push (push a i) j ∣
-}

coh : I → I → I → I → thePush'
coh r i j k =
  hfill (λ r → λ { (i = i0) → movep'∙ (~ r) k
                               ; (i = i1) → movep'∙ (~ r) k
                               ; (j = i0) → movep'∙ (~ r) k
                               ; (j = i1) → movep'∙ (~ r) k
                               ; (k = i0) → inl (surf i j , base)
                               ; (k = i1) → inl (surf i j , base)})
                     (inS (inl (surf i j , base)))
                     r

sideLem : (y : S²)
        → Cube {A = thePush'∥}
                (λ j k → ∣ movep' y k ∣) (λ j k → ∣ movep' y k ∣)
                (λ j k → ∣ movep' y k ∣) (λ j k → ∣ movep' y k ∣)
                (S²act y (pt (S² , base)))
                λ i j → ∣ inl (surf i j , y) ∣
sideLem =
  S²ToSetRec (λ _ → isOfHLevelPathP' 2
              (isOfHLevelPathP' 3
                (isOfHLevelPathP' 4 (isOfHLevelTrunc 5) _ _) _ _) _ _)
   λ i j k → ∣ coh i1 i j k ∣ₕ

pushact : (x : S²) → thePush' → thePush'∥
pushact base (inl y) = ∣ inl y ∣
pushact (surf i j) (inl y) = S²act (fst y) (snd y) i j
pushact base (inr z) = ∣ inl (base , z) ∣ₕ
pushact (surf i i₁) (inr z) = ∣ inl (surf i i₁ , z) ∣ₕ
pushact base (push (inl y) k) = ∣ (push (inl y) ∙ sym (push (inr y))) k ∣
pushact (surf i j) (push (inl y) k) = sideLem y i j k
pushact base (push (inr y) i) = ∣ inl (base , y) ∣
pushact (surf i j) (push (inr y) k) = ∣ inl (surf i j , y) ∣
pushact base (push (push a i₁) i) = ∣ movep'∙ i₁ i ∣
pushact (surf i j) (push (push a k) l) =
  ∣ hcomp (λ r → λ { (i = i0) → movep'∙ (k ∨ ~ r) l
                  ; (i = i1) → movep'∙ (k ∨ ~ r) l
                  ; (j = i0) → movep'∙ (k ∨ ~ r) l
                  ; (j = i1) → movep'∙ (k ∨ ~ r) l
                  ; (k = i0) → coh r i j l
                  ; (k = i1) → inl (surf i j , base)
                  ; (l = i0) → inl (surf i j , base)
                  ; (l = i1) → inl (surf i j , base)})
        (inl (surf i j , base)) ∣ₕ

pushact≡idfun : (x : _) → pushact base x ≡ ∣ x ∣
pushact≡idfun (inl x) = refl
pushact≡idfun (inr x) = cong ∣_∣ₕ (push (inr x))
pushact≡idfun (push (inl x) i) j =
  ∣ compPath-filler (push (inl x)) (λ i₁ → push (inr x) (~ i₁)) (~ j) i  ∣ₕ
pushact≡idfun (push (inr x) i) j = ∣ push (inr x) (j ∧ i) ∣
pushact≡idfun (push (push a i) j) k =
  ∣ movep-coh2 {A = thePush'} (push (inl base)) (push (inr base)) (λ k → push (push tt k)) i j k ∣ₕ

push→ : (x : S²) → thePush'∥ → thePush'∥
push→ x = trRec (isOfHLevelTrunc 5) (pushact x)
isEq-pushAct : (x : _) → isEquiv (push→ x)
isEq-pushAct =
  S²ToSetRec (λ _ → isProp→isSet (isPropIsEquiv _))
    (subst isEquiv (funExt id≡) (idIsEquiv _))
  where
  id≡ : (x : _) → x ≡ push→ base x
  id≡ = trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _) (sym ∘ pushact≡idfun)

pushact⁻ : (x : S²) → thePush' → thePush'∥
pushact⁻ base y = pushact base y
pushact⁻ (surf i j) y = pushact (surf (~ i) j) y

push← : (x : S²) → thePush'∥ → thePush'∥
push← x = trRec (isOfHLevelTrunc 5) (pushact⁻ x)

module _ {ℓ : Level} {P : thePush' → Type ℓ} (hlev : ((x : thePush') → isSet (P x)))
         (b : P (inl (base , base))) where
  private
    ×fun : (x y : S²) → P (inl (x , y))
    ×fun = S²ToSetRec (λ _ → isSetΠ (λ _ → hlev _))
            (S²ToSetRec (λ _ → hlev _) b)

    inrfun : (x : S²) → P (inr x)
    inrfun = S²ToSetRec (λ _ → hlev _) (subst P (push (inl base)) b)

    inl-pp : (x : S²) → PathP (λ i → P (push (inl x) i)) (×fun x base) (inrfun x)
    inl-pp = S²ToSetRec (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              λ j → transp (λ i → P (push (inl base) (i ∧ j))) (~ j) b

    inr-pp : (x : S²) → PathP (λ i → P (push (inr x) i)) (×fun base x) (inrfun x)
    inr-pp = S²ToSetRec (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              (transport (λ j → PathP (λ i → P (push (push tt j) i)) (×fun base base)
                                       (inrfun base))
              (inl-pp base))

  thePush→Set : (x : thePush') → P x
  thePush→Set (inl x) = ×fun (fst x) (snd x)
  thePush→Set (inr x) = inrfun x
  thePush→Set (push (inl x) i) = inl-pp x i
  thePush→Set (push (inr x) i) = inr-pp x i
  thePush→Set (push (push a j) i) = help j i
    where
    help : SquareP (λ j i → P (push (push tt j) i))
                   (λ i → inl-pp base i)
                   (λ i → inr-pp base i)
                   (λ _ → ×fun base base)
                   (λ _ → inrfun base)
    help = toPathP (isProp→PathP (λ _ → isOfHLevelPathP' 1 (hlev _) _ _) _ _)

cancel : (x : S²) (y : thePush'∥) → push→ x (push← x y) ≡ y
cancel x =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
         (h x)
  where
  h : (x : S²) (a : thePush') → push→ x (push← x ∣ a ∣) ≡ ∣ a ∣
  h base a = cong (push→ base) (pushact≡idfun a) ∙ pushact≡idfun a
  h (surf i j) a k = help a k i j
    where
    help : (a : thePush') → Cube (λ i j → push→ (surf i j) (push← (surf i j) ∣ a ∣)) (λ _ _ → ∣ a ∣)
                                 (λ i _ → (cong (push→ base) (pushact≡idfun a) ∙ pushact≡idfun a) i)
                                 ((λ i _ → (cong (push→ base) (pushact≡idfun a) ∙ pushact≡idfun a) i))
                                 ((λ i _ → (cong (push→ base) (pushact≡idfun a) ∙ pushact≡idfun a) i))
                                 (λ i _ → (cong (push→ base) (pushact≡idfun a) ∙ pushact≡idfun a) i)
    help =
      thePush→Set (λ _ → isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelTrunc 5 _ _) _ _) _ _)
                   λ k i j → hcomp (λ r → λ { (i = i0) → rUnit (refl {x = ∣ inl (base , base) ∣ₕ}) r k
                                              ; (i = i1) → rUnit (refl {x = ∣ inl (base , base) ∣ₕ}) r k
                                              ; (j = i0) → rUnit (refl {x = ∣ inl (base , base) ∣ₕ}) r k
                                              ; (j = i1) → rUnit (refl {x = ∣ inl (base , base) ∣ₕ}) r k
                                              ; (k = i0) → S²actId (surf (~ i) j) (~ r) i j
                                              ; (k = i1) → ∣ inl (base , base) ∣ₕ})
                                    (hh k i j)
      where
      T : Path (Path S² base base) refl refl
      T = surf

      pr : (x y : S²) → thePush'
      pr x y = inl (x , y)

      PR : (x y : S²) → thePush'∥
      PR x y = ∣ inl (x , y) ∣ₕ

      PRUnit : (x : S²) → PR x base ≡ PR base x
      PRUnit base = refl
      PRUnit (surf i j) k = ∣
        hcomp (λ r → λ {(i = i0) → push (push tt k) (~ r)
                       ; (i = i1) → push (push tt k) (~ r)
                       ; (j = i0) → push (push tt k) (~ r)
                       ; (j = i1) → push (push tt k) (~ r)
                       ; (k = i0) → push (inl (surf i j)) (~ r)
                       ; (k = i1) → push (inr (surf i j)) (~ r)})
               (inr (surf i j)) ∣ₕ

      hh : Path (Square {A = thePush'∥}
             (λ _ → ∣ inl (base , base) ∣) (λ _ → ∣ inl (base , base) ∣)
             (λ _ → ∣ inl (base , base) ∣) (λ _ → ∣ inl (base , base) ∣))
             (λ i j → ∣ inl (surf (~ i) j , surf i j) ∣ₕ)
             refl
      hh =
            (cong₂Funct (λ (x y : (Path S² base base)) → cong₂ PR x y) (sym surf) surf
           ∙ cong (_∙ cong (cong (PR base)) surf) (λ i → cong (cong (λ x → PRUnit x i)) (sym surf))
           ∙ lCancel (cong (cong (PR base)) surf))

cancel2 : (x : S²) (y : thePush'∥) → push← x (push→ x y) ≡ y
cancel2 x =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
    (h x)
    where
    h : (x : S²) (a : thePush') → push← x (push→ x ∣ a ∣) ≡ ∣ a ∣
    h base a = cancel base ∣ a ∣
    h (surf i j) a l = cancel (surf (~ i) j) ∣ a ∣ l

thePushIso : (x : S²) → Iso thePush'∥ thePush'∥
fun (thePushIso x) = push→ x
inv (thePushIso x) = push← x
rightInv (thePushIso x) = cancel x
leftInv (thePushIso x) = cancel2 x


S²∙ : Pointed ℓ-zero
S²∙ = S² , base

pre-CODE : (x : Susp S²) → Type
pre-CODE north = thePush'∥
pre-CODE south = thePush'∥
pre-CODE (merid a i) = isoToPath (thePushIso a) i

hLevPre : (x : Susp S²) → isOfHLevel 5 (pre-CODE x)
hLevPre =
  suspToPropElim base (λ _ → isPropIsOfHLevel 5) (isOfHLevelTrunc 5)

CODER : (hLevelTrunc 6 (Susp S²)) → Type ℓ-zero
CODER =
  fst ∘ trRec {B = TypeOfHLevel ℓ-zero 5} (isOfHLevelTypeOfHLevel 5)
    λ x → (pre-CODE x) , (hLevPre x)

again : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (r : refl ≡ p)
                → cong (p ∙_) (sym r) ∙ sym (rUnit p)
                ≡ cong (_∙ p) (sym r) ∙ sym (lUnit p)
again p = J (λ p r → cong (p ∙_) (sym r) ∙ sym (rUnit p)
                  ≡ cong (_∙ p) (sym r) ∙ sym (lUnit p)) refl

kk : thePush' → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ north ∣
kk (inl x) = cong ∣_∣ₕ (σ S²∙ (fst x) ∙ σ S²∙ (snd x))
kk (inr x) = cong ∣_∣ₕ (σ S²∙ x)
kk (push (inl x) i) j = ∣ (cong (σ S²∙ x ∙_) (rCancel (merid base)) ∙ sym (rUnit (σ S²∙ x))) i j ∣ₕ
kk (push (inr x) i) j = ∣ (cong (_∙ σ S²∙ x) (rCancel (merid base)) ∙ sym (lUnit (σ S²∙ x))) i j ∣ₕ
kk (push (push a i₁) i) j = ∣ again (σ S²∙ base) (sym (rCancel (merid base))) i₁ i j ∣ₕ

kk2 : thePush'∥ → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ north ∣
kk2 = trRec (isOfHLevelTrunc 6 _ _) kk

S²-rec : ∀ {ℓ} {P : S² → Type ℓ}
       → (b : P base)
       → SquareP (λ i j → P (surf i j))
           (λ _ → b) (λ _ → b) (λ _ → b) (λ _ → b)
       → (x : S²) → P x
S²-rec b p base = b
S²-rec b p (surf i i₁) = p i i₁

DEC : (x : Susp S²) → CODER ∣ x ∣ → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ x ∣
DEC north p = kk2 p
DEC south p = kk2 p ∙ cong ∣_∣ₕ (merid base)
DEC (merid a i) = h a i
  where

  base' : (x : thePush')
     → kk2 (pushact base x) ≡
        kk2 ∣ x ∣
  base' x = cong kk2 (pushact≡idfun x)

  ayeaye : (a : S²) (x : thePush')
     → isOfHLevel 4 (kk2 (pushact a x) ∙ (λ i₁ → ∣ merid a i₁ ∣) ≡
        kk2 ∣ x ∣ ∙ cong ∣_∣ₕ (merid base))
  ayeaye a x = isOfHLevelTrunc 6 _ _ _ _

  lem1 : base' (inl (base , base)) ≡ refl
  lem1 = refl

  ssd : (a : S²) (x : thePush')
     → kk2 (pushact⁻ a x) ∙ (λ i₁ → ∣ merid a i₁ ∣) ≡
        kk2 ∣ x ∣ ∙ cong ∣_∣ₕ (merid base)
  ssd base x = cong (_∙ cong ∣_∣ₕ (merid base)) (base' x)
  ssd (surf i j) x k = help x k i j -- help x k i j
    where
    kk2≡ : (q : typ (Ω (Susp∙ (typ S²∙)))) → q ≡ q ∙ σ S²∙ base
    kk2≡ = λ q → rUnit q ∙ cong (q ∙_) (sym (rCancel (merid base)))

    sillyGen : ∀ {ℓ} {A : Type ℓ} {x : A}
                      {p : x ≡ x}
                      → (refl ≡ p)
                    → (q : Square {A = x ≡ x} (λ _ → p) (λ _ → p) (λ _ → p) (λ _ → p))
                    → Cube {A = Path A x x}
                            (λ i j → q i j ∙ q (~ i) j) (λ _ _ → p ∙ p)
                            (λ k j → p ∙ p) (λ _ _ → p ∙ p)
                            (λ _ _ → p ∙ p) λ _ _ → p ∙ p
    sillyGen {A = A} {x = x} {p = p} =
      J (λ p _ → (q : Square {A = x ≡ x} (λ _ → p) (λ _ → p) (λ _ → p) (λ _ → p))
                → Cube {A = Path A x x}
                        (λ i j → q i j ∙ q (~ i) j) (λ _ _ → p ∙ p)
                        (λ k j → p ∙ p) (λ _ _ → p ∙ p)
                        (λ _ _ → p ∙ p) λ _ _ → p ∙ p)
      (λ q →
      (λ _ → cong₂ (λ (x y : Path (x ≡ x) refl refl) → cong₂ _∙_ x y) q (sym q) )
      ◁ (cong₂Funct (λ (x y : Path (x ≡ x) refl refl) → cong₂ _∙_ x y) q (sym q)
      ∙ transport (λ i → cong (λ (x₂ : Path (x ≡ x) refl refl) i₂ → rUnit (x₂ i₂) i) q ∙
                          cong (λ (y : Path (x ≡ x) refl refl) i₂ → lUnit (y i₂) i) (sym q)
                       ≡ refl {x = refl {x = lUnit (refl {x = x}) i}})
                       (rCancel q)))

    help : (x : thePush') → Cube {A = Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ south ∣}
                                        (λ i j → kk2 (pushact (surf (~ i) j) x) ∙
                                          (λ i₂ → ∣ merid (surf i j) i₂ ∣))
                                  (λ _ _ → kk2 ∣ x ∣ ∙ cong ∣_∣ₕ (merid base))
                                  (λ k j → base' x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
                                  (λ k j → base' x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
                                  (λ k i → base' x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
                                  (λ k i → base' x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
    help =
      thePush→Set (λ _ → isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (isOfHLevelTrunc 6 _ _ _ _) _ _) _ _)
                 (λ k i j l → hcomp (λ r → λ {(i = i0) → ((λ i → ∣ kk2≡ (σ S²∙ base) r i ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid base)) (sym ((merid base))) (~ r))) l
                                              ; (i = i1) → ((λ i → ∣ kk2≡ (σ S²∙ base) r i ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid base)) (sym ((merid base))) (~ r))) l
                                              ; (j = i0) → ((λ i → ∣ kk2≡ (σ S²∙ base) r i ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid base)) (sym ((merid base))) (~ r))) l
                                              ; (j = i1) → ((λ i → ∣ kk2≡ (σ S²∙ base) r i ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid base)) (sym ((merid base))) (~ r))) l
                                              ; (k = i0) → ((λ w → ∣ kk2≡ (σ S²∙ (surf (~ i) j)) r w ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid (surf i j))) (sym ((merid base))) (~ r))) l
                                              ; (k = i1) → ((λ i → ∣ kk2≡ (σ S²∙ base) r i ∣ₕ)
                                                             ∙ cong ∣_∣ₕ (compPath-filler ((merid base)) (sym ((merid base))) (~ r))) l
                                              ; (l = i0) → ∣ north ∣ₕ
                                              ; (l = i1) → ∣ merid base r ∣ₕ})
                                     (sillyGen {p = cong ∣_∣ₕ (σ (S²∙) base) } (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))
                                               (λ i j k → ∣ σ S²∙ (surf (~ i) j) k ∣ₕ) k i j l))

  h : (a : S²) → PathP (λ i → CODER ∣ merid a i ∣ → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ merid a i ∣)
                        kk2
                        λ x → kk2 x ∙ cong ∣_∣ₕ (merid base)
  h a =
    toPathP (funExt
      (trElim (λ _ → isOfHLevelSuc 4 (isOfHLevelTrunc 6 _ _ _ _))
       (λ x
      → (λ j → transp (λ i → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ merid a (i ∨ j) ∣) j
                  (compPath-filler (kk2 (pushact⁻ a (transportRefl x j))) (cong ∣_∣ₕ (merid a)) j))
      ∙ ssd a x)))

module _ {ℓ : Level } {A : Type ℓ} (f g : thePush' → A)
           (h : isOfHLevel 5 A)
           (lp : (x : S²) → f (inl (x , base)) ≡ g (inl (x , base)))
           (rp : (x : S²) → f (inl (base , x)) ≡ g (inl (base , x)))
           (r≡l : ((x : S²) → (sym (cong f (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x)))
                        ≡ (sym (cong f (push (inr x))) ∙∙ rp x ∙∙ cong g (push (inr x))))) where

  z-er : I → I → I → A
  z-er k i j =
    hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym (cong f (push (inl base))))
                                                        (lp base)
                                                        (cong g (push (inl base))) (~ k) j
                   ; (i = i1) → doubleCompPath-filler (sym (cong f (push (inr base))))
                                                       (rp base)
                                                       (cong g (push (inr base))) (~ k) j
                   ; (j = i0) → f (push (push tt i) (~ k))
                   ; (j = i1) → g (push (push tt i) (~ k))})
      (inS (r≡l base i j))
      k
  rl≡ : lp base ≡ rp base
  rl≡ = (λ i j → z-er i1 i j)

  sider : (x y : S²) → f (inl (x , y)) ≡ g (inl (x , y))
  sider = S²wedge (λ _ _ → h _ _) lp rp rl≡

  sider≡ : (x : S²) → sider x base ≡ lp x
  sider≡ = S²wedge≡ (λ _ _ → h _ _) lp rp rl≡

  side≡≡ : sider≡ base ≡ sym rl≡
  side≡≡ = refl

  inrer : (x : S²) → f (inr x) ≡ g (inr x)
  inrer x = cong f (sym (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x))

  inrer≡ : (x : S²) → inrer x ≡ ((sym (cong f (push (inr x))) ∙∙ rp x ∙∙ cong g (push (inr x))))
  inrer≡ = r≡l

  inlfill : (x : S²) → I → I → I → A
  inlfill x k i j =
    hfill (λ k → λ { (i = i0) → sider≡ x (~ k) j
                    ; (i = i1) → doubleCompPath-filler
                                   (cong f (sym (push (inl x))))
                                   (lp x)
                                   (cong g (push (inl x))) k j
                    ; (j = i0) → f (push (inl x) (i ∧ k))
                    ; (j = i1) → g (push (inl x) (i ∧ k))})
          (inS (lp x j))
          k

  inrfill : (x : S²) → I → I → I → A
  inrfill x k i j =
    hfill (λ k → λ { (i = i0) → doubleCompPath-filler
                                   (cong f (sym (push (inr x))))
                                   (rp x)
                                   (cong g (push (inr x))) (~ k) j
                    ; (i = i1) → inrer x j
                    ; (j = i0) → f (push (inr x) (i ∨ ~ k))
                    ; (j = i1) → g (push (inr x) (i ∨ ~ k))})
                      (inS (r≡l x (~ i) j))
                      k

  ok : (x : thePush') → f x ≡ g x
  ok (inl x) = sider (fst x) (snd x)
  ok (inr x) = inrer x
  ok (push (inl x) i) j = inlfill x i1 i j
  ok (push (inr x) i) j = inrfill x i1 i j
  ok (push (push a i) j) k =
    hcomp (λ r → λ {(i = i0) → inlfill base i1 j k
                   ; (i = i1) → inrfill-side r j k
                   ; (j = i0) → rp base k
                   ; (j = i1) → r≡l base (~ r ∧ i) k
                   ; (k = i0) → f (push (push a i) j)
                   ; (k = i1) → g (push (push a i) j)})
      (hcomp (λ r → λ {(i = i0) → inlfill base r j k
                   ; (i = i1) → doubleCompPath-filler
                                  (cong f (sym (push (inr base))))
                                  (rp base)
                                  (cong g (push (inr base))) (j ∧ r) k
                   ; (j = i0) → rl≡ (r ∨ i) k
                   ; (j = i1) → inlfill-side r i k
                   ; (k = i0) → f (push (push a i) (j ∧ r))
                   ; (k = i1) → g (push (push a i) (j ∧ r))})
              (rl≡ i k))
    where
    inlfill-side : I → I → I → A
    inlfill-side r i k =
      hcomp (λ j → λ { (r = i0) → z-er j i k
                      ; (r = i1) → r≡l base i k
                      ; (i = i0) → doubleCompPath-filler
                                  (cong f (sym (push (inl base))))
                                  (lp base)
                                  (cong g (push (inl base))) (r ∨ ~ j) k
                      ; (i = i1) → doubleCompPath-filler
                                  (cong f (sym (push (inr base))))
                                  (rp base)
                                  (cong g (push (inr base))) (r ∨ ~ j) k
                      ; (k = i0) → f (push (push a i) (r ∨ ~ j))
                      ; (k = i1) → g (push (push a i) (r ∨ ~ j))})
            (r≡l base i k)
  
    inrfill-side : I → I → I → A
    inrfill-side r j k =
      hcomp (λ i → λ { (r = i0) →
                           (doubleCompPath-filler (cong f (sym (push (inr base))))
                           (rp base)
                           (cong g (push (inr base)))) (j ∨ ~ i)  k
                      ; (r = i1) → inrfill base i j k
                      ; (j = i0) → inrfill base i i0 k
                      ; (j = i1) → r≡l base (~ r) k
                      ; (k = i0) → f (push (inr base) (j ∨ ~ i))
                      ; (k = i1) → g (push (inr base) (j ∨ ~ i))})
            (r≡l base (~ r ∨ ~ j) k)

thePushElim : ∀ {ℓ} {A : Type ℓ} (f g : thePush' → A)
           → isOfHLevel 5 A
           → (lp : (x : S²) → f (inl (x , base)) ≡ g (inl (x , base)))
           → (rp : (x : S²) → f (inl (base , x)) ≡ g (inl (base , x)))
           → ((x : S²) → (sym (cong f (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x)))
                        ≡ (sym (cong f (push (inr x))) ∙∙ rp x ∙∙ cong g (push (inr x))))
           → (x : _) → f x ≡ g x
thePushElim = ok

DECODE : (x : hLevelTrunc 6 (Susp S²)) → CODER x → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x
DECODE = trElim (λ _ → isOfHLevelΠ 6 λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
                DEC
pointed : DECODE ∣ north ∣ ∣ inl (base , base) ∣ ≡ refl
pointed = cong (cong ∣_∣ₕ) (cong (λ x → x ∙ x) (rCancel (merid base)) ∙ sym (rUnit refl))

ENCODE : (x : hLevelTrunc 6 (Susp S²)) → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x → CODER x
ENCODE x p = subst CODER p ∣ inl (base , base) ∣

enc-dec : (x : hLevelTrunc 6 (Susp S²)) → (p : ∣ north ∣ ≡ x) → DECODE x (ENCODE x p) ≡ p
enc-dec x = J (λ x p → DECODE x (ENCODE x p) ≡ p)
              (cong (DECODE ∣ north ∣) (transportRefl ∣ inl (base , base) ∣ₕ)
             ∙ pointed)

dec-enc : (p : CODER ∣ north ∣) → ENCODE ∣ north ∣ (DECODE ∣ north ∣ p) ≡ p
dec-enc =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
    (thePushElim ((λ a → ENCODE ∣ north ∣ (DECODE ∣ north ∣ ∣ a ∣))) ∣_∣ₕ
      (isOfHLevelTrunc 5)
      (λ x → cong (ENCODE ∣ north ∣) (cong (cong ∣_∣ₕ) (cong (σ S²∙ x ∙_)
               (rCancel (merid base)) ∙ sym (rUnit (σ S²∙ x))))
             ∙ help x)
      (λ x → (cong (ENCODE ∣ north ∣) (cong (cong ∣_∣ₕ) (cong (_∙ σ S²∙ x)
               (rCancel (merid base)) ∙ sym (lUnit (σ S²∙ x))))
             ∙ help x
             ∙ cong ∣_∣ₕ (push (inl x)) ∙ cong ∣_∣ₕ (sym (push (inr x)))))
      λ x → ID (ENCODE ∣ north ∣)
                (cong (DECODE ∣ north ∣) (cong ∣_∣ₕ (push (inl x))))
                ((cong (DECODE ∣ north ∣) (cong ∣_∣ₕ (push (inr x)))))
                (help x) (cong ∣_∣ₕ (push (inl x))) (cong ∣_∣ₕ (sym (push (inr x)))))
  where
  subber = transport (λ j → CODER ∣ merid base (~ j) ∣ₕ)

  ID : ∀ {ℓ} {A B : Type ℓ} {x x' y : A} {l w u : B}
       (f : A → B) (p : x ≡ y) (p' : x' ≡ y) (q : f y ≡ l) (r : l ≡ w) (r' : w ≡ u)
     → cong f (sym p) ∙∙ cong f p ∙ q ∙∙ r
     ≡ (cong f (sym p') ∙∙ (cong f p' ∙ q ∙ (r ∙ r')) ∙∙ sym r')
  ID {x = x} {x' = x'} {y = y'} {l = l} {w = w} {u = u} f p p' q r r' =
      (λ i → (λ j → f (p (~ j ∨ i))) ∙∙ (λ j → f (p (j ∨ i))) ∙ q ∙∙ r)
   ∙∙ (λ i → (λ j → f (p' (~ j ∨ ~ i))) ∙∙ (λ j → f (p' (j ∨ ~ i))) ∙ compPath-filler q r i ∙∙ λ j → r (i ∨ j))
   ∙∙ λ i → cong f (sym p') ∙∙ cong f p' ∙ q ∙ compPath-filler r r' i ∙∙ λ j → r' (~ j ∧ i)

  rr : (x : S²) → (pushact x (inl (base , base))) ≡ ∣ inl (x , base) ∣ₕ
  rr base = refl
  rr (surf i i₁) = refl

  help : (x : S²) → ENCODE ∣ north ∣ (λ i → ∣ σ S²∙ x i ∣) ≡ ∣ inl (x , base) ∣
  help x = (λ i → transp (λ j →  CODER (∣ merid base (i ∧  ~ j) ∣ₕ)) (~ i)
                                         (ENCODE ∣ merid base i ∣
                                          λ j → ∣ compPath-filler (merid x) (sym (merid base)) (~ i) j ∣ₕ))
         ∙ cong subber (transportRefl (pushact x (inl (base , base))))
         ∙ cong subber (rr x)

theIso : Iso (hLevelTrunc 5 (typ (Ω (Susp∙ S²)))) (hLevelTrunc 5 thePush')
theIso = compIso (invIso (PathIdTruncIso _))
         is
  where
  is : Iso _ _
  fun is = ENCODE ∣ north ∣
  inv is = DECODE ∣ north ∣
  rightInv is = dec-enc
  leftInv is = enc-dec ∣ north ∣

ENCODE-refl : ENCODE ∣ north ∣ refl ≡ ∣ inl (base , base) ∣
ENCODE-refl = transportRefl _

∙≃→π≅ : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ)
      → (e : typ A ≃ typ B)
      → fst e (pt A) ≡ pt B
      → GroupEquiv (πGr n A) (πGr n B)
∙≃→π≅ {A = A} {B = B} n e =
  EquivJ (λ A e → (a : A) → fst e a ≡ pt B → GroupEquiv (πGr n (A , a)) (πGr n B))
    (λ b p → J (λ b p → GroupEquiv (πGr n (fst B , b)) (πGr n B))
      idGroupEquiv (sym p))
    e (pt A)

π₄S³≅π₃PushS² :
  GroupIso (πGr 3 (S₊∙ 3))
           (πGr 2 (thePush' , inl (base , base)))
π₄S³≅π₃PushS² =
  compGroupIso
    lem1
    (compGroupIso
     (invGroupIso (GrIso-πΩ-π 2))
     (compGroupIso
       (πTruncGroupIso 2)
       (compGroupIso
         (GroupEquiv→GroupIso
          (∙≃→π≅ {B = _ , ∣ inl (base , base) ∣ₕ} 2 (isoToEquiv theIso) ENCODE-refl))
         (invGroupIso (πTruncGroupIso 2)))))
  where

  lem1 : GroupIso (πGr 3 (S₊∙ 3)) (πGr 3 (Susp∙ S²))
  lem1 =
    GroupEquiv→GroupIso
     (∙≃→π≅ 3 (compEquiv (isoToEquiv (invIso IsoS³S3)) S³≃SuspS²) refl)

{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.thePush where

open import Cubical.Homotopy.Loopspace

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
    (λ x → λ i j → ∣ inl (x , surf (~ i) j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf (~ i) j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf (~ i) j)) (~ k)
                               ; (r = i1) → push (inl (surf (~ i) j)) (~ k)})
                     (inr (surf (~ i) j)) ∣ₕ

μ1 : (x y : S²) → thePush'∥
μ1 x y = ∣ inl (x , y) ∣ₕ

S²actId : (x : S²) → S²act x base ≡ λ i j → ∣ inl (x , surf (~ i) j) ∣ₕ
S²actId = S²wedge≡ (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
    (λ x → λ i j → ∣ inl (x , surf (~ i) j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf (~ i) j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf (~ i) j)) (~ k)
                               ; (r = i1) → push (inl (surf (~ i) j)) (~ k)})
                     (inr (surf (~ i) j)) ∣ₕ

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
             ({!!} ◁ {!!}) -- λ i j k → rCancel (λ _ → x) i {!j!}
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
{-
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
                λ i j → ∣ inl (surf (~ i) j , y) ∣
sideLem =
  S²ToSetRec (λ _ → isOfHLevelPathP' 2
              (isOfHLevelPathP' 3
                (isOfHLevelPathP' 4 (isOfHLevelTrunc 5) _ _) _ _) _ _)
   λ i j k → ∣ coh i1 i j k ∣ₕ
   -}

coh : I → I → I → I → thePush'
coh r i j k =
  hfill (λ r → λ { (i = i0) → movep'∙ (~ r) k
                               ; (i = i1) → movep'∙ (~ r) k
                               ; (j = i0) → movep'∙ (~ r) k
                               ; (j = i1) → movep'∙ (~ r) k
                               ; (k = i0) → inl (surf (~ i) j , base)
                               ; (k = i1) → inl (surf (~ i) j , base)})
                     (inS (inl (surf (~ i) j , base)))
                     r


sideLem : (y : S²)
        → Cube {A = thePush'∥}
                (λ j k → ∣ movep' y k ∣) (λ j k → ∣ movep' y k ∣)
                (λ j k → ∣ movep' y k ∣) (λ j k → ∣ movep' y k ∣)
                (S²act y (pt (S² , base)))
                λ i j → ∣ inl (surf (~ i) j , y) ∣
sideLem = S²ToSetRec (λ _ → isOfHLevelPathP' 2
              (isOfHLevelPathP' 3
                (isOfHLevelPathP' 4 (isOfHLevelTrunc 5) _ _) _ _) _ _)
   λ i j k → ∣ coh i1 i j k ∣ₕ

basic : thePush' → thePush'∥
basic thePush' = {!!}

pushact : (x : S²) → thePush' → thePush'∥
pushact base (inl y) = ∣ inl y ∣
pushact (surf i j) (inl y) = S²act (fst y) (snd y) i j
pushact base (inr y) = ∣ inl (base , y) ∣ₕ
pushact (surf i i₁) (inr y) = ∣ inl (surf (~ i) i₁ , y) ∣ₕ
pushact base (push (inl x) k) = ∣ (push (inl x) ∙ sym (push (inr x))) k ∣
pushact base (push (inr x) k) = ∣ inl (base , x) ∣
pushact base (push (push a y) k) = ∣ movep'∙ y k ∣
pushact (surf i j) (push (inl x) k) = sideLem x i j k
pushact (surf i j) (push (inr x) k) = ∣ inl (surf (~ i) j , x) ∣
pushact (surf i j) (push (push a k) l) =
    ∣ hcomp (λ r → λ { (i = i0) → movep'∙ (k ∨ ~ r) l
                  ; (i = i1) → movep'∙ (k ∨ ~ r) l
                  ; (j = i0) → movep'∙ (k ∨ ~ r) l
                  ; (j = i1) → movep'∙ (k ∨ ~ r) l
                  ; (k = i0) → coh r i j l
                  ; (k = i1) → inl (surf (~ i) j , base)
                  ; (l = i0) → inl (surf (~ i) j , base)
                  ; (l = i1) → inl (surf (~ i) j , base)})
        (inl (surf (~ i) j , base)) ∣ₕ

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

S²∙ : Pointed ℓ-zero
S²∙ = S² , base

pre-CODE : (x : Susp S²) → Type
pre-CODE north = thePush'∥
pre-CODE south = thePush'∥
pre-CODE (merid a i) = ua (_ , isEq-pushAct a) (~ i)

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
     → kk2 (pushact a x) ∙ (λ i₁ → ∣ merid a i₁ ∣) ≡
        kk2 ∣ x ∣ ∙ cong ∣_∣ₕ (merid base)
  ssd base x = cong (_∙ cong ∣_∣ₕ (merid base)) (base' x)
  ssd (surf i j) x k = help x k i j
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
                                        (λ i j → kk2 (pushact (surf i j) x) ∙
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
                  (compPath-filler
                    (kk2 (transportRefl (pushact a x) j))
                  (cong ∣_∣ₕ (merid a)) j))
           ∙ ssd a x)))

DECODE : (x : hLevelTrunc 6 (Susp S²)) → CODER x → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x
DECODE = trElim (λ _ → isOfHLevelΠ 6 λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
                DEC

ENCODE : (x : hLevelTrunc 6 (Susp S²)) → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x → CODER x
ENCODE x p = subst CODER p ∣ inl (base , base) ∣

enc-dec : (x : hLevelTrunc 6 (Susp S²)) → (p : ∣ north ∣ ≡ x) → DECODE x (ENCODE x p) ≡ p
enc-dec x =
  J (λ x p → DECODE x (ENCODE x p) ≡ p) ((λ i → DECODE ∣ north ∣ (∣ inl (transportRefl (base , base) i) ∣))
   ∙ cong (cong ∣_∣ₕ) (cong (λ x → x ∙ x) (rCancel (merid base)) ∙ sym (rUnit refl))
   ∙ refl)

thePushElim : ∀ {ℓ} {A : Type ℓ} (f g : thePush' → A)
           → isOfHLevel 5 A
           → (lp : (x : S²) → f (inl (x , base)) ≡ g (inl (x , base)))
           → (rp : (x : S²) → f (inl (base , x)) ≡ g (inl (base , x)))
           → ((x : S²) → (sym (cong f (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x)))
                        ≡ (sym (cong f (push (inr x))) ∙∙ rp x ∙∙ cong g (push (inr x))))
           → (x : _) → f x ≡ g x
thePushElim = {!!}

dec-enc : (p : CODER ∣ north ∣) → ENCODE ∣ north ∣ (DECODE ∣ north ∣ p) ≡ p
dec-enc =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
    (thePushElim ((λ a → ENCODE ∣ north ∣ (DECODE ∣ north ∣ ∣ a ∣))) ∣_∣ₕ
      (isOfHLevelTrunc 5)
      (λ x → cong (ENCODE ∣ north ∣) (cong (cong ∣_∣ₕ) (cong (σ S²∙ x ∙_)
               (rCancel (merid base)) ∙ sym (rUnit (σ S²∙ x))))
             ∙ {!!})
      {!!}
      {!!})
  where
  ENCODESplit : {!(a : S²) → ENCODE ∣ north ∣ ? ≡ ?!}
  ENCODESplit = {!!}

  subber = transport (λ j → CODER ∣ merid base (~ j) ∣ₕ)

  subber⁻ = transport (λ j → CODER ∣ merid base j ∣ₕ)

  h2 : (x : S²) → subber⁻ ∣ inl (x , base) ∣
                        ≡ ∣ inl (x , base) ∣
  h2 x = refl

  lem1 : (x : S²) → pushact x (inl (x , base))
                   ≡ ∣ inl (x , base) ∣
  lem1 base = refl -- S²actId
  lem1 (surf i j) k =
    hcomp (λ r → λ { (i = i0) → ∣ inl (base , base) ∣
                    ; (i = i1) → ∣ inl (base , base) ∣
                    ; (j = i0) → ∣ inl (base , base) ∣
                    ; (j = i1) → ∣ inl (base , base) ∣
                    ; (k = i0) → S²actId (surf i j) (~ r) i j
                    ; (k = i1) → ∣ inl (surf i j , base) ∣})
          {!S²actId (surf i j) i1 i j!}

  help : (x : S²) → ENCODE ∣ north ∣ (λ i → ∣ σ S²∙ x i ∣) ≡ ∣ inl (x , base) ∣
  help x = (λ i → transp (λ j →  CODER (∣ merid base (i ∧  ~ j) ∣ₕ)) (~ i)
                                         (ENCODE ∣ merid base i ∣
                                          λ j → ∣ compPath-filler (merid x) (sym (merid base)) (~ i) j ∣ₕ))
         ∙ (λ i → subber (invEq (_ , isEq-pushAct x) ∣ inl (base , base) ∣))
         ∙ {!invEq (_ , isEq-pushAct x) ∣ inl (base , base) ∣!}
    where
    h : {!ENCODE ∣ north ∣ !}
    h = {!!}

testi : Iso (typ (Ω (hLevelTrunc 6 (Susp S²) , ∣ north ∣))) (hLevelTrunc 5 thePush')
fun testi = ENCODE ∣ north ∣
inv testi = DECODE ∣ north ∣
rightInv testi = dec-enc
leftInv testi = enc-dec ∣ north ∣

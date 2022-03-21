{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.QuickProof where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Whitehead
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.HSpace
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso
open import Cubical.Homotopy.HopfInvariant.HopfMap

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Int
  renaming (ℤ to Z ; _·_ to _·Z_ ; _+_ to _+Z_)

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; map to pMap)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)

open import Cubical.Algebra.Group
  renaming (Unit to UnitGr)
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Instances.IntMod

open Iso
open Exact4
open S¹Hopf


open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S3

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr


open import Cubical.HITs.Wedge
open import Cubical.HITs.Join hiding (joinS¹S¹→S³)
open import Cubical.HITs.Pushout

σ₁ = σ (S₊∙ 1)
σ₁' : S¹ → Path (S₊ 2) north north
σ₁' base = refl
σ₁' (loop i) j =
  (sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base)) i j

σ₁≡σ₁' : (x : S¹) → σ₁ x ≡ σ₁' x
σ₁≡σ₁' base = rCancel (merid base)
σ₁≡σ₁' (loop i) j k =
  doubleCompPath-filler (sym (rCancel (merid base)))  (λ i → merid (loop i) ∙ sym (merid base)) (rCancel (merid base)) j i k

σ₂' : S₊ 2 → Path (S₊ 3) north north
σ₂' north = refl
σ₂' south = refl
σ₂' (merid base i) = refl
σ₂' (merid (loop i) j) k =
    hfill (λ r → λ {(i = i0) → merid (merid base j) (k ∧ ~ r)
                   ; (i = i1) → merid (merid base j) (k ∧ ~ r)
                   ; (j = i0) → merid north (k ∧ ~ r)
                   ; (j = i1) → merid south (k ∧ ~ r)
                   ; (k = i0) → north
                   ; (k = i1) → merid (merid base j) (~ r)})
          (inS (merid (merid (loop i) j) k))
          i1


σ₂invSusp : (x : _) → σ (S₊∙ 2) (invSusp x) ≡ sym (σ (S₊∙ 2) x)
σ₂invSusp north = cong (σ (S₊∙ 2)) (sym (merid base))
                ∙ (rCancel (merid north)
                ∙ cong sym (sym (rCancel (merid north))))
σ₂invSusp south = ((rCancel (merid north)) ∙ cong sym (sym (rCancel (merid north)))) ∙ cong sym (cong (σ (S₊∙ 2)) (merid base))
σ₂invSusp (merid base i) j =
  hcomp (λ k → λ {
                   (i = i0) → compPath-filler' (cong (σ (S₊∙ 2)) (sym (merid base)))
                                  (rCancel (merid north) ∙ cong sym (sym (rCancel (merid north)))) k j
                 ; (i = i1) → compPath-filler ((rCancel (merid north)) ∙ cong sym (sym (rCancel (merid north))))
                                  (cong sym (cong (σ (S₊∙ 2)) (merid base))) k j
                 ; (j = i0) → σ (S₊∙ 2) (merid base (~ i ∧ k))
                 ; (j = i1) → sym (σ (S₊∙ 2) (merid base (i ∧ k)))})
        ((rCancel (merid north) ∙ cong sym (sym (rCancel (merid north)))) j)
σ₂invSusp (merid (loop k) i) j =
  {!!}

σ₂≡ : (x : _) → σ₂' x ≡ σ (S₊∙ 2) x
σ₂≡ north = sym (rCancel (merid north))
σ₂≡ south = sym (rCancel (merid north)) ∙ cong (_∙ merid north ⁻¹) (cong merid (merid base))
σ₂≡ (merid base i) j = {!!}
σ₂≡ (merid (loop i₁) i) =
  {!k = i0 ⊢ σ₂invSusp (merid base i) j
k = i1 ⊢ σ₂invSusp (merid base i) j
i = i0 ⊢ σ₂invSusp north j
i = i1 ⊢ σ₂invSusp south j
j = i0 ⊢ σ (S₊∙ 2) (invSusp (merid (loop k) i))
j = i1 ⊢ sym (σ (S₊∙ 2) (merid (loop k) i))!}


σ₂ = σ (S₊∙ 2)

σ'-sym : (a : S¹) → σ₁' (invLooper a) ≡ sym (σ₁' a)
σ'-sym base = refl
σ'-sym (loop i) j k = (sym≡cong-sym (λ i j → σ₁' (loop i) j)) j i k

σ₁-sym : (a : S¹) → σ₁ (invLooper a) ≡ sym (σ₁ a)
σ₁-sym a = σ₁≡σ₁' (invLooper a) ∙∙ σ'-sym a ∙∙ cong sym (sym (σ₁≡σ₁' a))

S¹×S¹→S²R : (a : S¹) → S¹×S¹→S² a base ≡ north
S¹×S¹→S²R base = refl
S¹×S¹→S²R (loop i) = refl

cool-test : (a b : S¹) → S¹×S¹→S² a b ≡ S¹×S¹→S² b (invLooper a)
cool-test base base = refl
cool-test base (loop i) = refl
cool-test (loop i) base = refl
cool-test (loop i) (loop j) k =
  sym≡flipSquare (λ j i → S¹×S¹→S² (loop i) (loop j)) (~ k) i j

private
  mana-filler : (i : I)
    → cong₂ (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
    ≡ cong (S¹×S¹→S² (loop i)) loop
  mana-filler i =
    cong₂Funct (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop 
     ∙∙ (λ j → cong (λ x → S¹×S¹→S²R (rotLoop x i) j) loop ∙
                cong (λ c → S¹×S¹→S² (loop i) c) loop)
     ∙∙ sym (lUnit _)

mana : (a b : S¹) → S¹×S¹→S² (a * b) b ≡ S¹×S¹→S² a b
mana a base j = S¹×S¹→S² (rUnitS¹ a j) base
mana base (loop i) k = mana-filler i0 k i
mana (loop i₁) (loop i) k = mana-filler i₁ k i

invLooperDistr : (x y : S¹) → invLooper (x * y) ≡ invLooper x * invLooper y
invLooperDistr =
  wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _) (λ _ → refl)
    (λ x → cong invLooper (rUnitS¹ x) ∙ sym (rUnitS¹ (invLooper x)))
    (sym (rUnit refl))

invSusp' : S₊ 2 → S₊ 2
invSusp' north = north
invSusp' south = north
invSusp' (merid a i) = σ (S₊∙ 1) a (~ i)

pullInv : (a b : S¹) → S¹×S¹→S² a (invLooper b) ≡ invSusp (S¹×S¹→S² a b)
pullInv base b = merid base
pullInv (loop i) base = merid base
pullInv (loop i) (loop j) k =
  hcomp (λ r → λ {(i = i0) → h r j k
                 ; (i = i1) → h r j k
                 ; (j = i0) → merid base k
                 ; (j = i1) → merid base k
                 ; (k = i0) → doubleCompPath-filler
                                 (sym (rCancel (merid base)))
                                 (λ i → merid (loop i) ∙ sym (merid base))
                                 (rCancel (merid base)) r i (~ j)
                 ; (k = i1)
                   → invSusp (doubleCompPath-filler
                                 (sym (rCancel (merid base)))
                                 (λ i → merid (loop i) ∙ sym (merid base))
                                 (rCancel (merid base)) r i j)})
   (hcomp (λ r → λ {(i = i0) → sq r (~ j) k
                 ; (i = i1) → sq r (~ j) k
                 ; (j = i0) → merid base (~ r ∨ k)
                 ; (j = i1) → merid base (r ∧ k)
                 ; (k = i0) → compPath-filler (merid (loop i)) (sym (merid base)) r (~ j)
                 ; (k = i1) → invSusp (compPath-filler (merid (loop i)) (sym (merid base)) r j)})
         (merid (loop i) (~ j)))
  where
  sq : I → I → I → S₊ 2
  sq r j k =
    hfill (λ r → λ{(j = i0) → merid base (k ∧ r)
                  ; (j = i1) → merid base (~ r ∨ k)
                  ; (k = i0) → compPath-filler (merid base) (sym (merid base)) r j
                  ; (k = i1) → invSusp (compPath-filler (merid base) (sym (merid base)) r (~ j))})
          (inS (merid base j))
          r

  h : Cube {A = S₊ 2} (λ j k → sq i1 (~ j) k) (λ r → merid base)
        (λ r → merid base) (λ r → merid base)
        (λ r j → rCancel (merid base) r (~ j))
        (λ r j → invSusp (rCancel (merid base) r j))
  h r j k =
    hcomp (λ i → λ {(r = i0) → sq i (~ j) k
                 ; (r = i1) → merid base k
                 ; (j = i0) → merid base (k ∨ (~ i ∧ ~ r))
                 ; (j = i1) → merid base (k ∧ (i ∨ r))
                 ; (k = i0) → rCancel-filler (merid base) i r (~ j)
                 ; (k = i1) → invSusp (rCancel-filler (merid base) i r j) })
     (hcomp (λ i → λ {(r = i0) → merid base (~ j ∨ (~ i ∧ k))
                 ; (r = i1) → merid base (k ∨ (~ i ∧ ~ j))
                 ; (j = i0) → merid base (k ∨ (~ r ∨ ~ i))
                 ; (j = i1) → merid base (k ∧ (~ i ∨ r))
                 ; (k = i0) → merid base (~ j ∧ (~ r ∨ ~ i))
                 ; (k = i1) → merid base ((~ j ∨ ~ i) ∨ r) })
            (merid base (~ j ∨ k)))

S¹×S¹→S²a+a : (a : S¹) → S¹×S¹→S² a a ≡ north
S¹×S¹→S²a+a base = refl
S¹×S¹→S²a+a (loop i) k = h k i
  where
  h : cong₂ S¹×S¹→S² loop loop ≡ refl
  h = cong₂Funct S¹×S¹→S² loop loop
    ∙ (λ i → rUnit (cong (λ x → S¹×S¹→S²R x i) loop) (~ i))




{-
Goal: join (Susp A) B
———— Boundary ——————————————————————————————————————————————
j = i0 ⊢ inl north
j = i1 ⊢ inl north
i = i0 ⊢ inl north
i = i1 ⊢ inl north
-}





{-
i = i0 ⊢ inl south
i = i1 ⊢ push north b k
k = i0 ⊢ suspJoinFiller (~ i) r i1 (pt A) b
k = i1 ⊢ push south b i
r = i0 ⊢ c1-filler b i k i1
r = i1 ⊢ c1-filler b i k i1
-}

HopfM : join S¹ S¹ → S₊ 2
HopfM (inl x) = north
HopfM (inr x) = north
HopfM (push a b i) = (merid (a * b) ∙ sym (merid base)) i

∨map : join S¹ S¹ → (S₊∙ 2) ⋁ (S₊∙ 2)
∨map (inl x) = inr north
∨map (inr x) = inl north
∨map (push a b i) = ((λ i → inr (σ (S₊∙ 1) b i)) ∙∙ sym (push tt) ∙∙ (λ i → inl (σ (S₊∙ 1) a i))) i


_+join_ : ∀ {ℓ} {A : Pointed ℓ} (f g : (join S¹ S¹ , inl base) →∙ A)
       → (join S¹ S¹ , inl base) →∙ A
fst (f +join g) (inl x) = fst f (inl x)
fst (f +join g) (inr x) = fst g (inr x)
fst (f +join g) (push a b i) =
  (cong (fst f) (push a b ∙ sym (push base b))
  ∙∙ snd f ∙ sym (snd g)
  ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i
snd (f +join g) = snd f

{-
S¹ × S¹ →∙ Ω S²
-}

join-fill : I → I → I → I → join S¹ S¹
join-fill r i j k =
  hfill (λ r → λ { (i = i0) → push (loop r) (loop (j ∨ r)) k
                  ; (i = i1) → push base (loop (j ∨ r)) k --  (k ∧ ~ r)
                  ; (j = i0) → push (loop (i ∨ r)) (loop r) k
                  ; (j = i1) → push (loop (i ∨ r)) base k
                  ; (k = i0) → inl (loop (i ∨ r)) -- inl (loop (i ∨ r))
                  ; (k = i1) → inr (loop (j ∨ r))})
        (inS (push (loop i) (loop j) k))
        r

{-
S³→joinS¹S¹ : S³ → join S¹ S¹
S³→joinS¹S¹ base = inl base
S³→joinS¹S¹ (surf j k i) = border-contraction i j k i1
-}

S3→joinS¹S¹ : S₊ 3 → join S¹ S¹
S3→joinS¹S¹ north = inl base
S3→joinS¹S¹ south = inl base
S3→joinS¹S¹ (merid north i) = inl base
S3→joinS¹S¹ (merid south i) = inl base
S3→joinS¹S¹ (merid (merid base i₁) i) = inl base
S3→joinS¹S¹ (merid (merid (loop i) j) k) = border-contraction k i j i1

HopF : S₊∙ 3 →∙ S₊∙ 2
fst HopF x = HopfM (S3→joinS¹S¹ x)
snd HopF = refl

HopF2 : S₊∙ 3 →∙ S₊∙ 2
fst HopF2 x = fold⋁ (∨map (S3→joinS¹S¹ x))
snd HopF2 = refl

{-
deJoin : (join S¹ S¹ , inl base) →∙ S₊∙ 2 → S₊∙ 3 →∙ S₊∙ 2
fst (deJoin f) x = fst f (Iso.inv (IsoSphereJoin 1 1) x)
snd (deJoin f) = snd f

joinify : S₊∙ 3 →∙ S₊∙ 2 → (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst (joinify f) x = fst f (joinS¹S¹→S³ x)
snd (joinify f) = snd f

-}
open import Cubical.Homotopy.Connected

-- todo: remove connectivity assumption
module _ {ℓ : Level} {A : Pointed ℓ} where
  joinify :  S₊∙ 3 →∙ A → (join S¹ S¹ , inl base) →∙ A
  fst (joinify f) x = fst f (joinS¹S¹→S³ x)
  snd (joinify f) = snd f


  deJoin : (join S¹ S¹ , inl base) →∙ A → S₊∙ 3 →∙ A
  fst (deJoin f) = λ x → fst f (Iso.inv (IsoSphereJoin 1 1) x)
  snd (deJoin f) = snd f

{-
  Iso-join-dejoin₁ : Iso ((join S¹ S¹ , inl base) →∙ A) (S₊∙ 3 →∙ A)
  Iso-join-dejoin₁ = post∘∙equiv (isoToEquiv (IsoSphereJoin 1 1) , refl)

  deJoin = fun Iso-join-dejoin₁

  joinify = inv Iso-join-dejoin₁
-}

open import Cubical.Data.Bool renaming (Bool to BoolT)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)
open import Cubical.Homotopy.Connected

ind→3Connected : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} {f g : A →∙ B}
  → (isConnected 3 (typ B)) → fst f ≡ fst g → ∥ f ≡ g ∥
ind→3Connected {f = f} {g = g} con p =
  trRec squash
    (λ q → ∣ ΣPathP (p , q) ∣)
    (fst (isConnectedPathP 1 (isConnectedPath 2 con _ _) (snd f) (snd g)))

ind→3Connected' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} {f g : A →∙ B}
  → (isConnected 3 (typ B)) → fst f ≡ fst g → ∣ f ∣₂ ≡ ∣ g ∣₂
ind→3Connected' con p = pRec (squash₂ _ _) (cong ∣_∣₂) (ind→3Connected con p)

joininfy-dejoin : (f : (join S¹ S¹ , inl base) →∙ S₊∙ 2) → ∥ joinify (deJoin f) ≡ f ∥
joininfy-dejoin f =
  ind→3Connected (sphereConnected 2) (funExt λ x → cong (fst f) (leftInv (IsoSphereJoin 1 1) x))

dejoin-joinify : (f : S₊∙ 3 →∙ S₊∙ 2) → ∥ deJoin (joinify f) ≡ f ∥
dejoin-joinify f =
  ind→3Connected (sphereConnected 2) (funExt λ x → cong (fst f) (rightInv (IsoSphereJoin 1 1) x))

_+join≡_ : ∀ {ℓ} {A : Pointed ℓ} (f g : S₊∙ 3 →∙ A)
         → joinify (∙Π f g)
         ≡ (joinify f +join joinify g)
_+join≡_ f g =
  ΣPathP ((funExt (λ { (inl x) → sym (snd f)
                     ; (inr x) → sym (snd g) ∙ cong (fst g) (merid north)
                     ; (push a b i) j → h a b j i}))
        , λ i j → snd f (j ∨ ~ i))
  where
  S¹×S¹→S²rUnit : (a : S¹) → S¹×S¹→S² a base ≡ north
  S¹×S¹→S²rUnit base = refl
  S¹×S¹→S²rUnit (loop i) = refl

  l1 : (a b : S¹)
    → cong (fst (joinify g)) (push base base ∙∙ sym (push a base) ∙∙ push a b)
    ≡ cong (fst g) (merid (S¹×S¹→S² a b))
  l1 a b = cong-∙∙ (fst (joinify g))
       (push base base) (sym (push a base)) (push a b)
       ∙ cong (cong (fst g) (merid north) ∙∙_∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
              (cong (cong (fst g)) (cong sym (cong merid (S¹×S¹→S²rUnit a))))
       ∙  ((λ i → (cong (fst g) (λ j → merid north (j ∧ ~ i)))
       ∙∙ (cong (fst g) (λ j → merid north (~ j ∧ ~ i)))
       ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
       ∙ sym (lUnit (cong (fst g) (merid (S¹×S¹→S² a b)))))

  l2 : ∀ {ℓ} {A : Type ℓ} {x y z w u : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u)
    → (refl ∙∙ p ∙∙ q) ∙ (r ∙∙ s ∙∙ refl)
     ≡ (p ∙∙ (q ∙ r) ∙∙ s)
  l2 p q r s = (λ i → (p ∙ q) ∙ compPath≡compPath' r s (~ i))
           ∙∙ sym (∙assoc p q (r ∙ s))
           ∙∙ cong (p ∙_) (∙assoc q r s)
            ∙ sym (doubleCompPath≡compPath p (q ∙ r) s)

  pp : (a b : S¹)
    → Square ((refl ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
             ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ refl))
             (((cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
                                          ∙∙ (snd f ∙ sym (snd g))
               ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))))
           (λ _ → fst f north)
           (cong (fst g) (merid north))
  pp a b = l2 (cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))))
              (snd f) (sym (snd g)) (cong (fst g)
              (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))))
         ◁ p
    where
    p : PathP (λ i → fst f north ≡ cong (fst g) (merid north) i)
              ((λ i →
                  fst f ((merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) i))
               ∙∙ snd f ∙ (λ i → snd g (~ i)) ∙∙
               (λ i →
                  fst g ((merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) i)))
              ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                sym (cong (fst f) (merid north)))
               ∙∙ snd f ∙ sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
    p i j =
      hcomp (λ k → λ { (i = i0) → (cong-∙ (fst f) (merid (S¹×S¹→S² a b)) (sym (merid north)) (~ k)
                                ∙∙ snd f ∙ (λ i₁ → snd g (~ i₁))
                                ∙∙ (λ i₁ → fst g (compPath-filler (merid (S¹×S¹→S² a b)) (λ i₂ → merid north (~ i₂)) k i₁))) j
                       ; (i = i1) → ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                                      sym (cong (fst f) (merid north)))
                                     ∙∙ (snd f ∙ sym (snd g)) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
                                    j
                       ; (j = i0) → fst f north
                       ; (j = i1) → fst g (merid north (~ k ∨ i))})
            (((cong (fst f) (merid (S¹×S¹→S² a b)) ∙
                                      sym (cong (fst f) (merid north)))
                                     ∙∙ (snd f ∙ sym (snd g)) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b)))
                                    j)

  h : (a b : S¹)
    → PathP (λ i → snd f (~ i) ≡ (sym (snd g) ∙ cong (fst g) (merid north)) i)
            ((sym (snd f) ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
            ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd g))
            ((cong (fst (joinify f)) (push a b ∙ sym (push base b))
          ∙∙ snd f ∙ sym (snd g)
          ∙∙ cong (fst (joinify g)) (push base base ∙∙ sym (push a base) ∙∙ push a b)))
  h a b =
    ((λ i j → hcomp (λ k → λ {(i = i0) → (((λ j → snd f (~ j ∧ k)) ∙∙ cong (fst f) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ snd f)
                                         ∙ (sym (snd g) ∙∙ cong (fst g) (merid (S¹×S¹→S² a b) ∙ (λ i₂ → merid north (~ i₂))) ∙∙ λ j → snd g (j ∧ k))) j
                              ; (i = i1) → ((cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
                                          ∙∙ snd f ∙ sym (snd g)
                                          ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))) j
                              ; (j = i0) → snd f (~ i ∧ k)
                              ; (j = i1) → compPath-filler' (sym (snd g)) (cong (fst g) (merid north)) k i})
                     (pp a b i j))
    ▷ (λ i → (cong (fst f) (merid (S¹×S¹→S² a b)) ∙ sym (cong (fst f) (merid north)))
           ∙∙ snd f ∙ sym (snd g)
           ∙∙ cong (fst g) (merid (S¹×S¹→S² a b))))
    ▷ λ i →
      cong-∙ (fst (joinify f)) (push a b) (sym (push base b)) (~ i)
      ∙∙ snd f ∙ sym (snd g)
      ∙∙ l1 a b (~ i)

⟨π₃*⟩ = ∥ (join S¹ S¹ , inl base) →∙ S₊∙ 2 ∥₂

_π₃*+_ : ⟨π₃*⟩ → ⟨π₃*⟩ → ⟨π₃*⟩
_π₃*+_ = sRec2 squash₂ λ x y → ∣ x +join y ∣₂


-- todo: remove connectivity assumption

module _ {ℓ : Level} (A : Pointed ℓ) (con : (isConnected 3 (typ A))) where
  π₃*Iso : Iso (typ (π'Gr 2 A)) ∥ (join S¹ S¹ , inl base) →∙ A ∥₂
  fun π₃*Iso = sMap joinify
  inv π₃*Iso = sMap deJoin
  rightInv π₃*Iso =
    sElim (λ _ → isSetPathImplicit)
      λ f → ind→3Connected'
        con (funExt λ x → cong (fst f) (Iso.leftInv (IsoSphereJoin 1 1) x))
  leftInv π₃*Iso =
    sElim (λ _ → isSetPathImplicit)
      λ f → ind→3Connected'
        con (funExt (λ x → cong (fst f) (Iso.rightInv (IsoSphereJoin 1 1) x)))

  π₃* : Group ℓ
  π₃* = InducedGroup (π'Gr 2 A) (sRec2 squash₂ (λ x y → ∣ x +join y ∣₂))
        (isoToEquiv π₃*Iso)
          (sElim2 (λ _ _ → isSetPathImplicit) (λ f g → cong ∣_∣₂ (_+join≡_ f g)))

  π₃≃π₃* : GroupEquiv (π'Gr 2 A) π₃*
  π₃≃π₃* =
    InducedGroupEquiv (π'Gr 2 A) (sRec2 squash₂ (λ x y → ∣ x +join y ∣₂))
        (isoToEquiv π₃*Iso)
          (sElim2 (λ _ _ → isSetPathImplicit) (λ f g → cong ∣_∣₂ (_+join≡_ f g))) 

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
         (conA : (isConnected 3 (typ A))) (conB : (isConnected 3 (typ B)))
         (f : A →∙ B) where
  postCompπ₃* : GroupHom (π₃* A conA) (π₃* B conB)
  fst postCompπ₃* = sMap (f ∘∙_)
  snd postCompπ₃* =
    makeIsGroupHom
      (sElim2 (λ _ _ → isSetPathImplicit)
        λ h g → ind→3Connected' conB
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a b i) j → 
           (cong-∙∙ (fst f)
                    (cong (fst h) ((push a b ∙ (sym (push base b)))))
                    (snd h ∙ (sym (snd g)))
                    (cong (fst g) ((push base base ∙∙ (sym (push a base)) ∙∙ push a b)))
             ∙ cong (cong (fst f) (cong (fst h) (push a b ∙ (sym (push base b))))
                                  ∙∙_∙∙
                                  cong (fst f) (cong (fst g) ((push base base ∙∙ (sym (push a base)) ∙∙ push a b))))
                    (cong-∙ (fst f) (snd h) (sym (snd g))
                    ∙ λ j → compPath-filler (cong (fst f) (snd h)) (snd f) j
                           ∙ sym (compPath-filler (cong (fst f) (snd g)) (snd f) j))) j i}))

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'}
         (conA : (isConnected 3 (typ A))) (conB : (isConnected 3 (typ B)))
         (f : A ≃∙ B) where
  postCompπ₃Equiv : GroupEquiv (π₃* A conA) (π₃* B conB)
  fst postCompπ₃Equiv = isoToEquiv h
    where
    h : Iso (π₃* A conA .fst) (π₃* B conB .fst)
    fun h = fst (postCompπ₃* conA conB (≃∙map f))
    inv h = fst (postCompπ₃* conB conA (≃∙map (invEquiv∙ f)))
    rightInv h =
      sElim (λ _ → isSetPathImplicit)
        λ g → ind→3Connected' conB (funExt λ x → secEq (fst f) (fst g x))
    leftInv h =
      sElim (λ _ → isSetPathImplicit)
        λ g → ind→3Connected' conA (funExt λ x → retEq (fst f) (fst g x))
  snd postCompπ₃Equiv = snd (postCompπ₃* conA conB (≃∙map f))

connS³ : isConnected 3 (S₊ 3)
connS³ =
  isConnectedSubtr 3 1 (sphereConnected 3)

con-joinS¹S¹ : isConnected 3 (join S¹ S¹)
con-joinS¹S¹ =
  (isConnectedRetractFromIso 3
      (IsoSphereJoin 1 1)
      (isConnectedSubtr 3 1 (sphereConnected 3)))

π₃S³ = π'Gr 2 (S₊∙ 3)

π₃*S³ : Group₀
π₃*S³ =
  π₃* (S₊∙ 3) connS³

_+π₃*_ : fst π₃*S³ → fst π₃*S³ → fst π₃*S³
_+π₃*_ = GroupStr._·_ (snd π₃*S³)

π₃*S² : Group₀
π₃*S² =
  π₃* (S₊∙ 2) (sphereConnected 2)

π₃*joinS¹S¹ : Group₀
π₃*joinS¹S¹ =
  π₃* (join S¹ S¹ , inl base) con-joinS¹S¹

π₃S²→π₃*S² : GroupEquiv (π'Gr 2 (S₊∙ 2)) π₃*S²
π₃S²→π₃*S² = π₃≃π₃* (S₊∙ 2) (sphereConnected 2) -- π₃*Iso

π₃S³≅π₃*S³ : GroupEquiv π₃S³ π₃*S³
π₃S³≅π₃*S³ = π₃≃π₃* (S₊∙ 3) connS³

π₃*S³≅π₃*joinS¹S¹ : GroupEquiv π₃*S³ π₃*joinS¹S¹
π₃*S³≅π₃*joinS¹S¹ =
  postCompπ₃Equiv
    connS³ con-joinS¹S¹
      (isoToEquiv (invIso (IsoSphereJoin 1 1)) , refl)


π₃S³≅π₃*joinS¹S¹-gen : fst (fst (compGroupEquiv π₃S³≅π₃*S³ π₃*S³≅π₃*joinS¹S¹)) ∣ idfun∙ _ ∣₂
                    ≡ ∣ idfun∙ _ ∣₂
π₃S³≅π₃*joinS¹S¹-gen =
  ind→3Connected' con-joinS¹S¹
    (funExt λ x → leftInv (IsoSphereJoin 1 1) x)


gen-by-id-≅π₃*joinS¹S¹ : gen₁-by π₃*joinS¹S¹ ∣ idfun∙ _ ∣₂
gen-by-id-≅π₃*joinS¹S¹ =
  subst (gen₁-by π₃*joinS¹S¹) π₃S³≅π₃*joinS¹S¹-gen
    (Iso-pres-gen₁ π₃S³ _
      ∣ idfun∙ _ ∣₂
      (πₙ'Sⁿ-gen-by-idfun 2)
      (GroupEquiv→GroupIso (compGroupEquiv π₃S³≅π₃*S³ π₃*S³≅π₃*joinS¹S¹)))

π₃' : GroupHom π₃*joinS¹S¹ π₃*S²
π₃' = postCompπ₃*
    con-joinS¹S¹ (sphereConnected 2)
      (fst ∘ JoinS¹S¹→TotalHopf , refl)

π₃'S³→π₃*joinS¹S¹ : GroupHom π₃S³ π₃*joinS¹S¹
π₃'S³→π₃*joinS¹S¹ =
  compGroupHom
    (fst (fst (π₃≃π₃* (S₊∙ 3) connS³)) , snd (π₃≃π₃* (S₊∙ 3) connS³))
    (postCompπ₃* {A = S₊∙ 3} connS³ con-joinS¹S¹
       (Iso.inv (IsoSphereJoin 1 1) , refl))

π₃'S³→π₃*S² : GroupHom (π'Gr 2 (S₊∙ 3)) π₃*S²
π₃'S³→π₃*S² = {!!}

module S³→S²LES = πLES {A = S₊∙ 3} {B = S₊∙ 2}
    (fst ∘ JoinS¹S¹→TotalHopf ∘ Iso.inv (IsoSphereJoin 1 1) , refl)

π₃'S³→π₃S² : GroupEquiv (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2))
π₃'S³→π₃S² =
  compGroupEquiv (πS³≅πTotalHopf 2) π'₃S²≅π'₃TotalHopf

π₃'S³→π₃S²η : fst (fst π₃'S³→π₃S²) {!!} ≡ {!!} -- fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂
π₃'S³→π₃S²η = {!(cong (fst f) (push a b ∙ sym (push base b))
  ∙∙ snd f ∙ sym (snd g)
  ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i!}

π₃'S³→π₃*S²' : GroupEquiv (π'Gr 2 (S₊∙ 3)) π₃*S²
π₃'S³→π₃*S²' = compGroupEquiv π₃'S³→π₃S² (π₃≃π₃* (S₊∙ 2) (sphereConnected 2))

π₃'S³→π₃*S²Hom : GroupHom (π'Gr 2 (S₊∙ 3)) π₃*S²
π₃'S³→π₃*S²Hom = compGroupHom π₃'S³→π₃*joinS¹S¹ π₃'

π₃'S³→π₃*S²'Hom : GroupHom (π'Gr 2 (S₊∙ 3)) π₃*S²
π₃'S³→π₃*S²'Hom = fst (fst π₃'S³→π₃*S²') , snd π₃'S³→π₃*S²'


isId : π₃'S³→π₃*S²'Hom ≡ π₃'S³→π₃*S²Hom
isId = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
              (funExt
                (sElim (λ _ → isSetPathImplicit)
                  λ f → ind→3Connected'
                          (sphereConnected 2)
                          (funExt
                            λ x
                            → (funExt⁻ (sym (cong fst hopfMap≡HopfMap'))
                                 (fst f (joinS¹S¹→S³ x))))))

π₃'S³≅π₃*S² : GroupEquiv (π'Gr 2 (S₊∙ 3)) π₃*S² -- π₃'S³→π₃*S²'Hom
fst (fst π₃'S³≅π₃*S²) = fst π₃'S³→π₃*S²Hom
snd (fst π₃'S³≅π₃*S²) = subst isEquiv (cong fst isId) (snd (fst π₃'S³→π₃*S²'))
snd π₃'S³≅π₃*S² = snd π₃'S³→π₃*S²Hom

η : π' 3 (S₊∙ 2)
η = fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂

η'-raw : (join S¹ S¹ , inl base) →∙ S₊∙ 2
fst η'-raw (inl x) = north
fst η'-raw (inr x) = north
fst η'-raw (push a b i) = (σ (S₊∙ 1) b ∙ σ (S₊∙ 1) a) i 
snd η'-raw = refl

η' : fst π₃*S²
η' = ∣ η'-raw ∣₂

η'↦η :  η' ≡ fst (fst π₃S²→π₃*S²) η
η'↦η = ind→3Connected' (sphereConnected 2) (funExt λ x → lem1 x ∙ sym (funExt⁻ lem0 x))
  where
  lem0 : fold∘W ∘ joinS¹S¹→S³ ≡ fold⋁ ∘ (joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1})
  lem0 = funExt λ x
    → cong (fold⋁ ∘ (joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}))
      (leftInv (IsoSphereJoin 1 1) x)

  lem1 : (x : join S¹ S¹) → fst η'-raw x ≡ (fold⋁ ∘ joinTo⋁) x
  lem1 (inl x) = refl
  lem1 (inr x) = refl
  lem1 (push a b i) j = help j i
    where
    help : (σ (S₊∙ 1) b ∙ σ (S₊∙ 1) a) ≡ cong (fold⋁ ∘ joinTo⋁) (push a b)
    help = sym (cong-∙∙ fold⋁ (λ j → inr (σ (S₊∙ 1) b j)) (sym (push tt)) (λ j → inl (σ (S₊∙ 1) a j))
             ∙ λ i → (λ j → σ (S₊∙ 1) b (j ∧ ~ i)) ∙∙ (λ j → σ (S₊∙ 1) b (j ∨ ~ i)) ∙∙ σ (S₊∙ 1) a)

π₃*joinS¹S¹→π₃*S² : GroupHom π₃*joinS¹S¹ π₃*S²
π₃*joinS¹S¹→π₃*S² =
  postCompπ₃* con-joinS¹S¹ (sphereConnected 2)
    (fst ∘ JoinS¹S¹→TotalHopf , refl)

isEquivπ₃*joinS¹S¹→π₃*S² : isEquiv (fst π₃*joinS¹S¹→π₃*S²)
isEquivπ₃*joinS¹S¹→π₃*S² =
  transport (λ i → isEquiv (fst (help (~ i))))
    (snd (fst GrEq))
  where
  GrEq = compGroupEquiv (πS³≅πTotalHopf 2) π'₃S²≅π'₃TotalHopf

  help : PathP (λ i → GroupHom
                         (GroupPath π₃*joinS¹S¹ (π'Gr 2 (S₊∙ 3)) .fst
                           (compGroupEquiv (invGroupEquiv (π₃≃π₃* (join S¹ S¹ , inl base) con-joinS¹S¹))
                                           (π'Iso 2 (isoToEquiv (IsoSphereJoin 1 1) , refl))) i)
                         (GroupPath π₃*S² (π'Gr 2 (S₊∙ 2)) .fst
                           (invGroupEquiv (π₃≃π₃* (S₊∙ 2) (sphereConnected 2))) i))
                         π₃*joinS¹S¹→π₃*S²
                         (fst (fst GrEq) , snd GrEq)
  help =
    toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ f → (λ i → transportRefl ((invGroupEquiv (π₃≃π₃* (S₊∙ 2) (sphereConnected 2))) .fst .fst
                             (fst π₃*joinS¹S¹→π₃*S² (
                               ((invEq (fst (invGroupEquiv (π₃≃π₃* (join S¹ S¹ , inl base) con-joinS¹S¹))))
                                (invEq (fst (π'Iso 2 (isoToEquiv (IsoSphereJoin 1 1) , refl))) (transportRefl f i)))))) i)
                   ∙ main f))

    where
    main : (f : _) → invEquiv (fst (π₃≃π₃* (S₊∙ 2) (sphereConnected 2))) .fst
      (fst π₃*joinS¹S¹→π₃*S²
       (invEq
        (invEquiv (fst (π₃≃π₃* (join S¹ S¹ , inl base) con-joinS¹S¹)))
        (invEq (fst (π'Iso 2 (isoToEquiv Iso-joinS¹S¹-S³ , (λ _ → north))))
         f)))
      ≡ fst GrEq .fst f
    main = sElim (λ _ → isSetPathImplicit)
      λ f → ind→3Connected' (sphereConnected 2)
        (funExt λ x → (λ i → fst (JoinS¹S¹→TotalHopf (Iso.inv (IsoSphereJoin 1 1)
                               (fst f (Iso.rightInv (IsoSphereJoin 1 1) x i)))))
                     ∙ sym (funExt⁻ (sym (cong fst hopfMap≡HopfMap'))
                                 (fst f x)))
joinS¹S¹→S² : join S¹ S¹ → S₊ 2
joinS¹S¹→S² (inl x) = north
joinS¹S¹→S² (inr x) = north
joinS¹S¹→S² (push a b i) =
  σ (S₊∙ 1) (invLooper a * b) i

π₃*joinS¹S¹→π₃*S²-nicer : GroupHom π₃*joinS¹S¹ π₃*S²
π₃*joinS¹S¹→π₃*S²-nicer =
  postCompπ₃* con-joinS¹S¹ (sphereConnected 2)
    (joinS¹S¹→S² , refl)

isEquivπ₃*joinS¹S¹→π₃*S²-nicer : fst π₃*joinS¹S¹→π₃*S² ≡ fst π₃*joinS¹S¹→π₃*S²-nicer
isEquivπ₃*joinS¹S¹→π₃*S²-nicer =
  funExt (sElim (λ _ → isSetPathImplicit) λ f → ind→3Connected' (sphereConnected 2)
    (funExt λ x → lem (fst f x)))
  where
  lem : (x : _) → fst (JoinS¹S¹→TotalHopf x) ≡ joinS¹S¹→S² x
  lem (inl x) = refl
  lem (inr x) = sym (merid base)
  lem (push a b i) j = compPath-filler (merid (invLooper a * b)) (sym (merid base)) j i


-- η''-raw : (join S¹ S¹ , inl base) →∙ (join S¹ S¹ , inl base)
-- fst η''-raw (inl x) = inr (invLooper x)
-- fst η''-raw (inr x) = inr x
-- fst η''-raw (push a b i) = (sym (push (b * invLooper a) (invLooper a)) ∙ push (b * invLooper a) b) i
-- snd η''-raw = sym (push base base)

-- η'' : fst (π₃*joinS¹S¹)
-- η'' = ∣ η''-raw ∣₂

-- invLooper² : (x : S¹) → invLooper (invLooper x) ≡ x
-- invLooper² base = refl
-- invLooper² (loop i) = refl

-- η''↦η' : fst π₃*joinS¹S¹→π₃*S²-nicer η'' ≡ η'
-- η''↦η' =
--   ind→3Connected' (sphereConnected 2)
--     (funExt λ { (inl x) → refl
--               ; (inr x) → refl
--               ; (push a b i) j → h a b j i})
--   where
--   h : (a b : S¹) → cong joinS¹S¹→S² ((sym (push (b * invLooper a) (invLooper a)) ∙ push (b * invLooper a) b))
--                   ≡ σ (S₊∙ 1) b ∙ σ (S₊∙ 1) a
--   h a b =
--       cong-∙ joinS¹S¹→S² (sym (push (b * invLooper a) (invLooper a))) (push (b * invLooper a) b) 
--     ∙ (λ i → sym (σ (S₊∙ 1) (invLooper (b * invLooper a) * invLooper a))
--             ∙ (σ (S₊∙ 1) (invLooper (b * invLooper a) * b)))
--     ∙ cong₂ _∙_ (cong sym (cong σ₁ (sym (invLooperDistr (b * invLooper a) a)))
--                          ∙ cong sym (σ₁-sym (b * invLooper a * a))
--                         ∙ cong σ₁ (sym (assocS¹ b (invLooper a) a)
--                                ∙ cong (b *_) (commS¹ _ _ ∙ sym (rCancelS¹ a))
--                                ∙ rUnitS¹ b))
--                          (cong σ₁ (cong (_* b) (invLooperDistr b (invLooper a)
--                                              ∙ cong (invLooper b *_) (invLooper² a)
--                                              ∙ commS¹ (invLooper b) a)
--                                              ∙ sym (assocS¹ a (invLooper b) b)
--                                              ∙ cong (a *_) (commS¹ _ _ ∙ sym (rCancelS¹ b))
--                                              ∙ rUnitS¹ a))


-- η'''-raw : (join S¹ S¹ , inl base) →∙ S₊∙ 3
-- fst η'''-raw (inl x) = north
-- fst η'''-raw (inr x) = north
-- fst η'''-raw (push a b i) =
--   (sym (σ₂ (S¹×S¹→S² a b)) ∙ sym (σ₂ (S¹×S¹→S² a b))) i
-- snd η'''-raw = refl

-- η'''-raw/2 : (join S¹ S¹ , inl base) →∙ S₊∙ 3
-- fst η'''-raw/2 (inl x) = north
-- fst η'''-raw/2 (inr x) = north
-- fst η'''-raw/2 (push a b i) = σ₂ (S¹×S¹→S² a b) (~ i)
-- snd η'''-raw/2 = refl

-- η''' : π₃*S³ .fst
-- η''' = ∣ η'''-raw ∣₂

-- η'''/2 : π₃*S³ .fst
-- η'''/2 = ∣ η'''-raw/2 ∣₂

-- gen↦η'''/2 : fst (fst π₃S³≅π₃*S³) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) ≡ η'''/2 
-- gen↦η'''/2 =
--   ind→3Connected' connS³
--     (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl})

-- η'''/2+η'''/2≡η''' : η'''/2 +π₃* η'''/2 ≡ η'''
-- η'''/2+η'''/2≡η''' =
--   ind→3Connected' connS³
--     (funExt λ { (inl x) → refl
--               ; (inr x) → refl
--               ; (push a b i) → λ j → lem a b j i})
--   where
--   lem : (a b : S¹) → cong (fst (η'''-raw/2 +join η'''-raw/2)) (push a b) ≡ cong (fst η'''-raw) (push a b)
--   lem a b = (λ i → cong-∙ (fst η'''-raw/2) (push a b) (sym (push base b)) i
--                  ∙∙ rUnit refl (~ i)
--                  ∙∙ cong-∙∙ (fst η'''-raw/2) (push base base) (sym (push a base)) (push a b) i)
--          ∙∙ (λ i → (sym (σ₂ (S¹×S¹→S² a b)) ∙ rCancel (merid north) i) -- sym (rCancel (merid north) i)
--                  ∙∙ refl
--                  ∙∙ (sym (rCancel (merid north) i)
--                  ∙∙ (cong σ₂ (S¹×S¹→S²R a) ∙ rCancel (merid north)) i
--                  ∙∙ sym (σ₂ (S¹×S¹→S² a b))))
--          ∙∙ ((λ i → rUnit (sym (σ₂ (S¹×S¹→S² a b))) (~ i)
--                   ∙∙ refl
--                   ∙∙ lUnit (sym (σ₂ (S¹×S¹→S² a b))) (~ i))
--            ∙ λ i → (λ j → σ₂ (S¹×S¹→S² a b) (i ∨ ~ j))
--                  ∙∙ (λ j → σ₂ (S¹×S¹→S² a b) (i ∧ ~ j))
--                  ∙∙ sym (σ₂ (S¹×S¹→S² a b)))

-- -- (cong (fst f) (push a b ∙ sym (push base b))
--  --  ∙∙ snd f ∙ sym (snd g)
--   -- ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) 

-- joinS¹S¹→S³σ : join S¹ S¹ → S₊ 3
-- joinS¹S¹→S³σ (inl x) = north
-- joinS¹S¹→S³σ (inr x) = north
-- joinS¹S¹→S³σ (push a b i) = σ₂ (S¹×S¹→S² a b) i

-- joinS¹S¹→S³σ≡ : (x : _) → joinS¹S¹→S³σ x ≡ joinS¹S¹→S³ x
-- joinS¹S¹→S³σ≡ (inl x) = refl
-- joinS¹S¹→S³σ≡ (inr x) = merid north
-- joinS¹S¹→S³σ≡ (push a b i) j =
--   compPath-filler (merid (S¹×S¹→S² a b)) (sym (merid north)) (~ j) i

-- η''↦η''' : invEq (fst π₃*S³≅π₃*joinS¹S¹) η'' ≡ η'''
-- η''↦η''' =
--   ind→3Connected' connS³ -- con-joinS¹S¹
--    (funExt λ x → sym (joinS¹S¹→S³σ≡ (fst η''-raw x))
--                 ∙ lem x)
--   where
--   lem : (x : _) → joinS¹S¹→S³σ (fst η''-raw x) ≡ fst η'''-raw x
--   lem (inl x) = refl
--   lem (inr x) = refl
--   lem (push a b i) = λ j → lem₂ j i
--     where
--     lem₂ : cong (joinS¹S¹→S³σ ∘ fst η''-raw) (push a b)
--         ≡ sym (σ₂ (S¹×S¹→S² a b)) ∙ sym (σ₂ (S¹×S¹→S² a b))
--     lem₂ = cong-∙ joinS¹S¹→S³σ (sym (push (b * invLooper a) (invLooper a))) (push (b * invLooper a) b)
--          ∙∙ (λ _ → sym (σ₂ ((S¹×S¹→S² (b * invLooper a) (invLooper a)))) ∙ σ₂ (S¹×S¹→S² (b * invLooper a) b))
--          ∙∙ cong₂ _∙_ (cong sym (cong σ₂ (mana b (invLooper a) ∙ sym (cool-test a b))))
--                       (cong σ₂ ((cong (λ x → S¹×S¹→S² x b) (commS¹ b (invLooper a)) ∙ mana (invLooper a) b)
--                             ∙∙ cool-test (invLooper a) b
--                             ∙ pullInv b (invLooper a) -- cong (S¹×S¹→S² b) (invLooper² a)
--                             ∙∙ refl)
--                     ∙∙ σ₂invSusp (S¹×S¹→S² b (invLooper a))
--                     ∙∙ cong (sym ∘ σ₂) (sym (cool-test a b)))

-- π₃S³→π₃*S³ : GroupEquiv (π'Gr 2 (S₊∙ 3)) π₃*S³
-- π₃S³→π₃*S³ = π₃≃π₃* (S₊∙ 3) connS³

-- η'''' : fst π₃S³
-- η'''' = ·π' 2 (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂)

-- η''''↦η''' : fst (fst π₃S³→π₃*S³) η'''' ≡ η'''
-- η''''↦η''' = IsGroupHom.pres· (snd π₃S³→π₃*S³) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂) (-π' 2 ∣ idfun∙ (S₊∙ 3) ∣₂)
--            ∙ cong₂ _+π₃*_ gen↦η'''/2 gen↦η'''/2
--            ∙ η'''/2+η'''/2≡η'''




-- -- -- π'₃S²≅π'₃TotalHopf
-- -- fst π₃'S³→π₃S² = {!LESπ.f!}
-- --                 , SES→isEquiv
-- --                     {!? ∙ sym (cong (πGr 2) IsoFiberTotalHopfS¹∙≡)!}
-- --                     ({!!} ∙ {!!})
-- --                     (S³→S²LES.fib→A 2)
-- --                     (S³→S²LES.A→B 2)
-- --                     (S³→S²LES.B→fib 1)
-- --                     (S³→S²LES.Ker-A→B⊂Im-fib→A 2)
-- --                     (S³→S²LES.Ker-B→fib⊂Im-A→B 1)
-- --   where
-- --   tt2 : {!!}
-- --   tt2 = IsoFiberTotalHopfS¹∙≡
  
-- -- snd π₃'S³→π₃S² =  S³→S²LES.A→B 2 .snd




-- -- BrunerieIsoAbstract' : GroupEquiv (π'Gr 3 (S₊∙ 3)) (abstractℤ/ 2)
-- -- BrunerieIsoAbstract' =
-- --   compGroupEquiv π₄S³≅π₃coFib-fold∘W∙
-- --     (invGroupEquiv
-- --       (GroupEquiv-abstractℤ/abs-gen
-- --         (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
-- --           (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))
-- --           (invGroupEquiv π₃S²≅ℤ) -- (invGroupEquiv hopfInvariantEquiv)
-- --           (π'∘∙Hom 2 (fold∘W , refl))
-- --           _
-- --           S³→S²→Pushout→Unit 2 {!fst (JoinS¹S¹→TotalHopf (inv (IsoSphereJoin 1 1) x)))!}))
-- --   where


-- --   η = fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂

-- --   η-preim-raw : (join S¹ S¹ , inl base) →∙ (join S¹ S¹ , inl base)
-- --   fst η-preim-raw (inl x) = inr (invLooper x)
-- --   fst η-preim-raw (inr x) = inr x
-- --   fst η-preim-raw (push a b i) =
-- --     (sym (push (b * invLooper a) (invLooper a))
-- --     ∙ push (b * invLooper a) b) i
-- --   snd η-preim-raw = sym (push base base)

-- --   η-preim : fst π₃*joinS¹S¹ -- ∥ ? ∥₂
-- --   η-preim = ∣ η-preim-raw ∣₂

-- --   mainEq : η ≡ {!!}
-- --   mainEq = {!!}


-- -- --   π₃S³→π₃*S² : GroupHom (π'Gr 2 (S₊∙ 3)) π₃*S²
-- -- --   π₃S³→π₃*S² = compGroupHom (π'∘∙Hom 2 (fst ∘ JoinS¹S¹→TotalHopf ∘ Iso.inv (IsoSphereJoin 1 1) , refl))
-- -- --                              (fst (fst (π₃S²→π₃*S²)) , snd π₃S²→π₃*S²)

-- -- --   id+id : S₊∙ 3 →∙ S₊∙ 3
-- -- --   fst id+id north = north
-- -- --   fst id+id south = north
-- -- --   fst id+id (merid a i) = (σ (S₊∙ 2) a ∙ σ (S₊∙ 2) a) i
-- -- --   snd id+id = refl

-- -- --   σ' = σ (S₊∙ 1)

-- -- --   H' : (a : join S¹ S¹) → SuspS¹
-- -- --   H' (inl x) = north
-- -- --   H' (inr x) = north
-- -- --   H' (push a b i) = σ' (invLooper a * b) i

-- -- --   joinTest : (a b : S¹) → Path (Path (join S¹ S¹) _ _) (push a b ∙ sym (push base b)) (push a base ∙ sym (push base base))
-- -- --   joinTest a base = refl
-- -- --   joinTest a (loop i) j = {!push a (loop (i ∨ j)) ∙ sym (push base (loop (i ∧ ~ j)))!}



-- -- --   coolId : fst π₃S³→π₃*S² ∣ id+id ∣₂ ≡ ∣ H' , refl ∣₂
-- -- --   coolId = ind→3Connected' (sphereConnected 2)
-- -- --             (funExt λ { (inl x) → refl
-- -- --                       ; (inr x) → refl
-- -- --                       ; (push a b i) → {!fst ∘ (JoinS¹S¹→TotalHopf (inv (IsoSphereJoin 1 1)))!}})
-- -- --     where
-- -- --     lem1 : (a b : S¹) → cong (fst id+id ∘ (fun (IsoSphereJoin 1 1))) (push a b) ≡ cong (fun (IsoSphereJoin 1 1)) (push b base ∙ sym (push a base)) -- --  ∙ sym (push base base))
-- -- --     lem1 a b = cong (cong (fst id+id)) (λ _ → merid (S¹×S¹→S² a b))
-- -- --             ∙∙ {!cong joinS¹S¹→S³ (push (loop ?) base)!}
-- -- --             ∙∙ sym (cong-∙ joinS¹S¹→S³ (push b base) (sym (push a base)))

-- -- --     help : (a b : S¹) → cong (fst ∘ JoinS¹S¹→TotalHopf ∘ inv (IsoSphereJoin 1 1) ∘ fst id+id ∘ (fun (IsoSphereJoin 1 1)))
-- -- --                               (push a b)
-- -- --                               ≡ cong H' (push a b)
-- -- --     help a b = {!!}

-- -- --   presGen : fst π₃S³→π₃*S² ∣ id∙ (S₊∙ 3) ∣₂ ≡ ∣ fst ∘ JoinS¹S¹→TotalHopf , refl ∣₂
-- -- --   presGen =
-- -- --     ind→3Connected' (sphereConnected 2)
-- -- --       (funExt λ x → cong (fst ∘ JoinS¹S¹→TotalHopf) (Iso.leftInv (IsoSphereJoin 1 1) x))

-- -- --   η-id : (fst (π'∘∙Hom 2 (fold∘W , refl))
-- -- --         (fst (fst (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))) 1))
-- -- --       ≡ fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂
-- -- --   η-id = {!!} {- cong (fst (π'∘∙Hom 2 (fold∘W , refl))) (sym (sym (leftInv ((fst (πₙ'Sⁿ≅ℤ 2))) ∣ id∙ (S₊∙ 3) ∣₂)
-- -- --           ∙ cong (inv (fst (πₙ'Sⁿ≅ℤ 2))) (πₙ'Sⁿ≅ℤ-idfun∙ 2))) -}

-- -- --   H2 : fst π₃*S²
-- -- --   H2 = ∣ (fold⋁ ∘ joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}) , refl ∣₂

-- -- --   help : fst (fst π₃S²→π₃*S²) (fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ id∙ (S₊∙ 3) ∣₂)
-- -- --        ≡ H2
-- -- --   help =
-- -- --     ind→3Connected' (sphereConnected 2)
-- -- --       (funExt λ x → cong (fold⋁ ∘ joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1})
-- -- --         (Iso.leftInv (IsoSphereJoin 1 1) x))

-- -- --   +commS¹ : (a b : S¹) → a * b ≡ b * a
-- -- --   +commS¹ base b = sym (rUnitS¹ b)
-- -- --   +commS¹ (loop i) base = refl
-- -- --   +commS¹ (loop i) (loop i₁) = refl

-- -- --   σaa : (a b : S¹)
-- -- --     →  σ' a ∙ σ' a ∙ σ' (invLooper a * b)
-- -- --       ≡ σ' b ∙ σ' a
-- -- --   σaa base b = {!!}
-- -- --   σaa (loop i) b = {!!}
-- -- --     where
-- -- --     meinlem : {!!}
-- -- --     meinlem = {!!}

-- -- --     c : cong₂ (λ x y → σ' x ∙ σ' y ∙ σ' (invLooper y * b)) loop loop
-- -- --             ≡ {!refl!}
-- -- --     c = cong₂Funct (λ x y → σ' x ∙ σ' y ∙ σ' (invLooper y * b))  loop loop
-- -- --         ∙ {!!}

-- -- --   push+ : (a b : S¹) → Path (Path (S₊∙ 2 ⋁ S₊∙ 2) _ _)
-- -- --                         (λ i → inl (σ' ((invLooper a) * b) i) )
-- -- --                         ((λ i → inl (σ' ((invLooper a)) i)) ∙ λ i → inl (σ' b i))
-- -- --   push+ a b = {!!}

-- -- --   HopfMapCharac : {!joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1} (push ? ? ?)!}
-- -- --   HopfMapCharac = {!!}

-- -- --   help2 : fst (fst π₃S²→π₃*S²) ∣ HopfMap ∣₂ ≡ ∣ (fst ∘ JoinS¹S¹→TotalHopf) , refl ∣₂
-- -- --   help2 = ind→3Connected' (sphereConnected 2)
-- -- --           (funExt λ x → cong ((fst ∘ JoinS¹S¹→TotalHopf)) (Iso.leftInv (IsoSphereJoin 1 1) x))

-- -- --   jV = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}

-- -- --   -j : join S¹ S¹ → join S¹ S¹
-- -- --   -j (inl x) = inr base
-- -- --   -j (inr x) = inl base
-- -- --   -j (push a b i) = (sym (push b base) ∙∙ push b a ∙∙ sym (push base a)) i

-- -- --   -j-j : (x : join S¹ S¹) → -j (-j x) ≡ x
-- -- --   -j-j (inl x) = push base base ∙ sym (push x base)
-- -- --   -j-j (inr x) = sym (sym (push base x) ∙ (push base base))
-- -- --   -j-j (push a b i) = λ j → pp j i
-- -- --     where
-- -- --     lem3 : cong -j (cong -j (push a b))
-- -- --          ≡ _
-- -- --     lem3 = cong-∙∙ -j (sym (push b base)) (push b a) (sym (push base a))
-- -- --          ∙∙ (λ i → ((λ j → push base b (j ∧ ~ i)) ∙∙ (λ j → push base b (~ j ∧ ~ i)) ∙∙ (push base base))
-- -- --                 ∙∙ (sym (push a base) ∙∙ push a b ∙∙ sym (push base b))
-- -- --                 ∙∙ ((push base base) ∙∙ (λ j → push a base (~ j ∨ i)) ∙∙ λ j → push a base (j ∨ i)))
-- -- --          ∙∙ ((λ i → ((lUnit (push base base)) (~ i)
-- -- --                   ∙∙ sym (push a base) ∙∙ push a b ∙∙ sym (push base b)
-- -- --                  ∙∙ ((sym (compPath≡compPath' (push base base) (λ _ → inr base)) ∙ sym (rUnit (push base base))) i)))
-- -- --          ∙ (λ i → compPath-filler (push base base) (sym (push a base)) i
-- -- --                  ∙∙ doubleCompPath-filler (sym (push a base)) (push a b) (sym (push base b)) (~ i)
-- -- --                  ∙∙ compPath-filler' (sym (push base b)) (push base base) i))

-- -- --     pp : PathP (λ i → (push base base ∙ sym (push a base)) i
-- -- --                      ≡ (sym (push base b) ∙ (push base base)) (~ i))
-- -- --                (cong -j (cong -j (push a b))) (push a b)
-- -- --     pp = lem3 ◁
-- -- --       λ i → doubleCompPath-filler
-- -- --         ((push base base ∙ sym (push a base)))
-- -- --           (push a b)
-- -- --          (sym (push base b) ∙ (push base base)) (~ i)

-- -- --   dejoinId : joinify {!!} ≡ {!!}
-- -- --   dejoinId = {!cong₂ (_∙∙ sym (push a base) ∙∙ push a b ∙∙ sym (push base b) ∙∙_)
-- -- --                   (sym (lUnit (push base base)))
-- -- --                   (sym (compPath≡compPath' (push base base) (λ _ → inr base)) ∙ sym (rUnit (push base base)))!}

-- -- --   -join : ∀ {ℓ} {A : Pointed ℓ} → ((join S¹ S¹ , inl base) →∙ A) → (join S¹ S¹ , inl base) →∙ A
-- -- --   fst (-join {A = A} f) (inl x) = (fst f (inr x))
-- -- --   fst (-join {A = A} f) (inr x) = (fst f (inl x))
-- -- --   fst (-join {A = A} f) (push a b i) = fst f (push b a (~ i))
-- -- --   snd (-join f) = cong (fst f) (sym (push base base)) ∙ snd f

-- -- --   123a : ∀ {ℓ} {A : Pointed ℓ} (f : S₊∙ 3 →∙ A)
-- -- --     → joinify (-Π f) ≡  -join (joinify f)
-- -- --   123a f = ΣPathP ((funExt
-- -- --     (λ { (inl x) → cong (fst f) (merid north) -- cong (fst f) (sym (push base base))
-- -- --        ; (inr x) → refl -- cong (fst f) (sym (push base base))
-- -- --        ; (push a b i) → {!!}}))
-- -- --                  , {!!})
-- -- --     where
-- -- --     h : (a : _) → {!!} -- cong (fst (deJoin (-join f))) (merid a) ≡ {!!}
-- -- --     h a =
-- -- --         {!!}
-- -- --       ∙ {!!}

-- -- --   +join- : ∀ {ℓ} {A : Pointed ℓ} → (f : (join S¹ S¹ , inl base) →∙ A)
-- -- --          → (x : _) → fst (-join f +join f) x ≡ pt A
-- -- --   +join- f (inl x) = {!!} -- (cong (fst f) (push x base ∙ sym (push base base))) ∙ snd f
-- -- --   +join- f (inr x) = {!!} -- (cong (fst f) (push x base ∙ sym (push base base))) ∙ snd f
-- -- --   +join- f (push a b i) = {!!}
-- -- --     where
-- -- --     help25 : cong (fst ((-join f) +join f)) (push a b) ≡ {!!}
-- -- --     help25 = (λ i → (cong-∙ (fst (-join f)) (push a b) (sym (push base b)) i
-- -- --            ∙∙ ((cong (fst f) (sym (push base base))) ∙ (snd f)) ∙ sym (snd f)
-- -- --            ∙∙ cong-∙∙ (fst f) (push base base) (sym (push a base)) (push a b) i))
-- -- --           ∙∙ {!!}
-- -- --           ∙∙ {!!}


-- -- --   H≡ : fst ∘ JoinS¹S¹→TotalHopf ≡ H'
-- -- --   H≡ = funExt λ { (inl x) → refl
-- -- --                  ; (inr x) → sym (merid base)
-- -- --                  ; (push a b i) j → compPath-filler (merid (invLooper a * b)) (sym (merid base)) j i}

-- -- --   mainId : H2 ≡ ∣ ((fst ∘ JoinS¹S¹→TotalHopf) , refl) +join ((fst ∘ JoinS¹S¹→TotalHopf) , refl) ∣₂
-- -- --   mainId = cong ∣_∣₂
-- -- --             (ΣPathP (funExt (λ { (inl x) → refl
-- -- --                                ; (inr x) → merid base
-- -- --                                ; (push a b i) → {!!}})
-- -- --                                , refl))
-- -- --     where
-- -- --     shuffle : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ∙∙ refl ∙∙ q ≡ p ∙ q
-- -- --     shuffle p q i = (λ j → p (~ i ∧ j)) ∙∙ (λ j → p (~ i ∨ j)) ∙∙ q

-- -- --     h : (a b : S¹) → cong (fold⋁ ∘ jV) (push a b) ≡ (σ (S₊∙ 1) b) ∙ σ (S₊∙ 1) a
-- -- --     h a b = cong-∙∙ fold⋁ (λ i → inr (σ' b i)) (sym (push tt)) (λ i → inl (σ' a i))
-- -- --           ∙ shuffle _ _

-- -- --     H = fst ∘ JoinS¹S¹→TotalHopf

-- -- --     x+x : join S¹ S¹ → join S¹ S¹
-- -- --     x+x (inl x) = inl x
-- -- --     x+x (inr x) = inr x
-- -- --     x+x (push a b i) = (push a base ∙ sym (push base base) ∙ push base b) i

-- -- --     grr : {!!}
-- -- --     grr = {!!}

-- -- --     2×H' : (r : _) → joinify (∙Π (idfun∙ _) (idfun∙ _)) .fst r ≡ Iso.fun (IsoSphereJoin 1 1) (x+x r)
-- -- --     2×H' (inl x) = refl
-- -- --     2×H' (inr x) = merid north
-- -- --     2×H' (push a b i) = {!!}

-- -- --     rs : (a b : S¹) → cong (fst
-- -- --       ((H' , refl) +join (H' , refl))) (push a b) ≡ {!!}
-- -- --     rs a b = (λ i → cong-∙ H'  (push a b) (sym (push base b)) i ∙∙ rUnit refl (~ i) ∙∙ cong-∙∙ H' (push base base) (sym (push a base)) (push a b) i)
-- -- --           ∙∙ shuffle _ _
-- -- --           ∙∙ (λ i → (σ' (invLooper a * b) ∙ (sym (σ' b)))
-- -- --                    ∙ (rCancel (merid base) i ∙∙ sym (σ' (rUnitS¹ (invLooper a) i)) ∙∙ σ' (invLooper a * b)))
-- -- --           ∙∙ {!!}
-- -- --           ∙∙ {!!}

-- -- -- {-
-- -- --   compGroupEquiv π₄S³≅π₃coFib-fold∘W∙
-- -- --     (invGroupEquiv
-- -- --       (GroupEquiv-abstractℤ/abs-gen
-- -- --         (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
-- -- --           (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))
-- -- --           (invGroupEquiv hopfInvariantEquiv)
-- -- --           (π'∘∙Hom 2 (fold∘W , refl))
-- -- --           _
-- -- --           S³→S²→Pushout→Unit Brunerie main)) -}

-- -- -- -- wedgeify : (f g : S₊∙ 3 →∙ S₊∙ 2) → S₊∙ 3 →∙ S₊∙ 2
-- -- -- -- fst (wedgeify f g) x = {!!}
-- -- -- -- snd (wedgeify f g) = {!x!}

-- -- -- -- HopF' : (join S¹ S¹ , inl base) →∙ S₊∙ 2
-- -- -- -- fst HopF' = HopfM
-- -- -- -- snd HopF' = refl

-- -- -- -- HopF2' : (join S¹ S¹ , inl base) →∙ S₊∙ 2
-- -- -- -- fst HopF2' = fold⋁ ∘ ∨map
-- -- -- -- snd HopF2' = refl

-- -- -- -- homotHom : ∥ (join S¹ S¹ , inl base) →∙ (join S¹ S¹ , inl base) ∥₂ → ∥ (join S¹ S¹ , inl base) →∙ S₊∙ 2 ∥₂ 
-- -- -- -- homotHom = sMap λ f → HopfM ∘ fst f , cong HopfM (snd f)


-- -- -- -- -- wedge+ : ∣ HopF2 ∣₂ ≡ ·π' 2 ∣ HopF ∣₂ ∣ HopF ∣₂
-- -- -- -- -- wedge+ =
-- -- -- -- --   cong ∣_∣₂
-- -- -- -- --     ( {!id2!} ∙∙ cong deJoin ((id2 ∙ {!!}) ∙∙ cong (λ x → x +join x) (sym id1) ∙∙ sym (HopF +join≡ HopF)) ∙∙ dejoin-joinify (∙Π HopF HopF))


-- -- -- -- --   where
-- -- -- -- --   id1 : joinify HopF ≡ HopF'
-- -- -- -- --   id1 = ΣPathP (funExt (λ x → cong HopfM (S3→joinS¹S¹→S³ x)) , flipSquare (cong (cong HopfM) (rCancel (push base base))))

-- -- -- -- --   id2 : joinify HopF2 ≡ HopF2'
-- -- -- -- --   id2 = ΣPathP (funExt (λ x → cong (fold⋁ ∘ ∨map) (S3→joinS¹S¹→S³ x)) , flipSquare ((cong (cong (fold⋁ ∘ ∨map)) (rCancel (push base base)))))

-- -- -- -- --   main : (x : _) → fst HopF2' x ≡ fst (HopF' +join HopF') x
-- -- -- -- --   main (inl x) = σ (S₊∙ 1) x
-- -- -- -- --   main (inr x) = σ (S₊∙ 1) x
-- -- -- -- --   main (push a b i) = {!!}
-- -- -- -- --     where
-- -- -- -- --     s1 : cong (fst HopF2') (push a b) ≡ {!cong fold⋁ ?!}
-- -- -- -- --     s1 = cong-∙∙ fold⋁ (λ i → inr (σ (S₊∙ 1) b i)) (sym (push tt)) (λ i → inl (σ (S₊∙ 1) a i))
-- -- -- -- --        ∙∙ {!!}
-- -- -- -- --        ∙∙ {!!}

-- -- -- -- --     σ' : S¹ → typ (Ω (S₊∙ 2))
-- -- -- -- --     σ' base = refl
-- -- -- -- --     σ' (loop i) j = (sym (rCancel (merid base)) ∙∙ (cong (σ (S₊∙ 1)) loop) ∙∙ rCancel (merid base)) i j

-- -- -- -- --     σ'≡σ : (a : S¹) → σ (S₊∙ 1) a ≡ σ' a
-- -- -- -- --     σ'≡σ base = rCancel (merid base)
-- -- -- -- --     σ'≡σ (loop i) j k =
-- -- -- -- --       doubleCompPath-filler (sym (rCancel (merid base))) (cong (σ (S₊∙ 1)) loop) (rCancel (merid base)) j i k

-- -- -- -- --     σ'-sym : (a : S¹) → σ' (invLooper a) ≡ sym (σ' a)
-- -- -- -- --     σ'-sym base = refl
-- -- -- -- --     σ'-sym (loop i) j k = (sym≡cong-sym (λ i j → σ' (loop i) j)) j i k

-- -- -- -- --     σ-sym : (a : S¹) → σ (S₊∙ 1) (invLooper a) ≡ sym (σ (S₊∙ 1) a)
-- -- -- -- --     σ-sym a = σ'≡σ (invLooper a) ∙∙ σ'-sym a ∙∙ cong sym (sym (σ'≡σ a))

-- -- -- -- --     σ'-morph : (a : S¹) → σ' (a * a) ≡ σ' a ∙ σ' a
-- -- -- -- --     σ'-morph base = rUnit refl
-- -- -- -- --     σ'-morph (loop i) j = help3 i j
-- -- -- -- --       where
-- -- -- -- --       help : cong σ' (cong₂ _*_ loop loop) ≡ cong σ' loop ∙ cong σ' loop
-- -- -- -- --       help = cong (cong σ') (cong₂Funct _*_ loop loop)
-- -- -- -- --           ∙∙ cong (cong σ') (λ i → cong (λ x → rUnitS¹ x i) loop ∙ loop)
-- -- -- -- --           ∙∙ cong-∙ σ' loop loop

-- -- -- -- --       help2 : cong₂ _∙_ (cong σ' loop) (cong σ' loop)
-- -- -- -- --             ≡ cong (λ x → x ∙ refl) (cong σ' loop) ∙ cong (λ x → refl ∙ x) (cong σ' loop)
-- -- -- -- --       help2 = cong₂Funct _∙_ (cong σ' loop) (cong σ' loop)

-- -- -- -- --       help3 : Square (rUnit refl) (rUnit refl) (cong σ' (cong₂ _*_ loop loop)) (cong₂ _∙_ (cong σ' loop) (cong σ' loop))
-- -- -- -- --       help3 =
-- -- -- -- --         flipSquare (help
-- -- -- -- --           ◁ ((λ i → cong (λ x → rUnit x i) (cong σ' loop) ∙ cong (λ x → lUnit x i) (cong σ' loop))
-- -- -- -- --           ▷ sym help2))

-- -- -- -- --     σ-morph : (a : S¹) → σ (S₊∙ 1) (a * a) ≡ σ (S₊∙ 1) a ∙ σ (S₊∙ 1) a
-- -- -- -- --     σ-morph a = σ'≡σ (a * a) ∙∙ σ'-morph a ∙∙ cong (λ x → x ∙ x) (sym (σ'≡σ a))

-- -- -- -- --     σ'3 : (a : S¹) → σ' a ∙∙ σ' a ∙∙ σ' a ≡ σ' ((a * a) * a)
-- -- -- -- --     σ'3 base = sym (rUnit refl)
-- -- -- -- --     σ'3 (loop i) = {!!}
-- -- -- -- --       where
-- -- -- -- --       h : cong₂ (λ x y → x ∙∙ x ∙∙ y) (cong σ' loop) (cong σ' loop) ≡ {!!} -- cong (λ x → (x * x) * x) loop
-- -- -- -- --       h = cong₂Funct (λ x y → x ∙∙ x ∙∙ y) (cong σ' loop) (cong σ' loop)
-- -- -- -- --         ∙∙ {!cong (!} ∙∙ {!!}

-- -- -- -- --     σ'-comm : (a b : S¹) → σ' (a * b) ∙∙ (σ' (invLooper b) ∙ σ' (invLooper a)) ∙∙ σ' (a * b) ≡ σ' b ∙ σ' a
-- -- -- -- --     σ'-comm base b = {!!} -- sym (lUnit (σ' b)) ∙∙ refl ∙∙ rUnit (σ' b)
-- -- -- -- --     σ'-comm (loop i) b = {!!}

-- -- -- -- --     {-
-- -- -- -- --       (cong (fst f) (push a b ∙ sym (push base b))
-- -- -- -- --   ∙∙ snd f ∙ sym (snd g)
-- -- -- -- --   ∙∙ cong (fst g) (push base base ∙∙ sym (push a base) ∙∙ push a b)) i
-- -- -- -- --     -}

-- -- -- -- --     s3 : cong (fst (HopF' +join HopF')) (push a b)
-- -- -- -- --        ≡ (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b))
-- -- -- -- --        ∙ (sym (σ (S₊∙ 1) a) ∙ σ (S₊∙ 1) (a * b))
-- -- -- -- --     s3 = (λ i → cong-∙ (fst HopF') (push a b) (sym (push base b)) i
-- -- -- -- --               ∙∙ rUnit refl (~ i)
-- -- -- -- --               ∙∙ cong-∙∙ (fst HopF') (push base base) (sym (push a base)) (push a b) i)
-- -- -- -- --       ∙∙ (λ i → (λ j → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) (~ i ∧ j))
-- -- -- -- --               ∙∙ ((λ j → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) (~ i ∨ j)))
-- -- -- -- --               ∙∙ (rCancel (merid base) i ∙∙ sym (σ (S₊∙ 1) (rUnitS¹ a i)) ∙∙ σ (S₊∙ 1) (a * b)))
-- -- -- -- --       ∙∙ refl


-- -- -- -- -- {- cong ∣_∣₂ (sym (dejoin-joinify {!!})
-- -- -- -- --                     ∙∙ {!!} -- cong deJoin
-- -- -- -- --                       ({!!}
-- -- -- -- --                        ∙ {!!}
-- -- -- -- --                       ∙∙ cong (λ x → x +join x) (sym id1)
-- -- -- -- --                       ∙∙ sym (HopF +join≡ HopF))
-- -- -- -- --                     ∙∙ dejoin-joinify (∙Π HopF HopF)) {- ((funExt (λ { north → refl
-- -- -- -- --                                      ; south → refl
-- -- -- -- --                                      ; (merid a i) j → help a j i})) -}
-- -- -- -- --                         --  , refl)) -}



-- -- -- -- -- --   where
-- -- -- -- -- --   maini : HopF2' ≡ (HopF' +join HopF')
-- -- -- -- -- --   maini = ΣPathP ((funExt (λ { (inl x) → refl
-- -- -- -- -- --                              ; (inr x) → refl
-- -- -- -- -- --                              ; (push a b i) j → h a b j i}))
-- -- -- -- -- --                 , refl)
-- -- -- -- -- --     where
-- -- -- -- -- --     rotLoop' : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → Square p p p p
-- -- -- -- -- --     rotLoop' p i j =
-- -- -- -- -- --       hcomp (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- -- -- -- -- --                  ; (i = i1) → p (j ∧ k)
-- -- -- -- -- --                  ; (j = i0) → p (i ∨ ~ k)
-- -- -- -- -- --                  ; (j = i1) → p (i ∧ k)})
-- -- -- -- -- --               (p i0)

-- -- -- -- -- --     rotLoop'-filler2 : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → I → I → I → A
-- -- -- -- -- --     rotLoop'-filler2 p k i j =
-- -- -- -- -- --       hfill (λ k → λ { (i = i0) → {!!}
-- -- -- -- -- --                  ; (i = i1) → {!p k!}
-- -- -- -- -- --                  ; (j = i0) → p (i ∨ ~ k)
-- -- -- -- -- --                  ; (j = i1) → p (i ∧ k)})
-- -- -- -- -- --               (inS (p i0))
-- -- -- -- -- --               k

-- -- -- -- -- --     rotLoop'-filler : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → I → I → I → A
-- -- -- -- -- --     rotLoop'-filler p k i j =
-- -- -- -- -- --       hfill (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- -- -- -- -- --                  ; (i = i1) → p (j ∧ k)
-- -- -- -- -- --                  ; (j = i0) → p (i ∨ ~ k)
-- -- -- -- -- --                  ; (j = i1) → p (i ∧ k)})
-- -- -- -- -- --               (inS (p i0))
-- -- -- -- -- --               k

-- -- -- -- -- --     S¹-ind : ∀ {ℓ} {A : S¹ → S¹ → Type ℓ} (f g : (a b : S¹) → A a b)
-- -- -- -- -- --           → (b : f base base ≡ g base base)
-- -- -- -- -- --           → (l : PathP (λ i → f (loop i) base ≡ g (loop i) base) b b)
-- -- -- -- -- --           → (r : PathP (λ i → f base (loop i) ≡ g base (loop i)) b b)
-- -- -- -- -- --           → (x y : S¹) → f x y ≡ g x y
-- -- -- -- -- --     S¹-ind f g b l r x y = {!!}
-- -- -- -- -- --     help : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x)
-- -- -- -- -- --          → refl ≡ p
-- -- -- -- -- --          → (q : p ≡ p)
-- -- -- -- -- --          → Σ[ b ∈ p ∙ p ≡ p ]
-- -- -- -- -- --              Σ[ l ∈ PathP (λ i → b i ≡ b i) (cong (p ∙_) q) q ]
-- -- -- -- -- --                Σ[ r ∈ PathP (λ i → b i ≡ b i) (cong (_∙ p) q) q ]
-- -- -- -- -- --                  (Cube (λ k j → l k j) (λ k j → l k j)
-- -- -- -- -- --                        (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- -- -- -- -- --                        (λ k j → r j k) (λ k j → r j k))
-- -- -- -- -- --     help {x = x} p =
-- -- -- -- -- --       J (λ p _ → (q : p ≡ p)
-- -- -- -- -- --          → Σ[ b ∈ p ∙ p ≡ p ]
-- -- -- -- -- --              Σ[ l ∈ PathP (λ i → b i ≡ b i) (cong (p ∙_) q) q ]
-- -- -- -- -- --                Σ[ r ∈ PathP (λ i → b i ≡ b i) (cong (_∙ p) q) q ]
-- -- -- -- -- --                  (Cube (λ k j → l k j) (λ k j → l k j)
-- -- -- -- -- --                        (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- -- -- -- -- --                        (λ k j → r j k) (λ k j → r j k)))
-- -- -- -- -- --           λ q → (sym (rUnit refl)) , ((λ i j → lUnit (q j) (~ i)) , (((λ i j → rUnit (q j) (~ i)))
-- -- -- -- -- --             , h q {!!}))
-- -- -- -- -- --       where
-- -- -- -- -- --       fill1 : (q : refl {x = x} ≡ refl) -- i j r
-- -- -- -- -- --         → Cube (λ j r s → q j s) (λ j r s → q j s)
-- -- -- -- -- --                 (λ i r → q i) (λ i r → q i)
-- -- -- -- -- --                 (rotLoop' q) (rotLoop' q)
-- -- -- -- -- --       fill1 = {!!}

-- -- -- -- -- --       h : (q : refl {x = x} ≡ refl) → (rotLoop' q ≡ flipSquare (rotLoop' q))
-- -- -- -- -- --         →  Cube (λ k j → lUnit (q j) (~ k)) (λ k j → lUnit (q j) (~ k))
-- -- -- -- -- --                 (λ i j → q i ∙ q j) (λ i j → rotLoop' q i j)
-- -- -- -- -- --                 (λ k j → rUnit (q k) (~ j)) (λ k j → rUnit (q k) (~ j))
-- -- -- -- -- --       h q fl i k j s =
-- -- -- -- -- --         hcomp (λ r → λ { (i = i0) → lUnit (q (j ∨ ~ r)) (~ k) s -- lUnit-filler (q j) r (~ k) s
-- -- -- -- -- --                         ; (i = i1) → lUnit (q (j ∧ r)) (~ k) s -- lUnit-filler (q j) r (~ k) s
-- -- -- -- -- --                         ; (j = i0) → {!rUnit (q (i ∨ ~ r)) (~ k) s!} -- rUnit (q i) (~ k ∧ r) s
-- -- -- -- -- --                         ; (j = i1) → {!!} -- rUnit (q i) (~ k ∧ r) s
-- -- -- -- -- --                         ; (k = i0) → {!!} -- compPath-filler (q i) (q j) r s
-- -- -- -- -- --                         ; (k = i1) → rotLoop'-filler q r i j s -- rotLoop' q i j s
-- -- -- -- -- --                         ; (s = i0) → {!!} -- x
-- -- -- -- -- --                         ; (s = i1) → {!!} }) -- q j (k ∨ r)})
-- -- -- -- -- --               (
-- -- -- -- -- --          hcomp (λ r → λ { (i = i0) → {!!}
-- -- -- -- -- --                         ; (i = i1) → {!!}
-- -- -- -- -- --                         ; (j = i0) → {!!}
-- -- -- -- -- --                         ; (j = i1) → {!!}
-- -- -- -- -- --                         ; (k = i0) → {!!}
-- -- -- -- -- --                         ; (k = i1) → {!lUnit (q (j ∨ ~ r)) (~ k) s -- rotLoop'-filler q r i0 j s!} -- rotLoop'-filler q r i j s -- rotLoop' q j i s -- rotLoop' q i j s
-- -- -- -- -- --                         ; (s = i0) → {!!}
-- -- -- -- -- --                         ; (s = i1) → {!!}}) -- q j k})
-- -- -- -- -- --               (hcomp (λ r → λ { (i = i0) → {!!} -- q (j ∨ ~ r) (k ∧ s)
-- -- -- -- -- --                         ; (i = i1) → {!!} -- q (j ∧ r) (k ∧ s)
-- -- -- -- -- --                         ; (j = i0) → {!q (~ r ∨ i) (~ k ∨ s)!}
-- -- -- -- -- --                         ; (j = i1) → {!!}
-- -- -- -- -- --                         ; (k = i0) → {!!}
-- -- -- -- -- --                         ; (k = i1) → {!!}
-- -- -- -- -- --                         ; (s = i0) → {!!}
-- -- -- -- -- --                         ; (s = i1) → {!!}})
-- -- -- -- -- --                      {!!}))
-- -- -- -- -- --       {-
-- -- -- -- -- -- lUnit-filler : {x y : A} (p : x ≡ y) → I → I → I → A
-- -- -- -- -- -- lUnit-filler {x = x} p j k i =
-- -- -- -- -- --   hfill (λ j → λ { (i = i0) → x
-- -- -- -- -- --                   ; (i = i1) → p (~ k ∨ j )
-- -- -- -- -- --                   ; (k = i0) → p i
-- -- -- -- -- --                -- ; (k = i1) → compPath-filler refl p j i
-- -- -- -- -- --                   }) (inS (p (~ k ∧ i ))) j

-- -- -- -- -- -- i = i0 ⊢ lUnit (q j) (~ k)
-- -- -- -- -- -- i = i1 ⊢ lUnit (q j) (~ k)
-- -- -- -- -- -- k = i0 ⊢ q i ∙ q j
-- -- -- -- -- -- k = i1 ⊢ rotLoop' q i j
-- -- -- -- -- -- j = i0 ⊢ rUnit (q i) (~ k)
-- -- -- -- -- -- j = i1 ⊢ rUnit (q i) (~ k)
-- -- -- -- -- -- -}
-- -- -- -- -- --       {-
-- -- -- -- -- --       hcomp (λ k → λ { (i = i0) → p (j ∨ ~ k)
-- -- -- -- -- --                  ; (i = i1) → p (j ∧ k)
-- -- -- -- -- --                  ; (j = i0) → p (i ∨ ~ k)
-- -- -- -- -- --                  ; (j = i1) → p (i ∧ k)})
-- -- -- -- -- --               (p i0)


-- -- -- -- -- --       i = i0 ⊢ lUnit (q j) (~ k)
-- -- -- -- -- -- i = i1 ⊢ lUnit (q j) (~ k)
-- -- -- -- -- -- j = i0 ⊢ rUnit (q i) (~ k)
-- -- -- -- -- -- j = i1 ⊢ rUnit (q i) (~ k)
-- -- -- -- -- -- k = i0 ⊢ q i ∙ q j
-- -- -- -- -- -- k = i1 ⊢ rotLoop' q i j
-- -- -- -- -- --       -}



-- -- -- -- -- --     rotLoop'-funct : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} {x : A} (p : x ≡ x) (f : A → B)
-- -- -- -- -- --       → rotLoop' (cong f p) ≡ λ i j → f (rotLoop' p i j)
-- -- -- -- -- --     rotLoop'-funct p f k i j = {!!}

-- -- -- -- -- --     inst-help = help (σ (S₊∙ (suc zero)) base) (sym (rCancel (merid base))) (cong (σ (S₊∙ (suc zero))) loop)

-- -- -- -- -- --     E : typ ((Ω^ 2) (S₊∙ 2))
-- -- -- -- -- --     E i = (sym (rCancel (merid base)) ∙∙ (λ i → (merid (loop i) ∙ sym (merid base))) ∙∙ rCancel (merid base)) i

-- -- -- -- -- --     -- S¹ × S¹ → ΩS²

-- -- -- -- -- --     σ' : S¹ → typ (Ω (S₊∙ 2))
-- -- -- -- -- --     σ' base = refl
-- -- -- -- -- --     σ' (loop i) = E i

-- -- -- -- -- --     negi : {!S¹ → S¹!}
-- -- -- -- -- --     negi = {!!}

-- -- -- -- -- --     a+a : (a : S¹) → σ' (a * a) ≡ refl
-- -- -- -- -- --     a+a base = refl
-- -- -- -- -- --     a+a (loop i) j =
-- -- -- -- -- --       hcomp (λ r → λ {(i = i0) → σ' (loop (~ r))
-- -- -- -- -- --                      ; (i = i1) → σ' (loop (r ∨ j))
-- -- -- -- -- --                      ; (j = i0) → σ' (rotLoop'-filler loop r i i)
-- -- -- -- -- --                      ; (j = i1) → σ' (loop (~ r ∧ ~ i))})
-- -- -- -- -- --             {!i₁ = i0 ⊢ lCancel (E i) j
-- -- -- -- -- -- i₁ = i1 ⊢ lCancel (E i) j
-- -- -- -- -- -- i = i0 ⊢ lUnit (E i₁) (~ j)
-- -- -- -- -- -- i = i1 ⊢ lUnit (E i₁) (~ j)
-- -- -- -- -- -- j = i0 ⊢ sym (σ' (loop i)) ∙ σ' (loop i * loop i₁)
-- -- -- -- -- -- j = i1 ⊢ σ' (loop i₁)!}

-- -- -- -- -- --     lUnit' : ∀ {ℓ} {A : Type ℓ} {x y : A} → (p : x ≡ y) → p ≡ refl ∙ p
-- -- -- -- -- --     lUnit' = λ p → compPath-filler' refl p

-- -- -- -- -- --     ff : I → I → I → snd (S₊∙ 2) ≡ snd (S₊∙ 2)
-- -- -- -- -- --     ff r i j =
-- -- -- -- -- --       hfill (λ r → λ {(i = i0) → lUnit' (E (~ r)) (~ j) -- rUnit refl (~ r) j s -- compPath-filler' (E r) refl (~ j) s
-- -- -- -- -- --                      ; (i = i1) → rUnit (E (~ r)) (~ j) -- rUnit refl (~ r) j s -- compPath-filler' {!!} {!!} (~ j) s
-- -- -- -- -- --                      ; (j = i0) → E (~ i ∨ ~ r) ∙ E (i ∨ ~ r)
-- -- -- -- -- --                      ; (j = i1) → E (~ r)}) -- north
-- -- -- -- -- --              (inS (rUnit refl (~ j))) --  (compPath-filler' refl (~ j)))
-- -- -- -- -- --              r

-- -- -- -- -- --     σ'aa : (a b : S¹) → (σ' (invLooper b) ∙ σ' (b * a)) ≡ σ' a
-- -- -- -- -- --     σ'aa a base = sym (lUnit' _) -- sym (compPath-filler' refl _)
-- -- -- -- -- --     σ'aa base (loop i) j =
-- -- -- -- -- --       ff i1 i j
-- -- -- -- -- --     σ'aa (loop i) (loop j)  k s =
-- -- -- -- -- --       hcomp (λ r → λ {(i = i0) → PP r j k s -- ff r j k
-- -- -- -- -- --                      ; (i = i1) → PP r j k s -- ff r j k
-- -- -- -- -- --                      ; (j = i0) → lUnit' (σ' (loop i)) (r ∧ ~ k) s
-- -- -- -- -- --                      ; (j = i1) → lUnit' (σ' (loop i)) (r ∧ ~ k) s
-- -- -- -- -- --                      ; (k = i0) → compPath-filler' (σ' (loop (~ j))) (σ' (loop j * loop i)) r s -- 
-- -- -- -- -- --                      ; (k = i1) → E i s -- E i s
-- -- -- -- -- --                      ; (s = i0) → σ' (loop (~ j)) (~ r ∧ ~ k) -- E (~ j) (~ r ∧ ~ k) -- E (~ j) (~ r)
-- -- -- -- -- --                      ; (s = i1) → north})
-- -- -- -- -- --         (hcomp (λ r → λ {(i = i0) → {!!}
-- -- -- -- -- --                      ; (i = i1) → {!!}
-- -- -- -- -- --                      ; (j = i0) → {!!}
-- -- -- -- -- --                      ; (j = i1) → {!!}
-- -- -- -- -- --                      ; (k = i0) → {!!}
-- -- -- -- -- --                      ; (k = i1) → {!!}
-- -- -- -- -- --                      ; (s = i0) → {!!}
-- -- -- -- -- --                      ; (s = i1) → {!!}})
-- -- -- -- -- --                {!!})
-- -- -- -- -- --     {-
-- -- -- -- -- -- Goal: snd (S₊∙ 2) ≡ snd (S₊∙ 2)
-- -- -- -- -- -- ———— Boundary ——————————————————————————————————————————————
-- -- -- -- -- -- i = i0 ⊢ ff i1 j k
-- -- -- -- -- -- i = i1 ⊢ ff i1 j k
-- -- -- -- -- -- j = i0 ⊢ lUnit (E i) (~ k)
-- -- -- -- -- -- j = i1 ⊢ lUnit (E i) (~ k)
-- -- -- -- -- -- k = i0 ⊢ σ' (invLooper (loop j)) ∙ σ' (loop j * loop i)
-- -- -- -- -- -- k = i1 ⊢ E i-}
-- -- -- -- -- --       where -- j k s
-- -- -- -- -- --       PP3 : Cube (λ j s → north) (λ j s → north)
-- -- -- -- -- --                  (λ j₂ s₂ → E j₂ s₂) (λ j s → north)
-- -- -- -- -- --                  (λ j₂ k₂ → E (~ j₂) (~ k₂)) (λ j s → north)
-- -- -- -- -- --       PP3 j k s =
-- -- -- -- -- --         hcomp (λ r → λ {(j = i0) → E r (~ k)
-- -- -- -- -- --                        ; (j = i1) → E r (s ∧ ~ k) -- E (k ∨ r) (s)
-- -- -- -- -- --                        ; (k = i0) → E (j ∧ r) s
-- -- -- -- -- --                        ; (k = i1) → north
-- -- -- -- -- --                        ; (s = i0) → E (~ j ∧ r) (~ k)
-- -- -- -- -- --                        ; (s = i1) → E r (~ k)})
-- -- -- -- -- --                north

-- -- -- -- -- --       PP :
-- -- -- -- -- --         PathP (λ r → Cube (λ k s → lUnit' (σ' base) (r ∧ ~ k) s) (λ k s → lUnit' (σ' base) (r ∧ ~ k) s)
-- -- -- -- -- --                            (λ j s → compPath-filler' (σ' (loop (~ j))) (σ' (loop j)) r s)
-- -- -- -- -- --                            (λ j s → north)
-- -- -- -- -- --                            (λ j k → σ' (loop (~ j)) (~ r ∧ ~ k))
-- -- -- -- -- --                            λ j k → north)
-- -- -- -- -- --                  PP3
-- -- -- -- -- --               λ j k s → ff i1 j k s
-- -- -- -- -- --       PP =
-- -- -- -- -- --         {!i = i0 ⊢ ff i1 j k
-- -- -- -- -- -- i = i1 ⊢ ff i1 j k
-- -- -- -- -- -- j = i0 ⊢ lUnit (E i) (~ k)
-- -- -- -- -- -- j = i1 ⊢ lUnit (E i) (~ k)
-- -- -- -- -- -- k = i0 ⊢ σ' (invLooper (loop j)) ∙ σ' (loop j * loop i)
-- -- -- -- -- -- k = i1 ⊢ E i!}

-- -- -- -- -- --       help2 : (a : S¹) → PathP (λ i →  cong₂ _∙_ (cong σ' (sym loop)) (cong σ' (rotLoop a)) i ≡ σ' a)
-- -- -- -- -- --                    (sym (lUnit (σ' a))) (sym (lUnit (σ' a)))  -- (σ' a) 
-- -- -- -- -- --       help2 a = flipSquare (({!congFunct σ' (cong (_* a) loop)!}
-- -- -- -- -- --                          ∙ {!!})
-- -- -- -- -- --                          ◁ {!!})

-- -- -- -- -- --     bazonga : (a b : S¹) → (σ' a ∙∙ refl ∙∙ (σ' b))
-- -- -- -- -- --                     ≡ σ' (a * b)
-- -- -- -- -- --     bazonga base base = sym (rUnit refl)
-- -- -- -- -- --     bazonga base (loop i) = sym (lUnit (E i))
-- -- -- -- -- --     bazonga (loop i) base j k = {!doubleCompPath-filler (E i) refl refl (~ j)!}
-- -- -- -- -- --     bazonga (loop i) (loop i₁) = {!!}

-- -- -- -- -- --     σp : (a b : S¹) → (σ' a ∙ (σ' b))
-- -- -- -- -- --                     ≡ σ' (a * b)
-- -- -- -- -- --     σp base base = sym (rUnit refl) -- inst-help .fst
-- -- -- -- -- --     σp base (loop j) = sym (lUnit (E j)) -- inst-help .snd .fst j
-- -- -- -- -- --     σp (loop i) base =  (sym (rUnit (E i))) -- inst-help .snd .snd .fst i
-- -- -- -- -- --     σp (loop i) (loop j) k s =
-- -- -- -- -- --       hcomp (λ r → λ { (i = i0) → lUnit-filler (E j) r (~ k) s
-- -- -- -- -- --                         ; (i = i1) → lUnit-filler (E j) r (~ k) s
-- -- -- -- -- --                         ; (j = i0) → rUnit (E i) (~ k ∧ r) s
-- -- -- -- -- --                         ; (j = i1) → rUnit (E i) (~ k ∧ r) s
-- -- -- -- -- --                         ; (k = i0) → compPath-filler (E i) (E j) r s
-- -- -- -- -- --                         ; (k = i1) → σ' (loop i * loop j) s
-- -- -- -- -- --                         ; (s = i0) → north
-- -- -- -- -- --                         ; (s = i1) → E j (k ∨ r)})
-- -- -- -- -- --             (hcomp (λ r → λ { (i = i0) → σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) ((k ∨ ~ r) ∧ s) -- σ' (loop j) (k ∧ s)
-- -- -- -- -- --                         ; (i = i1) → σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) (s ∧ (k ∨ ~ r)) -- σ' (loop j) (k ∧ (s ∨ ~ r)) -- σ' (loop j) ((k ∨ ~ r) ∧ s) -- σ' (loop j) ((k) ∧ s)
-- -- -- -- -- --                         ; (j = i0) → {!σ' (loop i) s!} -- σ' (loop i) s -- σ' (loop i) (s ∧ r) -- σ' (loop i) s
-- -- -- -- -- --                         ; (j = i1) → {!!} -- σ' (loop i) s -- σ' (loop i) (s ∧ r)
-- -- -- -- -- --                         ; (k = i0) → {!!} -- σ' (loop i) s
-- -- -- -- -- --                         ; (k = i1) → {!!} -- σ' (loop i * loop j) (s ∨ ~ r) -- σ' (loop i * loop j) (s ∧ r) -- σ' (loop i * loop j) s -- σ' (loop i * loop j) s -- rotLoop' q i j s
-- -- -- -- -- --                         ; (s = i0) → σ' (loop j) (k ∧ ~ r) -- σ' base s -- σ' base s -- north
-- -- -- -- -- --                         ; (s = i1) → E j k}) --  σ' (loop j) k})
-- -- -- -- -- --                    {!σ' ? (k ∧ s)!})
-- -- -- -- -- --      where
-- -- -- -- -- --      ss : {!!}
-- -- -- -- -- --      ss = {!!}
-- -- -- -- -- --     {-
-- -- -- -- -- -- i = i0 ⊢ σp base (loop j) k s
-- -- -- -- -- -- i = i1 ⊢ σp base (loop j) k s
-- -- -- -- -- -- j = i0 ⊢ σp (loop i) base k s
-- -- -- -- -- -- j = i1 ⊢ σp (loop i) base k s
-- -- -- -- -- -- k = i0 ⊢ (σ' (loop i) ∙ σ' (loop j)) s
-- -- -- -- -- -- k = i1 ⊢ σ' (loop i * loop j) s
-- -- -- -- -- -- s = i0 ⊢ snd (S₊∙ 2)
-- -- -- -- -- -- s = i1 ⊢ snd (S₊∙ 2) -}


-- -- -- -- -- --     lem : (a b : S¹) → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b)) ∙ (sym (σ (S₊∙ 1) a ∙ σ (S₊∙ 1) (a * b)))
-- -- -- -- -- --                       ≡ {!!}
-- -- -- -- -- --     lem a b = {!i = i0 ⊢ inst-help .snd .fst j k
-- -- -- -- -- -- i = i1 ⊢ inst-help .snd .fst j k
-- -- -- -- -- -- j = i0 ⊢ inst-help .snd .snd .fst i k
-- -- -- -- -- -- j = i1 ⊢ inst-help .snd .snd .fst i k
-- -- -- -- -- -- k = i0 ⊢ σ (S₊∙ 1) (loop i) ∙ σ (S₊∙ 1) (loop j)
-- -- -- -- -- -- k = i1 ⊢ σ (S₊∙ 1)
-- -- -- -- -- --          (hcomp
-- -- -- -- -- --           (λ { k₁ (j = i0) → loop (i ∨ ~ k₁)
-- -- -- -- -- --              ; k₁ (j = i1) → loop (i ∧ k₁)
-- -- -- -- -- --              ; k₁ (i = i0) → loop (j ∨ ~ k₁)
-- -- -- -- -- --              ; k₁ (i = i1) → loop (j ∧ k₁)
-- -- -- -- -- --              })
-- -- -- -- -- --           base)!}

-- -- -- -- -- --     h : (a b : S¹) → cong (fst HopF2') (push a b)
-- -- -- -- -- --                    ≡ ((cong (fst HopF') (push a b ∙ sym (push base b))
-- -- -- -- -- --                    ∙∙ refl ∙ refl
-- -- -- -- -- --                    ∙∙ cong (fst HopF') (push base base ∙∙ sym (push a base) ∙∙ push a b)))
-- -- -- -- -- --     h a b = cong-∙∙ fold⋁ ((λ i → inr (σ (S₊∙ 1) b i))) (sym (push tt)) (λ i → inl (σ (S₊∙ 1) a i))
-- -- -- -- -- --           ∙ (λ _ → σ (S₊∙ 1) b ∙∙ refl ∙∙ σ (S₊∙ 1) a)
-- -- -- -- -- --           ∙ ({!!}
-- -- -- -- -- --           ∙∙ {!sym (σ (S₊∙ 1)  (a * base))!}
-- -- -- -- -- --           ∙∙ {!σ (S₊∙ 1) base!})
-- -- -- -- -- --           ∙ (λ i → (σ (S₊∙ 1) (a * b) ∙ sym (σ (S₊∙ 1) b))
-- -- -- -- -- --                  ∙∙ refl
-- -- -- -- -- --                  ∙∙ (rCancel (merid base) (~ i) ∙∙ sym (σ (S₊∙ 1)  (rUnitS¹ a (~ i))) ∙∙ σ (S₊∙ 1) (a * b)))
-- -- -- -- -- --           ∙ λ i → cong-∙ HopfM (push a b) (sym (push base b)) (~ i)
-- -- -- -- -- --                 ∙∙ rUnit refl i
-- -- -- -- -- --                 ∙∙ cong-∙∙ HopfM (push base base) (sym (push a base)) (push a b) (~ i)
  
-- -- -- -- -- --   id1 : joinify HopF ≡ HopF'
-- -- -- -- -- --   id1 = ΣPathP (funExt (λ x → cong HopfM (S3→joinS¹S¹→S³ x)) , flipSquare (cong (cong HopfM) (rCancel (push base base))))

-- -- -- -- -- --   id2 : joinify HopF2 ≡ HopF2'
-- -- -- -- -- --   id2 = ΣPathP (funExt (λ x → cong (fold⋁ ∘ ∨map) (S3→joinS¹S¹→S³ x)) , flipSquare ((cong (cong (fold⋁ ∘ ∨map)) (rCancel (push base base)))))

-- -- -- -- -- --   l : cong (λ x → HopfM (S3→joinS¹S¹ x)) (merid north) ≡ refl
-- -- -- -- -- --   l = rCancel (merid base)

-- -- -- -- -- --   main : {!rUnit!}
-- -- -- -- -- --   main = {!!}

-- -- -- -- -- --   help : (a : S₊ 2) → cong (fst HopF2) (merid a) ≡ cong (fst (∙Π HopF HopF)) (merid a)
-- -- -- -- -- --   help a = {!cong (λ x → fold⋁ (∨map (S3→joinS¹S¹ x))) (merid a)!}
-- -- -- -- -- --         ∙∙ {!!}
-- -- -- -- -- --         ∙∙ {!!}
-- -- -- -- -- --         ∙∙ cong (λ x → x ∙ x) (rUnit (cong (fst HopF) (merid a))
-- -- -- -- -- --                          ∙ cong (cong (fst HopF) (merid a) ∙_) (cong sym (sym l))
-- -- -- -- -- --                          ∙ sym (cong-∙ (fst HopF) (merid a) (sym (merid north))))
-- -- -- -- -- --         ∙∙ λ i → rUnit (cong (fst HopF) (merid a ∙ sym (merid (ptSn 2)))) i
-- -- -- -- -- --          ∙ rUnit (cong (fst HopF) (merid a ∙ sym (merid (ptSn 2)))) i

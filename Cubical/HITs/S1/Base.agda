{-

Definition of the circle as a HIT with a proof that Ω(S¹) ≡ ℤ

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.S1.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
  hiding (_+_ ; _·_ ; +-assoc ; +-comm)
open import Cubical.Data.Int hiding (_·_)

data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

-- Check that transp is the identity function for S¹
module _ where
  transpS¹ : ∀ (φ : I) (u0 : S¹) → transp (λ _ → S¹) φ u0 ≡ u0
  transpS¹ φ u0 = refl

  compS1 : ∀ (φ : I) (u : ∀ i → Partial φ S¹) (u0 : S¹ [ φ ↦ u i0 ]) →
    comp (λ _ → S¹) (\ i → u i) (outS u0) ≡ hcomp u (outS u0)
  compS1 φ u u0 = refl

-- ΩS¹ ≡ ℤ
helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPathℤ i

ΩS¹ : Type₀
ΩS¹ = base ≡ base

encode : ∀ x → base ≡ x → helix x
encode x p = subst helix p (pos zero)

winding : ΩS¹ → ℤ
winding = encode base

intLoop : ℤ → ΩS¹
intLoop (pos zero)       = refl
intLoop (pos (suc n))    = intLoop (pos n) ∙ loop
intLoop (negsuc zero)    = sym loop
intLoop (negsuc (suc n)) = intLoop (negsuc n) ∙ sym loop

decodeSquare : (n : ℤ) → PathP (λ i → base ≡ loop i) (intLoop (predℤ n)) (intLoop n)
decodeSquare (pos zero) i j    = loop (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → base
                                                ; (j = i1) → loop k } )
                                       (inS (intLoop (pos n) j)) i
decodeSquare (negsuc n) i j = hfill (λ k → λ { (j = i0) → base
                                             ; (j = i1) → loop (~ k) })
                                    (inS (intLoop (negsuc n) j)) (~ i)

decode : (x : S¹) → helix x → base ≡ x
decode base         = intLoop
decode (loop i) y j =
  let n : ℤ
      n = unglue (i ∨ ~ i) y
  in hcomp (λ k → λ { (i = i0) → intLoop (predSuc y k) j
                    ; (i = i1) → intLoop y j
                    ; (j = i0) → base
                    ; (j = i1) → loop i })
           (decodeSquare n i j)

decodeEncode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = J (λ y q → decode y (encode y q) ≡ q) (λ _ → refl) p

isSetΩS¹ : isSet ΩS¹
isSetΩS¹ p q r s j i =
  hcomp (λ k → λ { (i = i0) → decodeEncode base p k
                 ; (i = i1) → decodeEncode base q k
                 ; (j = i0) → decodeEncode base (r i) k
                 ; (j = i1) → decodeEncode base (s i) k })
        (decode base (isSetℤ (winding p) (winding q) (cong winding r) (cong winding s) j i))

-- This proof does not rely on rewriting hcomp with empty systems in
-- ℤ as ghcomp has been implemented!
windingℤLoop : (n : ℤ) → winding (intLoop n) ≡ n
windingℤLoop (pos zero)       = refl
windingℤLoop (pos (suc n))    = cong sucℤ (windingℤLoop (pos n))
windingℤLoop (negsuc zero)    = refl
windingℤLoop (negsuc (suc n)) = cong predℤ (windingℤLoop (negsuc n))

ΩS¹Isoℤ : Iso ΩS¹ ℤ
Iso.fun ΩS¹Isoℤ      = winding
Iso.inv ΩS¹Isoℤ      = intLoop
Iso.rightInv ΩS¹Isoℤ = windingℤLoop
Iso.leftInv ΩS¹Isoℤ  = decodeEncode base

ΩS¹≡ℤ : ΩS¹ ≡ ℤ
ΩS¹≡ℤ = isoToPath ΩS¹Isoℤ

-- intLoop and winding are group homomorphisms
private
  intLoop-sucℤ : (z : ℤ) → intLoop (sucℤ z) ≡ intLoop z ∙ loop
  intLoop-sucℤ (pos n)          = refl
  intLoop-sucℤ (negsuc zero)    = sym (lCancel loop)
  intLoop-sucℤ (negsuc (suc n)) =
      rUnit (intLoop (negsuc n))
    ∙ (λ i → intLoop (negsuc n) ∙ lCancel loop (~ i))
    ∙ assoc (intLoop (negsuc n)) (sym loop) loop

  intLoop-predℤ : (z : ℤ) → intLoop (predℤ z) ≡ intLoop z ∙ sym loop
  intLoop-predℤ (pos zero)    = lUnit (sym loop)
  intLoop-predℤ (pos (suc n)) =
      rUnit (intLoop (pos n))
    ∙ (λ i → intLoop (pos n) ∙ (rCancel loop (~ i)))
    ∙ assoc (intLoop (pos n)) loop (sym loop)
  intLoop-predℤ (negsuc n)    = refl

intLoop-hom : (a b : ℤ) → (intLoop a) ∙ (intLoop b) ≡ intLoop (a + b)
intLoop-hom a (pos zero)       = sym (rUnit (intLoop a))
intLoop-hom a (pos (suc n))    =
    assoc (intLoop a) (intLoop (pos n)) loop
  ∙ (λ i → (intLoop-hom a (pos n) i) ∙ loop)
  ∙ sym (intLoop-sucℤ (a + pos n))
intLoop-hom a (negsuc zero)    = sym (intLoop-predℤ a)
intLoop-hom a (negsuc (suc n)) =
    assoc (intLoop a) (intLoop (negsuc n)) (sym loop)
  ∙ (λ i → (intLoop-hom a (negsuc n) i) ∙ (sym loop))
  ∙ sym (intLoop-predℤ (a + negsuc n))

winding-hom : (a b : ΩS¹) → winding (a ∙ b) ≡ (winding a) + (winding b)
winding-hom a b i =
  hcomp (λ t → λ { (i = i0) → winding (decodeEncode base a t ∙ decodeEncode base b t)
                 ; (i = i1) → windingℤLoop (winding a + winding b) t })
        (winding (intLoop-hom (winding a) (winding b) i))

-- Commutativity
comm-ΩS¹ : (p q : ΩS¹) → p ∙ q ≡ q ∙ p
comm-ΩS¹ p q = sym (cong₂ (_∙_) (decodeEncode base p) (decodeEncode base q))
             ∙ intLoop-hom (winding p) (winding q)
             ∙ cong intLoop (+Comm (winding p) (winding q))
             ∙ sym (intLoop-hom (winding q) (winding p))
             ∙ (cong₂ (_∙_) (decodeEncode base q) (decodeEncode base p))

-- Based homotopy group

basedΩS¹ : (x : S¹) → Type₀
basedΩS¹ x = x ≡ x

-- Proof that the homotopy group is actually independent on the basepoint
-- first, give a quasi-inverse to the basechange basedΩS¹→ΩS¹ for any loop i
-- (which does *not* match at endpoints)
private
  ΩS¹→basedΩS¹-filler : I → I → ΩS¹ → I → S¹
  ΩS¹→basedΩS¹-filler l i x j =
    hfill (λ t → λ { (j = i0) → loop (i ∧ t)
                   ; (j = i1) → loop (i ∧ t) })
          (inS (x j)) l

  basedΩS¹→ΩS¹-filler : (_ i : I) → basedΩS¹ (loop i) → I → S¹
  basedΩS¹→ΩS¹-filler l i x j =
    hfill (λ t → λ { (j = i0) → loop (i ∧ (~ t))
                   ; (j = i1) → loop (i ∧ (~ t)) })
          (inS (x j)) l

  ΩS¹→basedΩS¹ : (i : I) → ΩS¹ → basedΩS¹ (loop i)
  ΩS¹→basedΩS¹ i x j = ΩS¹→basedΩS¹-filler i1 i x j

  basedΩS¹→ΩS¹ : (i : I) → basedΩS¹ (loop i) → ΩS¹
  basedΩS¹→ΩS¹ i x j = basedΩS¹→ΩS¹-filler i1 i x j



  basedΩS¹→ΩS¹→basedΩS¹ : (i : I) → (x : basedΩS¹ (loop i))
                          → ΩS¹→basedΩS¹ i (basedΩS¹→ΩS¹ i x) ≡ x
  basedΩS¹→ΩS¹→basedΩS¹ i x j k =
    hcomp (λ t → λ { (j = i1) → basedΩS¹→ΩS¹-filler (~ t) i x k
                   ; (j = i0) → ΩS¹→basedΩS¹ i (basedΩS¹→ΩS¹ i x) k
                   ; (k = i0) → loop (i ∧ (t ∨ (~ j)))
                   ; (k = i1) → loop (i ∧ (t ∨ (~ j))) })
          (ΩS¹→basedΩS¹-filler (~ j) i (basedΩS¹→ΩS¹ i x) k)

  ΩS¹→basedΩS¹→ΩS¹ : (i : I) → (x : ΩS¹)
                          → basedΩS¹→ΩS¹ i (ΩS¹→basedΩS¹ i x) ≡ x
  ΩS¹→basedΩS¹→ΩS¹ i x j k =
    hcomp (λ t → λ { (j = i1) → ΩS¹→basedΩS¹-filler (~ t) i x k
                   ; (j = i0) → basedΩS¹→ΩS¹ i (ΩS¹→basedΩS¹ i x) k
                   ; (k = i0) → loop (i ∧ ((~ t) ∧ j))
                   ; (k = i1) → loop (i ∧ ((~ t) ∧ j)) })
          (basedΩS¹→ΩS¹-filler (~ j) i (ΩS¹→basedΩS¹ i x) k)

  -- from the existence of our quasi-inverse, we deduce that the basechange is an equivalence
  -- for all loop i

  basedΩS¹→ΩS¹-isequiv : (i : I) → isEquiv (basedΩS¹→ΩS¹ i)
  basedΩS¹→ΩS¹-isequiv i = isoToIsEquiv (iso (basedΩS¹→ΩS¹ i) (ΩS¹→basedΩS¹ i)
                   (ΩS¹→basedΩS¹→ΩS¹ i) (basedΩS¹→ΩS¹→basedΩS¹ i))


  -- now extend the basechange so that both ends match
  -- (and therefore we get a basechange for any x : S¹)

  loop-conjugation : basedΩS¹→ΩS¹ i1 ≡ λ x → x
  loop-conjugation i x =
    let p = (doubleCompPath-elim loop x (sym loop))
            ∙ (λ i → (lUnit loop i ∙ x) ∙ sym loop)
    in
    ((sym (decodeEncode base (basedΩS¹→ΩS¹ i1 x)))
    ∙ (λ t → intLoop (winding (p t)))
    ∙ (λ t → intLoop (winding-hom (intLoop (pos (suc zero)) ∙ x)
                                  (intLoop (negsuc zero)) t))
    ∙ (λ t → intLoop ((winding-hom (intLoop (pos (suc zero))) x t)
                      + (windingℤLoop (negsuc zero) t)))
    ∙ (λ t → intLoop (((windingℤLoop (pos (suc zero)) t) + (winding x)) + (negsuc zero)))
    ∙ (λ t → intLoop ((+Comm (pos (suc zero)) (winding x) t) + (negsuc zero)))
    ∙ (λ t → intLoop (+Assoc (winding x) (pos (suc zero)) (negsuc zero) (~ t)))
    ∙ (decodeEncode base x)) i

  refl-conjugation : basedΩS¹→ΩS¹ i0 ≡ λ x → x
  refl-conjugation i x j =
    hfill (λ t → λ { (j = i0) → base
                   ; (j = i1) → base })
          (inS (x j)) (~ i)

  basechange : (x : S¹) → basedΩS¹ x → ΩS¹
  basechange base y = y
  basechange (loop i) y =
    hcomp (λ t → λ { (i = i0) → refl-conjugation t y
                   ; (i = i1) → loop-conjugation t y })
          (basedΩS¹→ΩS¹ i y)

  -- for any loop i, the old basechange is equal to the new one
  basedΩS¹→ΩS¹≡basechange : (i : I) → basedΩS¹→ΩS¹ i ≡ basechange (loop i)
  basedΩS¹→ΩS¹≡basechange i j y =
    hfill (λ t → λ { (i = i0) → refl-conjugation t y
                   ; (i = i1) → loop-conjugation t y })
          (inS (basedΩS¹→ΩS¹ i y)) j

  -- so for any loop i, the extended basechange is an equivalence
  basechange-isequiv-aux : (i : I) → isEquiv (basechange (loop i))
  basechange-isequiv-aux i =
    transport (λ j → isEquiv (basedΩS¹→ΩS¹≡basechange i j)) (basedΩS¹→ΩS¹-isequiv i)


  -- as being an equivalence is contractible, basechange is an equivalence for all x : S¹
  basechange-isequiv : (x : S¹) → isEquiv (basechange x)
  basechange-isequiv base = basechange-isequiv-aux i0
  basechange-isequiv (loop i) =
    hcomp (λ t → λ { (i = i0) → basechange-isequiv-aux i0
                   ; (i = i1) → isPropIsEquiv (basechange base) (basechange-isequiv-aux i1)
                                              (basechange-isequiv-aux i0) t })
          (basechange-isequiv-aux i)

  basedΩS¹≡ΩS¹' : (x : S¹) → basedΩS¹ x ≡ ΩS¹
  basedΩS¹≡ΩS¹' x = ua (basechange x , basechange-isequiv x)

  basedΩS¹≡ℤ' : (x : S¹) → basedΩS¹ x ≡ ℤ
  basedΩS¹≡ℤ' x = (basedΩS¹≡ΩS¹' x) ∙ ΩS¹≡ℤ


---- Alternative proof of the same thing -----

toPropElim : ∀ {ℓ} {B : S¹ → Type ℓ}
             → ((s : S¹) → isProp (B s))
             → B base
             → (s : S¹) → B s
toPropElim isprop b base = b
toPropElim isprop b (loop i) =
  isOfHLevel→isOfHLevelDep 1 isprop b b loop i

toPropElim2 : ∀ {ℓ} {B : S¹ → S¹ → Type ℓ}
             → ((s t : S¹) → isProp (B s t))
             → B base base
             → (s t : S¹) → B s t
toPropElim2 isprop b base base = b
toPropElim2 isprop b base (loop i) =
  isProp→PathP (λ i → isprop base (loop i)) b b i
toPropElim2 isprop b (loop i) base =
  isProp→PathP (λ i → isprop (loop i) base) b b i
toPropElim2 {B = B} isprop b (loop i) (loop j) =
  isSet→SquareP (λ _ _ → isOfHLevelSuc 1 (isprop _ _))
    (isProp→PathP (λ i₁ → isprop base (loop i₁)) b b)
    (isProp→PathP (λ i₁ → isprop base (loop i₁)) b b)
    (isProp→PathP (λ i₁ → isprop (loop i₁) base) b b)
    (isProp→PathP (λ i₁ → isprop (loop i₁) base) b b) i j

toSetElim2 : ∀ {ℓ} {B : S¹ → S¹ → Type ℓ}
             → ((s t : S¹) → isSet (B s t))
             → (x : B base base)
             → PathP (λ i → B base (loop i)) x x
             → PathP (λ i → B (loop i) base) x x
             → (s t : S¹) → B s t
toSetElim2 isset b right left base base = b
toSetElim2 isset b right left base (loop i) = right i
toSetElim2 isset b right left (loop i) base = left i
toSetElim2 isset b right left (loop i) (loop j) =
  isSet→SquareP (λ _ _ → isset _ _) right right left left i j

isSetΩx : (x : S¹) → isSet (x ≡ x)
isSetΩx = toPropElim (λ _ → isPropIsSet) isSetΩS¹

basechange2 : (x : S¹) → ΩS¹ → (x ≡ x)
basechange2 base p = p
basechange2 (loop i) p =
  hcomp (λ k → λ { (i = i0) → lUnit (rUnit p (~ k)) (~ k)
                 ; (i = i1) → (cong ((sym loop) ∙_) (comm-ΩS¹ p loop)
                             ∙ assoc (sym loop) loop p
                             ∙ cong (_∙ p) (lCancel loop)
                             ∙ sym (lUnit _)) k })
        ((λ j → loop (~ j ∧ i)) ∙ p ∙ λ j → loop (j ∧ i))
basechange2⁻ : (x : S¹) → (x ≡ x) → ΩS¹
basechange2⁻ base p = p
basechange2⁻ (loop i) p =
  hcomp (λ k → λ { (i = i0) → lUnit (rUnit p (~ k)) (~ k)
                 ; (i = i1) → (cong (loop ∙_) (comm-ΩS¹ p (sym loop))
                             ∙ assoc loop (sym loop) p
                             ∙ cong (_∙ p) (rCancel loop)
                             ∙ sym (lUnit _)) k })
        ((λ j → loop (i ∧ j)) ∙ p ∙ λ j → loop (i ∧ (~ j)))
basechange2-sect : (x : S¹) → section (basechange2 x) (basechange2⁻ x)
basechange2-sect =
  toPropElim (λ _ → isOfHLevelΠ 1 λ _ → isSetΩx _ _ _ )
             λ _ → refl

basechange2-retr : (x : S¹) → retract (basechange2 x) (basechange2⁻ x)
basechange2-retr =
  toPropElim (λ s → isOfHLevelΠ 1 λ x → isSetΩx _ _ _)
             λ _ → refl

Iso-basedΩS¹-ΩS¹ : (x : S¹) → Iso (basedΩS¹ x) ΩS¹
Iso.fun (Iso-basedΩS¹-ΩS¹ x) = basechange2⁻ x
Iso.inv (Iso-basedΩS¹-ΩS¹ x) = basechange2 x
Iso.rightInv (Iso-basedΩS¹-ΩS¹ x) = basechange2-retr x
Iso.leftInv (Iso-basedΩS¹-ΩS¹ x) = basechange2-sect x

Iso-basedΩS¹-ℤ : (x : S¹) → Iso (basedΩS¹ x) ℤ
Iso-basedΩS¹-ℤ x = compIso (Iso-basedΩS¹-ΩS¹ x) ΩS¹Isoℤ

basedΩS¹≡ℤ : (x : S¹) → basedΩS¹ x ≡ ℤ
basedΩS¹≡ℤ x = isoToPath (Iso-basedΩS¹-ℤ x)

-- baschange2⁻ is a morphism

basechange2⁻-morph : (x : S¹) (p q : x ≡ x) →
                     basechange2⁻ x (p ∙ q) ≡ basechange2⁻ x p ∙ basechange2⁻ x q
basechange2⁻-morph =
  toPropElim {B = λ x → (p q : x ≡ x) → basechange2⁻ x (p ∙ q) ≡ basechange2⁻ x p ∙ basechange2⁻ x q}
             (λ _ → isPropΠ2 λ _ _ → isSetΩS¹ _ _)
             λ _ _ → refl

-- Some tests
module _ where
 private
  test-winding-pos : winding (intLoop (pos 5)) ≡ pos 5
  test-winding-pos = refl

  test-winding-neg : winding (intLoop (negsuc 5)) ≡ negsuc 5
  test-winding-neg = refl

-- the inverse when S¹ is seen as a group

invLooper : S¹ → S¹
invLooper base = base
invLooper (loop i) = loop (~ i)

invInvolutive : section invLooper invLooper
invInvolutive base = refl
invInvolutive (loop i) = refl

invS¹Equiv : S¹ ≃ S¹
invS¹Equiv = isoToEquiv theIso
  where
  theIso : Iso S¹ S¹
  Iso.fun theIso = invLooper
  Iso.inv theIso = invLooper
  Iso.rightInv theIso = invInvolutive
  Iso.leftInv theIso = invInvolutive

invS¹Path : S¹ ≡ S¹
invS¹Path = ua invS¹Equiv

-- rot, used in the Hopf fibration
-- we will denote rotation by _·_
-- it is called μ in the HoTT-book in "8.5.2 The Hopf construction"

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

_·_ : S¹ → S¹ → S¹
base     · x = x
(loop i) · x = rotLoop x i

infixl 30 _·_


-- rot i j = filler-rot i j i1
filler-rot : I → I → I → S¹
filler-rot i j = hfill (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                   ; (i = i1) → loop (j ∧ k)
                   ; (j = i0) → loop (i ∨ ~ k)
                   ; (j = i1) → loop (i ∧ k) }) (inS base)

isPropFamS¹ : ∀ {ℓ} (P : S¹ → Type ℓ) (pP : (x : S¹) → isProp (P x)) (b0 : P base) →
              PathP (λ i → P (loop i)) b0 b0
isPropFamS¹ P pP b0 i = pP (loop i) (transp (λ j → P (loop (i ∧ j))) (~ i) b0)
                                    (transp (λ j → P (loop (i ∨ ~ j))) i b0) i

rotIsEquiv : (a : S¹) → isEquiv (a ·_)
rotIsEquiv base = idIsEquiv S¹
rotIsEquiv (loop i) = isPropFamS¹ (λ x → isEquiv (x ·_))
                                  (λ x → isPropIsEquiv (x ·_))
                                  (idIsEquiv _) i

-- more direct definition of the rot (loop i) equivalence

rotLoopInv : (a : S¹) → PathP (λ i → rotLoop (rotLoop a (~ i)) i ≡ a) refl refl
rotLoopInv a i j = homotopySymInv rotLoop a j i

rotLoopEquiv : (i : I) → S¹ ≃ S¹
rotLoopEquiv i =
  isoToEquiv
    (iso (λ a → rotLoop a i)
         (λ a → rotLoop a (~ i))
         (λ a → rotLoopInv a i)
         (λ a → rotLoopInv a (~ i)))

-- some cancellation laws, used in the Hopf fibration
private
  rotInv-aux-1 : I → I → I → I → S¹
  rotInv-aux-1 j k i =
    hfill (λ l → λ { (k = i0) → (loop (i ∧ ~ l)) · loop j
                   ; (k = i1) → loop j
                   ; (i = i0) → (loop k · loop j) · loop (~ k)
                   ; (i = i1) → loop (~ k ∧ ~ l) · loop j })
          (inS ((loop (k ∨ i) · loop j) · loop (~ k)))

  rotInv-aux-2 : I → I → I → S¹
  rotInv-aux-2 i j k =
     hcomp (λ l → λ { (k = i0) → invLooper (filler-rot (~ i) (~ j) l)
                    ; (k = i1) → loop (j ∧ l)
                    ; (i = i0) → filler-rot k j l
                    ; (i = i1) → loop (j ∧ l)
                    ; (j = i0) → loop (i ∨ k ∨ (~ l))
                    ; (j = i1) → loop ((i ∨ k) ∧ l) })
           (base)

  rotInv-aux-3 : I → I → I → I → S¹
  rotInv-aux-3 j k i =
    hfill (λ l → λ { (k = i0) → rotInv-aux-2 i j l
                   ; (k = i1) → loop j
                   ; (i = i0) → loop (k ∨ l) · loop j
                   ; (i = i1) → loop k · (invLooper (loop (~ j) · loop k)) })
          (inS (loop k · (invLooper (loop (~ j) · loop (k ∨ ~ i)))))

  rotInv-aux-4 : I → I → I → I → S¹
  rotInv-aux-4 j k i =
    hfill (λ l → λ { (k = i0) → rotInv-aux-2 i j l
                   ; (k = i1) → loop j
                   ; (i = i0) → loop j · loop (k ∨ l)
                   ; (i = i1) → (invLooper (loop (~ j) · loop k)) · loop k })
          (inS ((invLooper (loop (~ j) · loop (k ∨ ~ i))) · loop k))

rotInv-1 : (a b : S¹) → b · a · invLooper b ≡ a
rotInv-1 base base i = base
rotInv-1 base (loop k) i = rotInv-aux-1 i0 k i i1
rotInv-1 (loop j) base i = loop j
rotInv-1 (loop j) (loop k) i = rotInv-aux-1 j k i i1

rotInv-2 : (a b : S¹) → invLooper b · a · b ≡ a
rotInv-2 base base i = base
rotInv-2 base (loop k) i = rotInv-aux-1 i0 (~ k) i i1
rotInv-2 (loop j) base i = loop j
rotInv-2 (loop j) (loop k) i = rotInv-aux-1 j (~ k) i i1

rotInv-3 : (a b : S¹) → b · (invLooper (invLooper a · b)) ≡ a
rotInv-3 base base i = base
rotInv-3 base (loop k) i = rotInv-aux-3 i0 k (~ i) i1
rotInv-3 (loop j) base i = loop j
rotInv-3 (loop j) (loop k) i = rotInv-aux-3 j k (~ i) i1

rotInv-4 : (a b : S¹) → invLooper (b · invLooper a) · b ≡ a
rotInv-4 base base i = base
rotInv-4 base (loop k) i = rotInv-aux-4 i0 k (~ i) i1
rotInv-4 (loop j) base i = loop j
rotInv-4 (loop j) (loop k) i = rotInv-aux-4 j k (~ i) i1

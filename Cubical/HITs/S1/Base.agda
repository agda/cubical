{-

Definition of the circle as a HIT with a proof that Ω(S¹) ≡ ℤ

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S1.Base where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
  hiding (_+_ ; _*_ ; +-assoc ; +-comm)
open import Cubical.Data.Int

data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

-- Check that transp is the identity function for S¹
module _ where
  transpS¹ : ∀ (φ : I) (u0 : S¹) → transp (λ _ → S¹) φ u0 ≡ u0
  transpS¹ φ u0 = refl

  compS1 : ∀ (φ : I) (u : ∀ i → Partial φ S¹) (u0 : S¹ [ φ ↦ u i0 ]) →
    comp (λ _ → S¹) _ u (outS u0) ≡ hcomp u (outS u0)
  compS1 φ u u0 = refl

helix : S¹ → Type₀
helix base     = Int
helix (loop i) = sucPathInt i

ΩS¹ : Type₀
ΩS¹ = base ≡ base

encode : ∀ x → base ≡ x → helix x
encode x p = subst helix p (pos zero)

winding : ΩS¹ → Int
winding = encode base

intLoop : Int → ΩS¹
intLoop (pos zero)       = refl
intLoop (pos (suc n))    = (intLoop (pos n)) ∙ loop
intLoop (negsuc zero)    = sym loop
intLoop (negsuc (suc n)) = (intLoop (negsuc n)) ∙ (sym loop)

decodeSquare : (n : Int) → PathP (λ i → base ≡ loop i) (intLoop (predInt n)) (intLoop n)
decodeSquare (pos zero) i j    = loop (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → base
                                                ; (j = i1) → loop k } )
                                       (inS (intLoop (pos n) j)) i
decodeSquare (negsuc n) i j = hcomp (λ k → λ { (i = i1) → intLoop (negsuc n) j
                                             ; (j = i0) → base
                                             ; (j = i1) → loop (i ∨ ~ k) })
                                    (intLoop (negsuc n) j)

decode : (x : S¹) → helix x → base ≡ x
decode base         = intLoop
decode (loop i) y j =
  let n : Int
      n = unglue (i ∨ ~ i) y
  in hcomp (λ k → λ { (i = i0) → intLoop (predSuc y k) j
                    ; (i = i1) → intLoop y j
                    ; (j = i0) → base
                    ; (j = i1) → loop i })
           (decodeSquare n i j)

decodeEncode : (x : S¹) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = J (λ y q → decode y (encode y q) ≡ q) (λ x → refl) p

isSetΩS¹ : isSet ΩS¹
isSetΩS¹ p q r s j i =
  hcomp (λ k → λ { (i = i0) → decodeEncode base p k
                 ; (i = i1) → decodeEncode base q k
                 ; (j = i0) → decodeEncode base (r i) k
                 ; (j = i1) → decodeEncode base (s i) k })
        (decode base (isSetInt (winding p) (winding q) (cong winding r) (cong winding s) j i))

-- This proof does not rely on rewriting hcomp with empty systems in
-- Int as ghcomp has been implemented!
windingIntLoop : (n : Int) → winding (intLoop n) ≡ n
windingIntLoop (pos zero)       = refl
windingIntLoop (pos (suc n))    = λ i → sucInt (windingIntLoop (pos n) i)
windingIntLoop (negsuc zero)    = refl
windingIntLoop (negsuc (suc n)) = λ i → predInt (windingIntLoop (negsuc n) i)

ΩS¹≡Int : ΩS¹ ≡ Int
ΩS¹≡Int = isoToPath (iso winding (decode base) windingIntLoop (decodeEncode base))

-- intLoop and winding are group homomorphisms
private
  intLoop-sucInt : (z : Int) → intLoop (sucInt z) ≡ (intLoop z) ∙ loop
  intLoop-sucInt (pos n)          = refl
  intLoop-sucInt (negsuc zero)    = sym (lCancel loop)
  intLoop-sucInt (negsuc (suc n)) =
    (rUnit (intLoop (negsuc n)))
    ∙ (λ i → intLoop (negsuc n) ∙ (lCancel loop (~ i)))
    ∙ (assoc (intLoop (negsuc n)) (sym loop) loop)

  intLoop-predInt : (z : Int) → intLoop (predInt z) ≡ (intLoop z) ∙ (sym loop)
  intLoop-predInt (pos zero)    = lUnit (sym loop)
  intLoop-predInt (pos (suc n)) =
    (rUnit (intLoop (pos n)))
    ∙ (λ i → intLoop (pos n) ∙ (rCancel loop (~ i)))
    ∙ (assoc (intLoop (pos n)) loop (sym loop))
  intLoop-predInt (negsuc n)    = refl

intLoop-hom : (a b : Int) → (intLoop a) ∙ (intLoop b) ≡ intLoop (a + b)
intLoop-hom a (pos zero)       = sym (rUnit (intLoop a))
intLoop-hom a (pos (suc n))    =
  (assoc (intLoop a) (intLoop (pos n)) loop)
  ∙ (λ i → (intLoop-hom a (pos n) i) ∙ loop)
  ∙ (sym (intLoop-sucInt (a + pos n)))
intLoop-hom a (negsuc zero)    = sym (intLoop-predInt a)
intLoop-hom a (negsuc (suc n)) =
  (assoc (intLoop a) (intLoop (negsuc n)) (sym loop))
  ∙ (λ i → (intLoop-hom a (negsuc n) i) ∙ (sym loop))
  ∙ (sym (intLoop-predInt (a + negsuc n)))

winding-hom : (a b : ΩS¹) → winding (a ∙ b) ≡ (winding a) + (winding b)
winding-hom a b i =
  hcomp (λ t → λ { (i = i0) → winding ((decodeEncode base a t) ∙ (decodeEncode base b t))
                 ; (i = i1) → windingIntLoop ((winding a) + (winding b)) t })
        (winding (intLoop-hom (winding a) (winding b) i))

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

private
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
                      + (windingIntLoop (negsuc zero) t)))
    ∙ (λ t → intLoop (((windingIntLoop (pos (suc zero)) t) + (winding x)) + (negsuc zero)))
    ∙ (λ t → intLoop ((+-comm (pos (suc zero)) (winding x) t) + (negsuc zero)))
    ∙ (λ t → intLoop (+-assoc (winding x) (pos (suc zero)) (negsuc zero) (~ t)))
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

  basedΩS¹≡ΩS¹ : (x : S¹) → basedΩS¹ x ≡ ΩS¹
  basedΩS¹≡ΩS¹ x = ua (basechange x , basechange-isequiv x)

basedΩS¹≡Int : (x : S¹) → basedΩS¹ x ≡ Int
basedΩS¹≡Int x = (basedΩS¹≡ΩS¹ x) ∙ ΩS¹≡Int


-- Some tests
module _ where
 private
  five : ℕ
  five = suc (suc (suc (suc (suc zero))))

  test-winding-pos : winding (intLoop (pos five)) ≡ pos five
  test-winding-pos = refl

  test-winding-neg : winding (intLoop (negsuc five)) ≡ negsuc five
  test-winding-neg = refl

-- the inverse when S¹ is seen as a group

inv : S¹ → S¹
inv base = base
inv (loop i) = loop (~ i)

-- rot, used in the Hopf fibration

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

rot : S¹ → S¹ → S¹
rot base x     = x
rot (loop i) x = rotLoop x i

_*_ : S¹ → S¹ → S¹
a * b = rot a b

infixl 30 _*_


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

rotIsEquiv : (a : S¹) → isEquiv (rot a)
rotIsEquiv base = idIsEquiv S¹
rotIsEquiv (loop i) = isPropFamS¹ (λ x → isEquiv (rot x))
                                  (λ x → isPropIsEquiv (rot x))
                                  (idIsEquiv _) i

-- more direct definition of the rot (loop i) equivalence

rotLoopInv : (a : S¹) → PathP (λ i → rotLoop (rotLoop a (~ i)) i ≡ a) refl refl
rotLoopInv a i j =
  hcomp
    (λ k → λ {
      (i = i0) → a;
      (i = i1) → rotLoop a (j ∧ ~ k);
      (j = i0) → rotLoop (rotLoop a (~ i)) i;
      (j = i1) → rotLoop a (i ∧ ~ k)})
    (rotLoop (rotLoop a (~ i ∨ j)) i)

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
    hfill (λ l → λ { (k = i0) → (loop (i ∧ ~ l)) * loop j
                   ; (k = i1) → loop j
                   ; (i = i0) → (loop k * loop j) * loop (~ k)
                   ; (i = i1) → loop (~ k ∧ ~ l) * loop j })
          (inS ((loop (k ∨ i) * loop j) * loop (~ k)))

  rotInv-aux-2 : I → I → I → S¹
  rotInv-aux-2 i j k =
     hcomp (λ l → λ { (k = i0) → inv (filler-rot (~ i) (~ j) l)
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
                   ; (i = i0) → loop (k ∨ l) * loop j
                   ; (i = i1) → loop k * (inv (loop (~ j) * loop k)) })
          (inS (loop k * (inv (loop (~ j) * loop (k ∨ ~ i)))))

  rotInv-aux-4 : I → I → I → I → S¹
  rotInv-aux-4 j k i =
    hfill (λ l → λ { (k = i0) → rotInv-aux-2 i j l
                   ; (k = i1) → loop j
                   ; (i = i0) → loop j * loop (k ∨ l)
                   ; (i = i1) → (inv (loop (~ j) * loop k)) * loop k })
          (inS ((inv (loop (~ j) * loop (k ∨ ~ i))) * loop k))

rotInv-1 : (a b : S¹) → b * a * inv b ≡ a
rotInv-1 base base i = base
rotInv-1 base (loop k) i = rotInv-aux-1 i0 k i i1
rotInv-1 (loop j) base i = loop j
rotInv-1 (loop j) (loop k) i = rotInv-aux-1 j k i i1

rotInv-2 : (a b : S¹) → inv b * a * b ≡ a
rotInv-2 base base i = base
rotInv-2 base (loop k) i = rotInv-aux-1 i0 (~ k) i i1
rotInv-2 (loop j) base i = loop j
rotInv-2 (loop j) (loop k) i = rotInv-aux-1 j (~ k) i i1

rotInv-3 : (a b : S¹) → b * (inv (inv a * b)) ≡ a
rotInv-3 base base i = base
rotInv-3 base (loop k) i = rotInv-aux-3 i0 k (~ i) i1
rotInv-3 (loop j) base i = loop j
rotInv-3 (loop j) (loop k) i = rotInv-aux-3 j k (~ i) i1

rotInv-4 : (a b : S¹) → inv (b * inv a) * b ≡ a
rotInv-4 base base i = base
rotInv-4 base (loop k) i = rotInv-aux-4 i0 k (~ i) i1
rotInv-4 (loop j) base i = loop j
rotInv-4 (loop j) (loop k) i = rotInv-aux-4 j k (~ i) i1

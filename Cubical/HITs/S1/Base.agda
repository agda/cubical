{-

Definition of the circle as a HIT with a proof that Ω(S¹) ≡ ℤ

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S1.Base where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Groupoid
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
  hiding (_+_ ; +-assoc)
open import Cubical.Data.Int

data S¹ : Set where
  base : S¹
  loop : base ≡ base

-- Check that transp is the identity function for S¹
module _ where
  transpS¹ : ∀ (φ : I) (u0 : S¹) → transp (λ _ → S¹) φ u0 ≡ u0
  transpS¹ φ u0 = refl

  compS1 : ∀ (φ : I) (u : ∀ i → Partial φ S¹) (u0 : S¹ [ φ ↦ u i0 ]) →
    comp (λ _ → S¹) u u0 ≡ hcomp u (ouc u0)
  compS1 φ u u0 = refl

helix : S¹ → Set
helix base     = Int
helix (loop i) = sucPathInt i

ΩS¹ : Set
ΩS¹ = base ≡ base

encode : ∀ x → base ≡ x → helix x
encode x p = subst helix p (pos zero)

winding : ΩS¹ → Int
winding = encode base

intLoop : Int → ΩS¹
intLoop (pos zero)       = refl
intLoop (pos (suc n))    = compPath (intLoop (pos n)) loop
intLoop (negsuc zero)    = sym loop
intLoop (negsuc (suc n)) = compPath (intLoop (negsuc n)) (sym loop)

decodeSquare : (n : Int) → PathP (λ i → base ≡ loop i) (intLoop (predInt n)) (intLoop n)
decodeSquare (pos zero) i j    = loop (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → base
                                                ; (j = i1) → loop k } )
                                       (inc (intLoop (pos n) j)) i
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

intLoop-sucInt : (z : Int) → intLoop (sucInt z) ≡ (intLoop z) ⋆ loop
intLoop-sucInt (pos n)          = refl
intLoop-sucInt (negsuc zero)    = sym (compPath-inv-l loop)
intLoop-sucInt (negsuc (suc n)) =
  (sym (compPath-refl-r (intLoop (negsuc n))))
  ⋆ (λ i → intLoop (negsuc n) ⋆ (compPath-inv-l loop (~ i)))
  ⋆ (sym (compPath-assoc (intLoop (negsuc n)) (sym loop) loop))

intLoop-predInt : (z : Int) → intLoop (predInt z) ≡ (intLoop z) ⋆ (sym loop)
intLoop-predInt (pos zero)    = sym (compPath-refl-l (sym loop))
intLoop-predInt (pos (suc n)) =
  (sym (compPath-refl-r (intLoop (pos n))))
  ⋆ (λ i → intLoop (pos n) ⋆ (compPath-inv-r loop (~ i)))
  ⋆ (sym (compPath-assoc (intLoop (pos n)) loop (sym loop)))
intLoop-predInt (negsuc n)    = refl

intLoop-hom : (a : Int) → (b : Int) → (intLoop a) ⋆ (intLoop b) ≡ intLoop (a + b)
intLoop-hom a (pos zero)       = compPath-refl-r (intLoop a)
intLoop-hom a (pos (suc n))    =
  (sym (compPath-assoc (intLoop a) (intLoop (pos n)) loop))
  ⋆ (λ i → (intLoop-hom a (pos n) i) ⋆ loop)
  ⋆ (sym (intLoop-sucInt (a + pos n)))
intLoop-hom a (negsuc zero)    = sym (intLoop-predInt a)
intLoop-hom a (negsuc (suc n)) =
  (sym (compPath-assoc (intLoop a) (intLoop (negsuc n)) (sym loop)))
  ⋆ (λ i → (intLoop-hom a (negsuc n) i) ⋆ (sym loop))
  ⋆ (sym (intLoop-predInt (a + negsuc n)))

winding-hom : (a : ΩS¹) → (b : ΩS¹) → winding (a ⋆ b) ≡ (winding a) + (winding b)
winding-hom a b i =
  hcomp (λ t → λ { (i = i0) → winding ((decodeEncode base a t) ⋆ (decodeEncode base b t))
                 ; (i = i1) → windingIntLoop ((winding a) + (winding b)) t })
        (winding (intLoop-hom (winding a) (winding b) i))

-- Based homotopy group

basedΩS¹ : (x : S¹) → Set
basedΩS¹ x = x ≡ x

-- Proof that the homotopy group is actually independent on the basepoint
-- first, give a quasi-inverse to the basechange basedΩS¹→ΩS¹ for any loop i
-- (which does *not* match at endpoints)

ΩS¹→basedΩS¹-filler : I → (i : I) → ΩS¹ → I → S¹
ΩS¹→basedΩS¹-filler l i x j =
  hfill (λ t → λ { (j = i0) → loop (i ∧ t)
                 ; (j = i1) → loop (i ∧ t) })
        (inc (x j)) l

ΩS¹→basedΩS¹ : (i : I) → ΩS¹ → basedΩS¹ (loop i)
ΩS¹→basedΩS¹ i x j = ΩS¹→basedΩS¹-filler i1 i x j

basedΩS¹→ΩS¹-filler : I → (i : I) → basedΩS¹ (loop i) → I → S¹
basedΩS¹→ΩS¹-filler l i x j =
  hfill (λ t → λ { (j = i0) → loop (i ∧ (~ t))
                 ; (j = i1) → loop (i ∧ (~ t)) })
        (inc (x j)) l

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

unfold : (x : ΩS¹) → basedΩS¹→ΩS¹ i1 x ≡ ((intLoop (pos (suc zero))) ⋆ x) ⋆ (intLoop (negsuc zero))
unfold x = compPath (doubleCompPath-elim loop x (sym loop))
                    (λ i → compPath (compPath (compPath-refl-l loop (~ i)) x) (sym loop))

loop-conjugation : basedΩS¹→ΩS¹ i1 ≡ λ x → x
loop-conjugation i x =
    ((sym (decodeEncode base (basedΩS¹→ΩS¹ i1 x)))
     ⋆ (λ t → intLoop (winding (unfold x t)))
     ⋆ (λ t → intLoop (winding-hom (compPath (intLoop (pos (suc zero))) x)
                                   (intLoop (negsuc zero)) t))
     ⋆ (λ t → intLoop ((winding-hom (intLoop (pos (suc zero))) x t)
                       + (windingIntLoop (negsuc zero) t)))
     ⋆ (λ t → intLoop (((windingIntLoop (pos (suc zero)) t) + (winding x)) + (negsuc zero)))
     ⋆ (λ t → intLoop ((+-comm (pos (suc zero)) (winding x) t) + (negsuc zero)))
     ⋆ (λ t → intLoop (+-assoc (winding x) (pos (suc zero)) (negsuc zero) (~ t)))
     ⋆ (decodeEncode base x)) i

refl-conjugation : basedΩS¹→ΩS¹ i0 ≡ λ x → x
refl-conjugation i x j =
  hfill (λ t → λ { (j = i0) → base
                 ; (j = i1) → base })
        (inc (x j)) (~ i)

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
        (inc (basedΩS¹→ΩS¹ i y)) j

-- so for any loop i, the extended basechange is an equivalence

basechange-isequiv-aux : (i : I) → isEquiv (basechange (loop i))
basechange-isequiv-aux i =
  transp (λ j → isEquiv (basedΩS¹→ΩS¹≡basechange i j)) i0 (basedΩS¹→ΩS¹-isequiv i)


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
basedΩS¹≡Int x = compPath (basedΩS¹≡ΩS¹ x) ΩS¹≡Int


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

flip : S¹ → S¹
flip base = base
flip (loop i) = loop (~ i)

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

-- rot i j = filler-rot i j i1
filler-rot : I → I → I → S¹
filler-rot i j = hfill (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                   ; (i = i1) → loop (j ∧ k)
                   ; (j = i0) → loop (i ∨ ~ k)
                   ; (j = i1) → loop (i ∧ k) }) (inc base)

isPropFamS¹ : ∀ {ℓ} (P : S¹ → Set ℓ) (pP : (x : S¹) → isProp (P x)) (b0 : P base) →
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

rotInv : I → I → I → I → S¹
rotInv j k i =
  hfill (λ l → λ {
      (k = i0) → rot (loop (i ∧ ~ l)) (loop j) ;
      (k = i1) → loop j ;
      (i = i0) → rot (rot (loop k) (loop j)) (loop (~ k)) ;
      (i = i1) → rot (loop (~ k ∧ ~ l)) (loop j) })
    (inc (rot (rot (loop (k ∨ i)) (loop j)) (loop (~ k))))

rotFlip : I → I → I → S¹
rotFlip i j k =
   hcomp (λ l → λ { (k = i0) → flip (filler-rot (~ i) (~ j) l)
                  ; (k = i1) → loop (j ∧ l)
                  ; (i = i0) → filler-rot k j l
                  ; (i = i1) → loop (j ∧ l)
                  ; (j = i0) → loop (i ∨ k ∨ (~ l))
                  ; (j = i1) → loop ((i ∨ k) ∧ l) })
          (base)

rotInvFlip : I → I → I → I → S¹
rotInvFlip j k i =
  hfill (λ l → λ {
      (k = i0) → rotFlip i j l ;
      (k = i1) → loop j ;
      (i = i0) → rot (loop j) (loop (k ∨ l)) ;
      (i = i1) → rot (flip (rot (loop (~ j)) (loop k))) (loop k) })
    (inc (rot (flip (rot (loop (~ j)) (loop (k ∨ (~ i))))) (loop k)))

rotInvFlip' : I → I → I → I → S¹
rotInvFlip' j k i =
  hfill (λ l → λ {
      (k = i0) → rotFlip i j l ;
      (k = i1) → loop j ;
      (i = i0) → rot (loop (k ∨ l)) (loop j) ;
      (i = i1) → rot (loop k) (flip (rot (loop (~ j)) (loop k))) })
    (inc (rot (loop k) (flip (rot (loop (~ j)) (loop (k ∨ (~ i)))))))

rotInv-1 : (a : S¹) → (b : S¹) → rot (rot b a) (flip b) ≡ a
rotInv-1 base base i = base
rotInv-1 base (loop k) i = rotInv i0 k i i1
rotInv-1 (loop j) base i = loop j
rotInv-1 (loop j) (loop k) i = rotInv j k i i1

rotInv-2 : (a : S¹) → (b : S¹) → rot (rot (flip b) a) b ≡ a
rotInv-2 base base i = base
rotInv-2 base (loop k) i = rotInv i0 (~ k) i i1
rotInv-2 (loop j) base i = loop j
rotInv-2 (loop j) (loop k) i = rotInv j (~ k) i i1

rotInv-3 : (a : S¹) → (b : S¹) → rot b (flip (rot (flip a) b)) ≡ a
rotInv-3 base base i = base
rotInv-3 base (loop k) i = rotInvFlip' i0 k (~ i) i1
rotInv-3 (loop j) base i = loop j
rotInv-3 (loop j) (loop k) i = rotInvFlip' j k (~ i) i1

rotInv-4 : (a : S¹) → (b : S¹) → rot (flip (rot b (flip a))) b ≡ a
rotInv-4 base base i = base
rotInv-4 base (loop k) i = rotInvFlip i0 k (~ i) i1
rotInv-4 (loop j) base i = loop j
rotInv-4 (loop j) (loop k) i = rotInvFlip j k (~ i) i1

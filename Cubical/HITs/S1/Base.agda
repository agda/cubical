{-

Definition of the circle as a HIT with a proof that Ω(S¹) ≡ ℤ

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S1.Base where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

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

-- some groupoid lemma : p ⋆ q ⋆ r = id ⋆ (id ⋆ p ⋆ q) ⋆ r

_⋆_ : {ℓ : Level} → {A : Set ℓ} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
x≡y ⋆ y≡z = compPath x≡y y≡z

infixl 30 _⋆_

doubleCompPath-filler : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z →
                        I → I → A
doubleCompPath-filler p q r i =
  hfill (λ t → λ { (i = i0) → p (~ t)
                 ; (i = i1) → r t })
        (inc (q i))

doubleCompPath : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
doubleCompPath p q r i = doubleCompPath-filler p q r i i1

_⋆⋆_⋆⋆_ : {ℓ : Level} {A : Set ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
p ⋆⋆ q ⋆⋆ r = doubleCompPath p q r

rhombus-filler : {ℓ : Level} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → A
rhombus-filler p q i j =
  hcomp (λ t → λ { (i = i0) → p (~ t ∨ j)
                 ; (i = i1) → q (t ∧ j)
                 ; (j = i0) → p (~ t ∨ i)
                 ; (j = i1) → q (t ∧ i) })
        (p i1)

leftright : {ℓ : Level} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
            (refl ⋆⋆ p ⋆⋆ q) ≡ (p ⋆⋆ q ⋆⋆ refl)
leftright p q i j =
  hcomp (λ t → λ { (j = i0) → p (i ∧ (~ t))
                 ; (j = i1) → q (t ∨ i) })
        (rhombus-filler p q i j)

split-leftright : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ⋆⋆ q ⋆⋆ r) ≡ (refl ⋆⋆ (p ⋆⋆ q ⋆⋆ refl) ⋆⋆ r)
split-leftright p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ i ∧ ~ t)
                 ; (j = i1) → r t })
        (doubleCompPath-filler p q refl j i)

split-leftright' : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ⋆⋆ q ⋆⋆ r) ≡ (p ⋆⋆ (refl ⋆⋆ q ⋆⋆ r) ⋆⋆ refl)
split-leftright' p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ t)
                 ; (j = i1) → r (i ∨ t) })
        (doubleCompPath-filler refl q r j i)

doubleCompPath-elim : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                      (r : y ≡ z) → (p ⋆⋆ q ⋆⋆ r) ≡ (p ⋆ q) ⋆ r
doubleCompPath-elim p q r = (split-leftright p q r) ⋆ (λ i → (leftright p q (~ i)) ⋆ r)

doubleCompPath-elim' : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                       (r : y ≡ z) → (p ⋆⋆ q ⋆⋆ r) ≡ p ⋆ (q ⋆ r)
doubleCompPath-elim' p q r = (split-leftright' p q r) ⋆ (sym (leftright p (q ⋆ r)))

compPath-assoc : {ℓ : Level} {A : Set ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                 (p ⋆ q) ⋆ r ≡ p ⋆ (q ⋆ r)
compPath-assoc p q r = (sym (doubleCompPath-elim p q r)) ⋆ (doubleCompPath-elim' p q r)

-- another groupoid lemma : id ⋆ p ⋆ id = p

compPath-refl-r : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⋆ refl ≡ p
compPath-refl-r p i j =
  hfill (λ t → λ { (j = i0) → p i0 ; (j = i1) → p i1 }) (inc (p j)) (~ i)

compPath-refl-l : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → refl ⋆ p ≡ p
compPath-refl-l p = (leftright refl p) ⋆ (compPath-refl-r p)

compPath-inv-r : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⋆ (sym p) ≡ refl
compPath-inv-r p i j =
  hcomp (λ t → λ { (i = i1) → p i0
                 ; (j = i0) → p i0
                 ; (j = i1) → p (~ i ∧ ~ t) })
        (p (~ i ∧ j))

compPath-inv-l : {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ≡ y) → (sym p) ⋆ p ≡ refl
compPath-inv-l p = compPath-inv-r (sym p)

-- Group homomorphism

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
  hcomp (λ t → λ { (i = i0) → winding (compPath (decodeEncode base a t)
                                                (decodeEncode base b t))
                 ; (i = i1) → windingIntLoop ((winding a) + (winding b)) t })
        (winding (intLoop-hom (winding a) (winding b) i))

-- Based homotopy group

basedΩS¹ : (x : S¹) → Set
basedΩS¹ x = x ≡ x

-- Proof that the homotopy group is actually independent on the basepoint

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

basedΩS¹→ΩS¹-isequiv : (i : I) → isEquiv (basedΩS¹→ΩS¹ i)
basedΩS¹→ΩS¹-isequiv i = isoToIsEquiv (iso (basedΩS¹→ΩS¹ i) (ΩS¹→basedΩS¹ i)
                 (ΩS¹→basedΩS¹→ΩS¹ i) (basedΩS¹→ΩS¹→basedΩS¹ i))


-- now

unfold : (x : ΩS¹) → basedΩS¹→ΩS¹ i1 x ≡ compPath (compPath (intLoop (pos (suc zero))) x) (intLoop (negsuc zero))
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

basedΩS¹→ΩS¹≡basechange : (i : I) → basedΩS¹→ΩS¹ i ≡ basechange (loop i)
basedΩS¹→ΩS¹≡basechange i j y =
  hfill (λ t → λ { (i = i0) → refl-conjugation t y
                 ; (i = i1) → loop-conjugation t y })
        (inc (basedΩS¹→ΩS¹ i y)) j

basechange-isequiv-aux : (i : I) → isEquiv (basechange (loop i))
basechange-isequiv-aux i =
  transp (λ j → isEquiv (basedΩS¹→ΩS¹≡basechange i j)) i0 (basedΩS¹→ΩS¹-isequiv i)

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

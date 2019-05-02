{-

This file proves the higher groupoid structure of types
for homogeneous and heterogeneous paths

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.GroupoidLaws where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w : A

_⁻¹ : (x ≡ y) → (y ≡ x)
x≡y ⁻¹ = sym x≡y

infix 40 _⁻¹

-- homogeneous groupoid laws

symInvo : (p : x ≡ y) → p ≡ p ⁻¹ ⁻¹
symInvo p = refl

rUnit : (p : x ≡ y) → p ≡ p ∙ refl
rUnit p j i = compPath-filler p refl j i

-- The filler of left unit: lUnit-filler p =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) x (p (~ j ∨ i)))
-- (refl i) (λ j → compPath-filler refl p i j)) (λ k i → (p (~ k ∧ i ))) (lUnit p)

lUnit-filler : {x y : A} (p : x ≡ y) → I → I → I → A
lUnit-filler {x = x} p j k i =
  hfill (λ j → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∨ j )
                  ; (k = i0) → p i
               -- ; (k = i1) → compPath-filler refl p j i
                  }) (inS (p (~ k ∧ i ))) j

lUnit : (p : x ≡ y) → p ≡ refl ∙ p
lUnit p j i = lUnit-filler p i1 j i

symRefl : refl {x = x} ≡ refl ⁻¹
symRefl i = refl

compPathRefl : refl {x = x} ≡ refl ∙ refl
compPathRefl = rUnit refl

-- The filler of right cancellation: rCancel-filler p =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) x (p (~ j ∧ ~ i)))
-- (λ j → compPath-filler p (p ⁻¹) i j) (refl i)) (λ j i → (p (i ∧ ~ j))) (rCancel p)

rCancel-filler : ∀ {x y : A} (p : x ≡ y) → (k j i : I) → A
rCancel-filler {x = x} p k j i =
  hfill (λ k → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∧ ~ j)
               -- ; (j = i0) → compPath-filler p (p ⁻¹) k i
                  ; (j = i1) → x
                  }) (inS (p (i ∧ ~ j))) k

rCancel : (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
rCancel {x = x} p j i = rCancel-filler p i1 j i

lCancel : (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
lCancel p = rCancel (p ⁻¹)

-- The filler of the three-out-of-four identification: 3outof4-filler α p β =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) (α i i0) (α i i1))
-- (λ j → α i j) (λ j → β i j)) (λ j i → α i0 i) (3outof4 α p β)

3outof4-filler : (α : I → I → A) → (p : α i1 i0 ≡ α i1 i1) →
  (β : PathP (λ j → Path A (α j i0) (α j i1)) (λ i → α i0 i) p) → I → I → I → A
3outof4-filler α p β k j i =
  hfill (λ k → λ { (i = i0) → α k i0
                  ; (i = i1) → α k i1
                  ; (j = i0) → α k i
                  ; (j = i1) → β k i
                  }) (inS (α i0 i)) k

3outof4 : (α : I → I → A) → (p : α i1 i0 ≡ α i1 i1) →
  (β : PathP (λ j → Path A (α j i0) (α j i1)) (λ i → α i0 i) p) → (λ i → α i1 i) ≡ p
3outof4 α p β j i = 3outof4-filler α p β i1 j i

-- The filler of the pre-associative square: preassoc p q r =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) x (compPath-filler q r i j))
-- (refl i) (λ j → compPath-filler (p ∙ q) r i j)) (λ j i → compPath-filler p q j i) (preassoc p q r)

preassoc-filler : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → I → I → I → A
preassoc-filler {x = x} p q r k j i =
  hfill (λ k → λ { (i = i0) → x
                  ; (i = i1) → compPath-filler q r k j
                  ; (j = i0) → p i
               -- ; (j = i1) → compPath-filler (p ∙ q) r k i
                  }) (inS (compPath-filler p q j i)) k

preassoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  PathP (λ j → Path A x ((q ∙ r) j)) p ((p ∙ q) ∙ r)
preassoc {x = x} p q r j i = preassoc-filler p q r i1 j i

assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  p ∙ q ∙ r ≡ (p ∙ q) ∙ r
assoc p q r = 3outof4 (compPath-filler p (q ∙ r)) ((p ∙ q) ∙ r) (preassoc p q r)

-- heterogeneous groupoid laws

symInvoP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
     PathP (λ j → PathP (λ i → symInvo (λ i → A i) j i) x y) p (symP (symP p))
symInvoP p = refl

rUnitP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
  PathP (λ j → PathP (λ i → rUnit (λ i → A i) j i) x y) p (compPathP p refl)
rUnitP p j i = compPathP-filler p refl i j

lUnitP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
  PathP (λ j → PathP (λ i → lUnit (λ i → A i) j i) x y) p (compPathP refl p)
lUnitP {A = A} {x = x} p k i =
  comp (λ j → lUnit-filler (λ i → A i) j k i)
       _
       (λ j → λ { (i = i0) → x
                 ; (i = i1) → p (~ k ∨ j )
                 ; (k = i0) → p i
                 }) (p (~ k ∧ i ))


rCancelP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
   PathP (λ j → PathP (λ i → rCancel (λ i → A i) j i) x x) (compPathP p (symP p)) refl
rCancelP {A = A} {x = x} p j i =
  comp (λ k → rCancel-filler (λ i → A i) k j i)
       _
       (λ k → λ { (i = i0) → x
                 ; (i = i1) → p (~ k ∧ ~ j)
                 ; (j = i1) → x
                 }) (p (i ∧ ~ j))

lCancelP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
   PathP (λ j → PathP (λ i → lCancel (λ i → A i) j i) y y) (compPathP (symP p) p) refl
lCancelP p = rCancelP (symP p)

3outof4P : {A : I → I → Type ℓ} {P : (A i0 i1) ≡ (A i1 i1)}
  {B : PathP (λ j → Path (Type ℓ) (A i0 j) (A i1 j)) (λ i → A i i0) P}
  (α : ∀ (i j : I) → A j i)
  (p : PathP (λ i → P i) (α i1 i0) (α i1 i1)) →
  (β : PathP (λ j → PathP (λ i → B j i) (α j i0) (α j i1)) (λ i → α i0 i) p) →
  PathP (λ j → PathP (λ i → 3outof4 (λ j i → A i j) P B j i) (α i1 i0) (α i1 i1)) (λ i → α i1 i) p
3outof4P {A = A} {P} {B} α p β j i =
  comp (λ k → 3outof4-filler (λ j i → A i j) P B k j i)
       _
       (λ k → λ { (i = i0) → α k i0
                 ; (i = i1) → α k i1
                 ; (j = i0) → α k i
                 ; (j = i1) → β k i
                 }) (α i0 i)

preassocP : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
  {C_i1 : Type ℓ} {C : (B i1) ≡ C_i1} {w : C i1} (p : PathP A x y) (q : PathP (λ i → B i) y z) (r : PathP (λ i → C i) z w) →
  PathP (λ j → PathP (λ i → preassoc (λ i → A i) B C j i) x ((compPathP q r) j)) p (compPathP (compPathP p q) r)
preassocP {A = A} {x = x} {B = B} {C = C} p q r j i =
  comp (λ k → preassoc-filler (λ i → A i) B C k j i) _
       (λ k → λ { (i = i0) → x
                 ; (i = i1) → compPathP-filler q r j k
                 ; (j = i0) → p i
              -- ; (j = i1) → compPathP-filler (compPathP p q) r i k
                 }) (compPathP-filler p q i j)

assocP : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
  {C_i1 : Type ℓ} {C : (B i1) ≡ C_i1} {w : C i1} (p : PathP A x y) (q : PathP (λ i → B i) y z) (r : PathP (λ i → C i) z w) →
  PathP (λ j → PathP (λ i → assoc (λ i → A i) B C j i) x w) (compPathP p (compPathP q r)) (compPathP (compPathP p q) r)
assocP p q r =
  3outof4P (λ i j → compPathP-filler p (compPathP q r) j i) (compPathP (compPathP p q) r) (preassocP p q r)



-- Loic's code below


-- simultaneaous composition on both sides of a path

doubleCompPath-filler : {ℓ : Level} {A : Type ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z →
                        I → I → A
doubleCompPath-filler p q r i =
  hfill (λ t → λ { (i = i0) → p (~ t)
                 ; (i = i1) → r t })
        (inS (q i))

doubleCompPath : {ℓ : Level} {A : Type ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
doubleCompPath p q r i = doubleCompPath-filler p q r i i1

_∙∙_∙∙_ : {ℓ : Level} {A : Type ℓ} {w x y z : A} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
p ∙∙ q ∙∙ r = doubleCompPath p q r

-- some exchange law for doubleCompPath and refl

rhombus-filler : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → A
rhombus-filler p q i j =
  hcomp (λ t → λ { (i = i0) → p (~ t ∨ j)
                 ; (i = i1) → q (t ∧ j)
                 ; (j = i0) → p (~ t ∨ i)
                 ; (j = i1) → q (t ∧ i) })
        (p i1)

leftright : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
            (refl ∙∙ p ∙∙ q) ≡ (p ∙∙ q ∙∙ refl)
leftright p q i j =
  hcomp (λ t → λ { (j = i0) → p (i ∧ (~ t))
                 ; (j = i1) → q (t ∨ i) })
        (rhombus-filler p q i j)

-- equating doubleCompPath and a succession of two compPath

split-leftright : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ∙∙ q ∙∙ r) ≡ (refl ∙∙ (p ∙∙ q ∙∙ refl) ∙∙ r)
split-leftright p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ i ∧ ~ t)
                 ; (j = i1) → r t })
        (doubleCompPath-filler p q refl j i)

split-leftright' : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ∙∙ q ∙∙ r) ≡ (p ∙∙ (refl ∙∙ q ∙∙ r) ∙∙ refl)
split-leftright' p q r i j =
  hcomp (λ t → λ { (j = i0) → p (~ t)
                 ; (j = i1) → r (i ∨ t) })
        (doubleCompPath-filler refl q r j i)

doubleCompPath-elim : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                      (r : y ≡ z) → (p ∙∙ q ∙∙ r) ≡ (p ∙ q) ∙ r
doubleCompPath-elim p q r = (split-leftright p q r) ∙ (λ i → (leftright p q (~ i)) ∙ r)

doubleCompPath-elim' : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                       (r : y ≡ z) → (p ∙∙ q ∙∙ r) ≡ p ∙ (q ∙ r)
doubleCompPath-elim' p q r = (split-leftright' p q r) ∙ (sym (leftright p (q ∙ r)))

-- deducing associativity for compPath

-- assoc : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
--                 (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
-- assoc p q r = (sym (doubleCompPath-elim p q r)) ∙ (doubleCompPath-elim' p q r)

hcomp-unique : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
               (h2 : ∀ i → A [ (φ ∨ ~ i) ↦ (\ { (φ = i1) → u i 1=1; (i = i0) → outS u0}) ])
               → (hcomp u (outS u0) ≡ outS (h2 i1)) [ φ ↦ (\ { (φ = i1) → (\ i → u i1 1=1)}) ]
hcomp-unique {φ = φ} u u0 h2 = inS (\ i → hcomp (\ k → \ { (φ = i1) → u k 1=1
                                                            ; (i = i1) → outS (h2 k) })
                                                   (outS u0))


lid-unique : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
               (h1 h2 : ∀ i → A [ (φ ∨ ~ i) ↦ (\ { (φ = i1) → u i 1=1; (i = i0) → outS u0}) ])
               → (outS (h1 i1) ≡ outS (h2 i1)) [ φ ↦ (\ { (φ = i1) → (\ i → u i1 1=1)}) ]
lid-unique {φ = φ} u u0 h1 h2 = inS (\ i → hcomp (\ k → \ { (φ = i1) → u k 1=1
                                                            ; (i = i0) → outS (h1 k)
                                                            ; (i = i1) → outS (h2 k) })
                                                   (outS u0))


transp-hcomp : ∀ {ℓ} (φ : I) {A' : Set ℓ}
                     (A : (i : I) → Set ℓ [ φ ↦ (λ _ → A') ]) (let B = \ (i : I) → outS (A i))
                 → ∀ {ψ} (u : I → Partial ψ (B i0)) → (u0 : B i0 [ ψ ↦ u i0 ]) →
                 (transp B φ (hcomp u (outS u0)) ≡ hcomp (\ i o → transp B φ (u i o)) (transp B φ (outS u0)))
                   [ ψ ↦ (\ { (ψ = i1) → (\ i → transp B φ (u i1 1=1))}) ]
transp-hcomp φ A u u0 = inS (sym (outS (hcomp-unique
               ((\ i o → transp B φ (u i o))) (inS (transp B φ (outS u0)))
                 \ i → inS (transp B φ (hfill u u0 i)))))
  where
    B = \ (i : I) → outS (A i)


hcomp-cong : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
                                    (u' : I → Partial φ A) → (u0' : A [ φ ↦ u' i0 ]) →

             (ueq : ∀ i → PartialP φ (\ o → u i o ≡ u' i o)) → (outS u0 ≡ outS u0') [ φ ↦ (\ { (φ = i1) → ueq i0 1=1}) ]
             → (hcomp u (outS u0) ≡ hcomp u' (outS u0')) [ φ ↦ (\ { (φ = i1) → ueq i1 1=1 }) ]
hcomp-cong u u0 u' u0' ueq 0eq = inS (\ j → hcomp (\ i o → ueq i o j) (outS 0eq j))

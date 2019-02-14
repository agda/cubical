{-# OPTIONS --cubical #-}
module Cubical.HITs.Hopf where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Equiv

open import Cubical.Data.Int
open import Cubical.Data.Prod

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Susp
open import Cubical.HITs.Join

data Interval : Set where
  I0 : Interval
  I1 : Interval
  seg : I0 ≡ I1

PseudoHopf : Set
PseudoHopf = (S¹ × Interval) × S¹

PseudoHopf-π1 : PseudoHopf → S¹
PseudoHopf-π1 ((y , _) , _) = y

PseudoHopf-π2 : PseudoHopf → S¹
PseudoHopf-π2 (_ , x) = x

Border : (x : S¹) → (j : I) → Partial (j ∨ (~ j)) (Σ Set (λ T → T ≃ S¹))
Border x j (j = i0) = S¹ , rot x , rotIsEquiv x
Border x j (j = i1) = S¹ , idEquiv S¹

Border1 : (x : S¹) → (j : I) → Partial (j ∨ (~ j)) Set
Border1 x j y = Border x j y .fst

Border2 : (x : S¹) → (j : I) → PartialP (j ∨ (~ j)) (λ y → Border1 x j y ≃ S¹)
Border2 x j y = Border x j y .snd

HopfSuspS¹ : SuspS¹ → Set
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x j) = Glue S¹ (Border x j)

-- Total space of the fibration
TotalSpace : Set
TotalSpace = Σ SuspS¹ HopfSuspS¹

unglueb : (x : S¹) → (j : I) → Glue S¹ (Border x j) → S¹
unglueb x j y = unglue {_} _ {Border1 x j} {Border2 x j} y

-- rot i j = filler-rot i j i1
filler-rot : I → I → I → S¹
filler-rot i j = hfill (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                   ; (i = i1) → loop (j ∧ k)
                   ; (j = i0) → loop (i ∨ ~ k)
                   ; (j = i1) → loop (i ∧ k) }) (inc base)

flip : S¹ → S¹
flip base = base
flip (loop i) = loop (~ i)

rotInv : I → I → I → I → S¹
rotInv j k i =
  hfill (λ l → λ {
      (k = i0) → rot (loop (i ∧ ~ l)) (loop j) ;
      (k = i1) → loop j ;
      (i = i0) → rot (rot (loop k) (loop j)) (loop (~ k)) ;
      (i = i1) → rot (loop (~ k ∧ ~ l)) (loop j) })
    (inc (rot (rot (loop (k ∨ i)) (loop j)) (loop (~ k))))

-- flip (rot (flip a) (flip b)) ≡ rot a b, but in a diagonal way to fit in rotInv3-aux
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

rotInv-3 : (a : S¹) → (b : S¹) → rot (flip (rot b (flip a))) b ≡ a
rotInv-3 base base i = base
rotInv-3 base (loop k) i = rotInvFlip i0 k (~ i) i1
rotInv-3 (loop j) base i = loop j
rotInv-3 (loop j) (loop k) i = rotInvFlip j k (~ i) i1

rotInv-4 : (a : S¹) → (b : S¹) → rot b (flip (rot (flip a) b)) ≡ a
rotInv-4 base base i = base
rotInv-4 base (loop k) i = rotInvFlip' i0 k (~ i) i1
rotInv-4 (loop j) base i = loop j
rotInv-4 (loop j) (loop k) i = rotInvFlip' j k (~ i) i1

-- independence of ΩS¹ on the basepoint
-- should be an instance of the relation between base change and conjugation, plus
-- ΩS¹ being abelian

basedΩS¹ : (x : S¹) → Set
basedΩS¹ x = x ≡ x

ΩS¹→basedΩS¹ : (i : I) → basedΩS¹ base → basedΩS¹ (loop i)
ΩS¹→basedΩS¹ i l j =
  hcomp (λ t → λ { (j = i0) → loop (i ∨ (~ t))
                 ; (j = i1) → loop (i ∨ (~ t)) })
        (l j)

basedΩS¹→ΩS¹ : (i : I) → basedΩS¹ (loop i) → basedΩS¹ base
basedΩS¹→ΩS¹ i l j =
  hcomp (λ t → λ { (j = i0) → loop (i ∧ (~ t))
                 ; (j = i1) → loop (i ∧ (~ t)) })
        (l j)

basedΩS¹→ΩS¹→basedΩS¹ : (i : I) → (x : basedΩS¹ (loop i))
                        → ΩS¹→basedΩS¹ i (basedΩS¹→ΩS¹ i x) ≡ x
basedΩS¹→ΩS¹→basedΩS¹ i x = {!!}

ΩS¹≡basedΩS¹ : (x : S¹) → basedΩS¹ base ≡ basedΩS¹ x
ΩS¹≡basedΩS¹ base = refl
ΩS¹≡basedΩS¹ (loop i) j = {!!}

Int≡basedΩS¹ : (x : S¹) → Int ≡ basedΩS¹ x
Int≡basedΩS¹ x = compPath (sym ΩS¹≡Int) (ΩS¹≡basedΩS¹ x)

-- the sections of the trivial fibration λ (_ : S¹) (_ : S¹) → Int are constant
-- this should be an instance of S¹ × S¹ being connected, which should follow
-- from S¹ being connected and product of connected spaces being connected.

fibInt : S¹ → S¹ → Set
fibInt _ _ = Int

constant-loop-0 : (F : S¹ → Int) → (j : I) → (x : I) → F base ≡ F (loop x)
constant-loop-0 F j x =
  hfill (λ t → λ { (x = i0) → λ _ → F base
                 ; (x = i1) → isSetInt (F base) (F base) (λ j → F (loop j)) refl t })
        (inc (λ i → F (loop (x ∧ i)))) j

constant-loop : (F : S¹ → S¹ → Int) → (x : S¹) → (y : S¹) → F base base ≡ F x y
constant-loop F base base = λ _ → F base base
constant-loop F (loop x) base = constant-loop-0 (λ x → F x base) i1 x
constant-loop F base (loop y) = constant-loop-0 (F base) i1 y
constant-loop F (loop x) (loop y) =
  hcomp (λ t → λ { (x = i0) → constant-loop-0 (F base) t y
                 ; (x = i1) → isSetInt (F base base) (F base (loop y))
                                       (λ j → F (loop j) (loop (y ∧ j)))
                                       (constant-loop-0 (F base) i1 y) t
                 ; (y = i0) → constant-loop-0 (λ x → F x base) t x
                 ; (y = i1) → isSetInt (F base base) (F (loop x) base)
                                       (λ j → F (loop (x ∧ j)) (loop j))
                                       (constant-loop-0 (λ x → F x base) i1 x) t })
        (λ i → F (loop (x ∧ i)) (loop (y ∧ i)))

discretefib : (F : S¹ → S¹ → Set) → Set
discretefib F = (a : (x : S¹) → (y : S¹) → F x y) →
        (b : (x : S¹) → (y : S¹) → F x y) →
        (a base base ≡ b base base) →
        (x : S¹) → (y : S¹) → a x y ≡ b x y

discretefib-fibInt : discretefib fibInt
discretefib-fibInt a b h x y i =
  hcomp (λ t → λ { (i = i0) → constant-loop a x y t
                 ; (i = i1) → constant-loop b x y t })
        (h i)

-- use the two previous results to build filler of squares dependent on S¹ × S¹ when
-- the square above (base , base) has a filler

assocFiller-1 : I → I → S¹ → S¹ → S¹
assocFiller-1 i j x y =
  hfill (λ t → λ { (i = i0) → rot (rot (flip (rot (rot y x) (flip y))) (rot y x))
                                  (rotInv-1 x y t)
                 ; (i = i1) → rot (rotInv-3 y (rot y x) (~ t)) x })
        (inc (rotInv-2 (rot y x) (rot (rot y x) (flip y)) i)) j

assoc-1 : (x : S¹) → (y : S¹) → basedΩS¹ (rot (rot (flip (rot (rot y x) (flip y))) (rot y x)) x)
assoc-1 x y i = assocFiller-1 i i1 x y

-- this one is not a problem, see assocConst-2
assocConst-1 : (x : S¹) → (y : S¹) → assoc-1 x y ≡ refl
assocConst-1 x y = {!!}

assocSquare-1 : I → I → S¹ → S¹ → S¹
assocSquare-1 i j x y = hcomp (λ t → λ { (i = i0) → assocFiller-1 i0 j x y
                                     ; (i = i1) → assocFiller-1 i1 j x y
                                     ; (j = i0) → assocFiller-1 i i0 x y
                                     ; (j = i1) → assocConst-1 x y t i })
                            (assocFiller-1 i j x y)

-- that one used to be very clean :

-- assocFiller-2 : I → I → S¹ → S¹ → S¹
-- assocFiller-2 i j x y =
--   hfill (λ t → λ { (i = i0) → rotInv-1 y (rot (flip y) x) t
--                  ; (i = i1) → rotInv-4 y x t })
--         (inc (rot (rotInv-2 x y i) (flip (rot (flip y) x)))) j

-- but I need it to be definitionnally equal to base when x = y = base,
-- and not having to destruct x and y. So it became this mess :(

assocFiller-2-0 : I → I → I → S¹
assocFiller-2-0 i j x =
  hfill (λ t → λ { (i = i0) → rotInv-1 base (loop x) t
                 ; (i = i1) → rotInv-4 base (loop x) t
                 ; (x = i0) → base
                 ; (x = i1) → base })
        (inc (rot (loop x) (flip (loop x)))) j

assocFiller-2-1 : I → I → I → S¹
assocFiller-2-1 i j y =
  hfill (λ t → λ { (i = i0) → rotInv-1 (loop y) (loop (~ y)) t
                 ; (i = i1) → loop y
                 ; (y = i0) → base
                 ; (y = i1) → base })
        (inc (rot (rotInv-2 base (loop y) i) (loop y))) j

assocFiller-2-2 : (x : S¹) → (y : S¹) → y ≡ y
assocFiller-2-2 base base i = base
assocFiller-2-2 (loop x) base i = assocFiller-2-0 i i1 x
assocFiller-2-2 base (loop y) i = assocFiller-2-1 i i1 y
assocFiller-2-2 (loop x) (loop y) i =
  hcomp (λ t → λ { (i = i0) → rotInv-1 (loop y) (rot (loop (~ y)) (loop x)) t
                 ; (i = i1) → rotInv-4 (loop y) (loop x) t
                 ; (x = i0) → assocFiller-2-1 i t y
                 ; (x = i1) → assocFiller-2-1 i t y
                 ; (y = i0) → assocFiller-2-0 i t x
                 ; (y = i1) → assocFiller-2-0 i t x })
        (rot (rotInv-2 (loop x) (loop y) i) (flip (rot (loop (~ y)) (loop x))))

assocFiller-2 : (x : S¹) → (y : S¹) → PathP (λ j → rotInv-1 y (rot (flip y) x) j ≡ rotInv-4 y x j) (λ i → (rot (rotInv-2 x y i) (flip (rot (flip y) x)))) (assocFiller-2-2 x y)
assocFiller-2 base base j i = base
assocFiller-2 (loop x) base j i = assocFiller-2-0 i j x
assocFiller-2 base (loop y) j i = assocFiller-2-1 i j y
assocFiller-2 (loop x) (loop y) j i =
  hfill (λ t → λ { (i = i0) → rotInv-1 (loop y) (rot (loop (~ y)) (loop x)) t
                 ; (i = i1) → rotInv-4 (loop y) (loop x) t
                 ; (x = i0) → assocFiller-2-1 i t y
                 ; (x = i1) → assocFiller-2-1 i t y
                 ; (y = i0) → assocFiller-2-0 i t x
                 ; (y = i1) → assocFiller-2-0 i t x })
        (inc (rot (rotInv-2 (loop x) (loop y) i) (flip (rot (loop (~ y)) (loop x))))) j

assoc-2 : (x : S¹) → (y : S¹) → basedΩS¹ y
assoc-2 x y i = assocFiller-2 x y i1 i

fibInt≡fibAssoc-2 : Path (S¹ → S¹ → Set) fibInt (λ _ y → basedΩS¹ y)
fibInt≡fibAssoc-2 i = λ x y → Int≡basedΩS¹ y i

discretefib-fibAssoc-2 : discretefib (λ _ y → basedΩS¹ y)
discretefib-fibAssoc-2 =
  transp (λ i → discretefib (fibInt≡fibAssoc-2 i)) i0 discretefib-fibInt

assocConst-2 : (x : S¹) → (y : S¹) → assoc-2 x y ≡ refl
assocConst-2 x y = discretefib-fibAssoc-2 assoc-2 (λ _ _ → refl) refl x y

assocSquare-2 : I → I → S¹ → S¹ → S¹
assocSquare-2 i j x y = hcomp (λ t → λ { (i = i0) → assocFiller-2 x y j i0
                                       ; (i = i1) → assocFiller-2 x y j i1
                                       ; (j = i0) → assocFiller-2 x y i0 i
                                       ; (j = i1) → assocConst-2 x y t i })
                            (assocFiller-2 x y j i)

-- Forward direction

filler-1 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → join S¹ S¹
filler-1 i j y x = hfill (λ t → λ { (j = i0) → inl (rotInv-1 x y t)
                                  ; (j = i1) → inr x })
                         (inc (push (rot (unglueb y j x) (flip y)) (unglueb y j x) j)) i

Hopf→Join : TotalSpace → join S¹ S¹
Hopf→Join (north , x) = inl x
Hopf→Join (south , x) = inr x
Hopf→Join (merid y j , x) = filler-1 i1 j y x

-- Backward direction

Join→Hopf : join S¹ S¹ → TotalSpace
Join→Hopf (inl x) = (north , x)
Join→Hopf (inr x) = (south , x)
Join→Hopf (push y x j) =
  (merid (rot (flip y) x) j
  , glue {_} {_} {_} {_} {Border1 (rot (flip y) x) j} {Border2 (rot (flip y) x) j}
         (λ { (j = i0) → y ; (j = i1) → x })
         (rotInv-2 x y j))

-- First homotopy

filler-3-0 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-3-0 i j y x =
  hfill (λ t → λ { (j = i0) → ((rot (flip (rot (rot y x) (flip y))) (rot y x) , I0)
                              , rot (rot (flip (rot (rot y x) (flip y))) (rot y x))
                                    (rotInv-1 x y t))
                 ; (j = i1) → ((rot (flip (rot x (flip y))) x , I1)
                              , x) })
        (inc ((rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x) , seg j)
             , rotInv-2 (unglueb y j x) (rot (unglueb y j x) (flip y)) j)) i

filler-3-1 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-3-1 i j y x =
  hfill (λ t → λ { (j = i0) → ((rot (flip (rot (rot y x) (flip y))) (rot y x) , I0)
                              , rot (rotInv-3 y (rot y x) (~ t)) x)
                 ; (j = i1) → ((rot (flip (rot x (flip y))) x , I1) , x) })
        (inc ((rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x) , seg j)
             , unglueb y j x)) i

filler-3-2 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalSpace
filler-3-2 i j y x =
  hcomp (λ t → λ { (i = i0) → Join→Hopf (filler-1 t j y x)
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-3-0 t j y x)) j
                              , glue {_} {_} {_} {_}
                                     {Border1 (PseudoHopf-π1 (filler-3-0 t j y x)) j}
                                     {Border2 (PseudoHopf-π1 (filler-3-0 t j y x)) j}
                                     (λ { (j = i0) → rotInv-1 x y t
                                        ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-3-0 t j y x)))
                 ; (j = i0) → (north , rotInv-1 x y t)
                 ; (j = i1) → (south , x) })
        (merid (rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x)) j
        , glue {_} {_} {_} {_}
               {Border1 (rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x)) j}
               {Border2 (rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x)) j}
               (λ { (j = i0) → rot (rot y x) (flip y) ; (j = i1) → x })
               (rotInv-2 (unglueb y j x) (rot (unglueb y j x) (flip y)) j) )

filler-3-3 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-3-3 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-3-0 t j y x
                 ; (i = i1) → filler-3-1 t j y x
                 ; (j = i0) → ((rot (flip (rot (rot y x) (flip y))) (rot y x) , I0)
                              , assocSquare-1 i t x y)
                 ; (j = i1) → ((rot (flip (rot x (flip y))) x , I1) , x) })
        ((rot (flip (rot (unglueb y j x) (flip y))) (unglueb y j x) , seg j)
        , rotInv-2 (unglueb y j x) (rot (unglueb y j x) (flip y)) (i ∨ j))

filler-3-4 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-3-4 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-3-1 t j y x
                 ; (i = i1) → ((y , seg j) , unglueb y j x)
                 ; (j = i0) → ((rotInv-3 y (rot y x) i , I0)
                              , rot (rotInv-3 y (rot y x) (i ∨ ~ t)) x)
                 ; (j = i1) → ((rotInv-3 y x i , I1) , x) })
        ((rotInv-3 y (unglueb y j x) i , seg j) , unglueb y j x)

filler-3-5 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalSpace
filler-3-5 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-3-2 (~ t) j y x
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-3-4 t j y x)) j
                              , glue {_} {_} {_} {_}
                                     {Border1 (PseudoHopf-π1 (filler-3-4 t j y x)) j}
                                     {Border2 (PseudoHopf-π1 (filler-3-4 t j y x)) j}
                                     (λ { (j = i0) → x ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-3-4 t j y x)))
                 ; (j = i0) → (north , x)
                 ; (j = i1) → (south , x) })
        (merid (PseudoHopf-π1 (filler-3-3 i j y x)) j
        , glue {_} {_} {_} {_}
               {Border1 (PseudoHopf-π1 (filler-3-3 i j y x)) j}
               {Border2 (PseudoHopf-π1 (filler-3-3 i j y x)) j}
               (λ { (j = i0) → x ; (j = i1) → x })
               (PseudoHopf-π2 (filler-3-3 i j y x)))

Hopf→Join→Hopf : ∀ x → Join→Hopf (Hopf→Join x) ≡ x
Hopf→Join→Hopf (north , x) i = (north , x)
Hopf→Join→Hopf (south , x) i = (south , x)
Hopf→Join→Hopf (merid y j , x) i = filler-3-5 i j y x

-- Second homotopy

filler-4-0 : I → I → S¹ → S¹ → join S¹ S¹
filler-4-0 i j y x =
  filler-1 i j (rot (flip y) x)
           (glue {_} {_} {_} {_} {Border1 (rot (flip y) x) j} {Border2 (rot (flip y) x) j}
                 (λ { (j = i0) → y ; (j = i1) → x })
                 (rotInv-2 x y j))

filler-4-1 : I → I → S¹ → S¹ → join S¹ S¹
filler-4-1 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-4-0 t j y x
                 ; (i = i1) → push (rotInv-4 y x t) x j
                 ; (j = i0) → inl (assocSquare-2 i t x y)
                 ; (j = i1) → inr x })
        (push (rot (rotInv-2 x y (i ∨ j)) (flip (rot (flip y) x))) (rotInv-2 x y (i ∨ j)) j)

Join→Hopf→Join : ∀ x → Hopf→Join (Join→Hopf x) ≡ x
Join→Hopf→Join (inl x) i = inl x
Join→Hopf→Join (inr x) i = inr x
Join→Hopf→Join (push y x j) i = filler-4-1 i j y x

Join≡Hopf : join S¹ S¹ ≡ TotalSpace
Join≡Hopf = isoToPath (iso Join→Hopf Hopf→Join Hopf→Join→Hopf Join→Hopf→Join)

S³≡Hopf : S³ ≡ TotalSpace
S³≡Hopf = compPath S³≡joinS¹S¹ Join≡Hopf

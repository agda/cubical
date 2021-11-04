{-# OPTIONS --safe #-}
module Cubical.HITs.Hopf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int hiding (_·_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Interval
  renaming ( zero to I0 ; one to I1 )

Border : (x : S¹) → (j : I) → Partial (j ∨ ~ j) (Σ Type₀ (λ T → T ≃ S¹))
Border x j (j = i0) = S¹ , (x ·_) , rotIsEquiv x
Border x j (j = i1) = S¹ , idEquiv S¹

-- Hopf fibration using SuspS¹
HopfSuspS¹ : SuspS¹ → Type₀
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x j) = Glue S¹ (Border x j)

-- Hopf fibration using S²
-- TODO : prove that it is equivalent to HopfSuspS¹
HopfS² : S² → Type₀
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

-- Hopf fibration using more direct definition of the rot equivalence
-- TODO : prove that it is equivalent to HopfSuspS¹
HopfS²' : S² → Type₀
HopfS²' base = S¹
HopfS²' (surf i j) = Glue S¹ (λ { (i = i0) → _ , rotLoopEquiv i0
                                ; (i = i1) → _ , rotLoopEquiv i0
                                ; (j = i0) → _ , rotLoopEquiv i0
                                ; (j = i1) → _ , rotLoopEquiv i } )

-- Total space of the fibration
TotalHopf : Type₀
TotalHopf = Σ SuspS¹ HopfSuspS¹

-- Forward direction
filler-1 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → join S¹ S¹
filler-1 i j y x = hfill (λ t → λ { (j = i0) → inl (rotInv-1 x y t)
                                  ; (j = i1) → inr x })
                         (inS (push ((unglue (j ∨ ~ j) x) · invLooper y) (unglue (j ∨ ~ j) x) j)) i

TotalHopf→JoinS¹S¹ : TotalHopf → join S¹ S¹
TotalHopf→JoinS¹S¹ (north , x) = inl x
TotalHopf→JoinS¹S¹ (south , x) = inr x
TotalHopf→JoinS¹S¹ (merid y j , x) = filler-1 i1 j y x

-- Backward direction
JoinS¹S¹→TotalHopf : join S¹ S¹ → TotalHopf
JoinS¹S¹→TotalHopf (inl x) = (north , x)
JoinS¹S¹→TotalHopf (inr x) = (south , x)
JoinS¹S¹→TotalHopf (push y x j) =
  (merid (invLooper y · x) j
  , glue (λ { (j = i0) → y ; (j = i1) → x }) (rotInv-2 x y j))

-- Now for the homotopies, we will need to fill squares indexed by x y : S¹ with value in S¹
-- Some will be extremeley tough, but happen to be easy when x = y = base
-- therefore, we fill them for x = y = base and then use the connectedness of S¹ × S¹ and
-- the discreteness of ΩS¹ to get general fillers.

-- To proceed with that strategy, we first need a lemma :
-- the sections of the trivial fibration λ (_ : S¹) (_ : S¹) → Int are constant

-- this should be generalized to a constant fibration over a connected space with
-- discrete fiber
fibℤ : S¹ → S¹ → Type₀
fibℤ _ _ = ℤ

S¹→HSet : (A : Type₀) (p : isSet A) (F : S¹ → A) (x : S¹) → F base ≡ F x
S¹→HSet A p F base = refl {x = F base}
S¹→HSet A p F (loop i) = f' i
  where
  f : PathP (λ i → F base ≡ F (loop i)) refl (cong F loop)
  f i = λ j → F (loop (i ∧ j))
  L : cong F loop ≡ refl
  L = p (F base) (F base) (f i1) refl
  f' : PathP (λ i → F base ≡ F (loop i)) (refl {x = F base}) (refl {x = F base})
  f' = transport (λ i → PathP (λ j → F base ≡ F (loop j)) refl (L i)) f

constant-loop : (F : S¹ → S¹ → ℤ) → (x y : S¹) → F base base ≡ F x y
constant-loop F x y = L0 ∙ L1
  where
  p : isSet (S¹ → ℤ)
  p = isSetΠ (λ _ → isSetℤ)
  L : F base ≡ F x
  L = S¹→HSet (S¹ → ℤ) p F x
  L0 : F base base ≡ F x base
  L0 i = L i base
  L1 : F x base ≡ F x y
  L1 = S¹→HSet ℤ isSetℤ (F x) y

discretefib : (F : S¹ → S¹ → Type₀) → Type₀
discretefib F = (a : (x y : S¹) → F x y) →
        (b : (x y : S¹) → F x y) →
        (a base base ≡ b base base) →
        (x y : S¹) → a x y ≡ b x y

discretefib-fibℤ : discretefib fibℤ
discretefib-fibℤ a b h x y i =
  hcomp (λ t → λ { (i = i0) → constant-loop a x y t
                 ; (i = i1) → constant-loop b x y t })
        (h i)

-- first homotopy

assocFiller-3-aux : I → I → I → I → S¹
assocFiller-3-aux x y j i =
  hfill (λ t → λ { (i = i0) → rotInv-1 (loop y) (loop (~ y) · loop x) t
                 ; (i = i1) → rotInv-3 (loop y) (loop x) t
                 ; (x = i0) (y = i0) → base
                 ; (x = i0) (y = i1) → base
                 ; (x = i1) (y = i0) → base
                 ; (x = i1) (y = i1) → base })
        (inS ((rotInv-2 (loop x) (loop y) i) · (invLooper (loop (~ y) · loop x)))) j

-- assocFiller-3-endpoint is used only in the type of the next function, to specify the
-- second endpoint.
-- However, I only need the first endpoint, but I cannot specify only one of them as is.
-- TODO : use cubical extension types when available to remove assocFiller-3-endpoint
assocFiller-3-endpoint : (x : S¹) → (y : S¹) → y ≡ y
assocFiller-3-endpoint base base i = base
assocFiller-3-endpoint (loop x) base i = assocFiller-3-aux x i0 i1 i
assocFiller-3-endpoint base (loop y) i = assocFiller-3-aux i0 y i1 i
assocFiller-3-endpoint (loop x) (loop y) i = assocFiller-3-aux x y i1 i

assocFiller-3 : (x : S¹) → (y : S¹) →
                PathP (λ j → rotInv-1 y (invLooper y · x) j ≡ rotInv-3 y x j)
                      (λ i → ((rotInv-2 x y i) · (invLooper (invLooper y · x))))
                      (assocFiller-3-endpoint x y)
assocFiller-3 base base j i = base
assocFiller-3 (loop x) base j i = assocFiller-3-aux x i0 j i
assocFiller-3 base (loop y) j i = assocFiller-3-aux i0 y j i
assocFiller-3 (loop x) (loop y) j i = assocFiller-3-aux x y j i

assoc-3 : (_ y : S¹) → basedΩS¹ y
assoc-3 x y i = assocFiller-3 x y i1 i

fibℤ≡fibAssoc-3 : fibℤ ≡ (λ _ y → basedΩS¹ y)
fibℤ≡fibAssoc-3 i = λ x y → basedΩS¹≡ℤ y (~ i)

discretefib-fibAssoc-3 : discretefib (λ _ y → basedΩS¹ y)
discretefib-fibAssoc-3 =
  transp (λ i → discretefib (fibℤ≡fibAssoc-3 i)) i0 discretefib-fibℤ

assocConst-3 : (x y : S¹) → assoc-3 x y ≡ refl
assocConst-3 x y = discretefib-fibAssoc-3 assoc-3 (λ _ _ → refl) refl x y

assocSquare-3 : I → I → S¹ → S¹ → S¹
assocSquare-3 i j x y = hcomp (λ t → λ { (i = i0) → assocFiller-3 x y j i0
                                       ; (i = i1) → assocFiller-3 x y j i1
                                       ; (j = i0) → assocFiller-3 x y i0 i
                                       ; (j = i1) → assocConst-3 x y t i })
                            (assocFiller-3 x y j i)

filler-3 : I → I → S¹ → S¹ → join S¹ S¹
filler-3 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-1 t j (invLooper y · x)
                                           (glue (λ { (j = i0) → y ; (j = i1) → x })
                                                 (rotInv-2 x y j))
                 ; (i = i1) → push (rotInv-3 y x t) x j
                 ; (j = i0) → inl (assocSquare-3 i t x y)
                 ; (j = i1) → inr x })
        (push ((rotInv-2 x y (i ∨ j)) · (invLooper (invLooper y · x))) (rotInv-2 x y (i ∨ j)) j)

JoinS¹S¹→TotalHopf→JoinS¹S¹ : ∀ x → TotalHopf→JoinS¹S¹ (JoinS¹S¹→TotalHopf x) ≡ x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (inl x) i = inl x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (inr x) i = inr x
JoinS¹S¹→TotalHopf→JoinS¹S¹ (push y x j) i = filler-3 i j y x

-- Second homotopy

-- This HIT is the total space of the Hopf fibration but the ends of SuspS¹ have not been
-- glued together yet — which makes it into a cylinder.
-- This allows to write compositions that do not properly match at the endpoints. However,
-- I suspect it is unnecessary. TODO : do without PseudoHopf

PseudoHopf : Type₀
PseudoHopf = (S¹ × Interval) × S¹

PseudoHopf-π1 : PseudoHopf → S¹
PseudoHopf-π1 ((y , _) , _) = y

PseudoHopf-π2 : PseudoHopf → S¹
PseudoHopf-π2 (_ , x) = x

assocFiller-4-aux : I → I → I → I → S¹
assocFiller-4-aux x y j i =
  hfill (λ t → λ { (i = i0) → ((invLooper (loop y · loop x · loop (~ y))) · (loop y · loop x))
                              · (rotInv-1 (loop x) (loop y) t)
                 ; (i = i1) → (rotInv-4 (loop y) (loop y · loop x) (~ t)) · loop x
                 ; (x = i0) (y = i0) → base
                 ; (x = i0) (y = i1) → base
                 ; (x = i1) (y = i0) → base
                 ; (x = i1) (y = i1) → base })
        (inS (rotInv-2 (loop y · loop x) (loop y · loop x · loop (~ y)) i)) j

-- See assocFiller-3-endpoint
-- TODO : use cubical extension types when available to remove assocFiller-4-endpoint
assocFiller-4-endpoint : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
assocFiller-4-endpoint base base i = base
assocFiller-4-endpoint (loop x) base i = assocFiller-4-aux x i0 i1 i
assocFiller-4-endpoint base (loop y) i = assocFiller-4-aux i0 y i1 i
assocFiller-4-endpoint (loop x) (loop y) i = assocFiller-4-aux x y i1 i

assocFiller-4 : (x y : S¹) →
                PathP (λ j → ((invLooper (y · x · invLooper y)) · (y · x)) · (rotInv-1 x y j) ≡ (rotInv-4 y (y · x) (~ j)) · x)
                      (λ i → (rotInv-2 (y · x) (y · x · invLooper y) i))
                      (assocFiller-4-endpoint x y)
assocFiller-4 base base j i = base
assocFiller-4 (loop x) base j i = assocFiller-4-aux x i0 j i
assocFiller-4 base (loop y) j i = assocFiller-4-aux i0 y j i
assocFiller-4 (loop x) (loop y) j i = assocFiller-4-aux x y j i

assoc-4 : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
assoc-4 x y i = assocFiller-4 x y i1 i

fibℤ≡fibAssoc-4 : fibℤ ≡ (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
fibℤ≡fibAssoc-4 i = λ x y → basedΩS¹≡ℤ (((invLooper (y · x · invLooper y)) · (y · x)) · x) (~ i)

discretefib-fibAssoc-4 : discretefib (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
discretefib-fibAssoc-4 =
  transp (λ i → discretefib (fibℤ≡fibAssoc-4 i)) i0 discretefib-fibℤ

assocConst-4 : (x y : S¹) → assoc-4 x y ≡ refl
assocConst-4 x y = discretefib-fibAssoc-4 assoc-4 (λ _ _ → refl) refl x y

assocSquare-4 : I → I → S¹ → S¹ → S¹
assocSquare-4 i j x y =
  hcomp (λ t → λ { (i = i0) → assocFiller-4 x y j i0
                 ; (i = i1) → assocFiller-4 x y j i1
                 ; (j = i0) → assocFiller-4 x y i0 i
                 ; (j = i1) → assocConst-4 x y t i })
        (assocFiller-4 x y j i)

filler-4-0 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-0 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                              , invLooper (y · x · invLooper y) · (y · x) · (rotInv-1 x y t))
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        (inS ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) j)) i

filler-4-1 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-1 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                              , (rotInv-4 y (y · x) (~ t)) · x)
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        (inS ((invLooper (x' · invLooper y) · x' , seg j) , unglue (j ∨ ~ j) x)) i

filler-4-2 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
filler-4-2 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → JoinS¹S¹→TotalHopf (filler-1 t j y x)
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-0 t j y x)) j
                              , glue (λ { (j = i0) → rotInv-1 x y t ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-4-0 t j y x)))
                 ; (j = i0) → (north , rotInv-1 x y t)
                 ; (j = i1) → (south , x) })
        (merid (invLooper (x' · invLooper y) · x') j
        , glue (λ { (j = i0) → y · x · invLooper y ; (j = i1) → x }) (rotInv-2 x' (x' · invLooper y) j))

filler-4-3 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-3 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → filler-4-0 t j y x
                 ; (i = i1) → filler-4-1 t j y x
                 ; (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0) , assocSquare-4 i t x y)
                 ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
        ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) (i ∨ j))

filler-4-4 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
filler-4-4 i j y x =
  let x' = unglue (j ∨ ~ j) x in
  hcomp (λ t → λ { (i = i0) → filler-4-1 t j y x
                 ; (i = i1) → ((y , seg j) , unglue (j ∨ ~ j) x)
                 ; (j = i0) → ((rotInv-4 y (y · x) i , I0)
                              , (rotInv-4 y (y · x) (i ∨ ~ t)) · x)
                 ; (j = i1) → ((rotInv-4 y x i , I1) , x) })
        ((rotInv-4 y x' i , seg j) , x')

filler-4-5 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
filler-4-5 i j y x =
  hcomp (λ t → λ { (i = i0) → filler-4-2 (~ t) j y x
                 ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-4 t j y x)) j
                              , glue (λ { (j = i0) → x ; (j = i1) → x })
                                     (PseudoHopf-π2 (filler-4-4 t j y x)))
                 ; (j = i0) → (north , x)
                 ; (j = i1) → (south , x) })
        (merid (PseudoHopf-π1 (filler-4-3 i j y x)) j
        , glue (λ { (j = i0) → x ; (j = i1) → x }) (PseudoHopf-π2 (filler-4-3 i j y x)))

TotalHopf→JoinS¹S¹→TotalHopf : ∀ x → JoinS¹S¹→TotalHopf (TotalHopf→JoinS¹S¹ x) ≡ x
TotalHopf→JoinS¹S¹→TotalHopf (north , x) i = (north , x)
TotalHopf→JoinS¹S¹→TotalHopf (south , x) i = (south , x)
TotalHopf→JoinS¹S¹→TotalHopf (merid y j , x) i = filler-4-5 i j y x


JoinS¹S¹≡TotalHopf : join S¹ S¹ ≡ TotalHopf
JoinS¹S¹≡TotalHopf = isoToPath (iso JoinS¹S¹→TotalHopf
                                    TotalHopf→JoinS¹S¹
                                    TotalHopf→JoinS¹S¹→TotalHopf
                                    JoinS¹S¹→TotalHopf→JoinS¹S¹)

S³≡TotalHopf : S³ ≡ TotalHopf
S³≡TotalHopf = S³≡joinS¹S¹ ∙ JoinS¹S¹≡TotalHopf

open Iso
IsoS³TotalHopf : Iso (S₊ 3) TotalHopf
fun IsoS³TotalHopf x = JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 x))
inv IsoS³TotalHopf x = fun IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x))
rightInv IsoS³TotalHopf x =
     cong (JoinS¹S¹→TotalHopf ∘ S³→joinS¹S¹)
          (leftInv IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x)))
  ∙∙ cong JoinS¹S¹→TotalHopf
          (joinS¹S¹→S³→joinS¹S¹ (TotalHopf→JoinS¹S¹ x))
  ∙∙ TotalHopf→JoinS¹S¹→TotalHopf x
leftInv IsoS³TotalHopf x =
     cong (fun IsoS³S3 ∘ joinS¹S¹→S³)
          (JoinS¹S¹→TotalHopf→JoinS¹S¹ (S³→joinS¹S¹ (inv IsoS³S3 x)))
  ∙∙ cong (fun IsoS³S3) (S³→joinS¹S¹→S³ (inv IsoS³S3 x))
  ∙∙ Iso.rightInv IsoS³S3 x

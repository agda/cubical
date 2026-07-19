{-

Mayer-Vietoris cofiber sequence:

  Let X be a pointed type, and let a span B ←[f]- X -[g]→ C be given.
  Then the mapping cone of the canonical map (B ⋁ C) → B ⊔_X C is equivalent to Susp X.

The sequence Susp X → (B ⋁ C) → B ⊔_X C therefore induces a long exact sequence in cohomology.
Proof is adapted from Evan Cavallo's master's thesis.

-}
module Cubical.Homotopy.MayerVietorisCofiber where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed

open import Cubical.Data.Unit

open import Cubical.HITs.MappingCones
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge

module _ {ℓX ℓB ℓC} {X : Pointed ℓX} {B : Type ℓB} {C : Type ℓC} (f : X .fst → B) (g : X .fst → C)
  where

  private
    Y : Pointed _
    Y = (B , f (X .snd))

    Z : Pointed _
    Z = (C , g (X .snd))

  wedgeToPushout : Y ⋁ Z → Pushout f g
  wedgeToPushout (inl y) = inl y
  wedgeToPushout (inr z) = inr z
  wedgeToPushout (push _ i) = push (pt X) i

  pushoutToSusp : Pushout f g → Susp (X .fst)
  pushoutToSusp (inl y) = north
  pushoutToSusp (inr z) = south
  pushoutToSusp (push x i) = merid x i

  {-
    Coherence lemma:
    To construct a function f : (c : Cone wedgeToPushout) → D c, we can always
    adjust the definition of (f (spoke (inr z) i)) so that there is a canonical
    choice for (f (spoke (push tt j) i))
  -}
  module Helper {ℓD} {D : Cone wedgeToPushout → Type ℓD}
    (inj* : ∀ w → D (inj w))
    (hub* : D hub)
    (inl* : ∀ y → PathP (λ i → D (spoke (inl y) i)) hub* (inj* (inl y)))
    (inr* : ∀ z → PathP (λ i → D (spoke (inr z) i)) hub* (inj* (inr z)))
    where

    cap : (i j : I) → D (spoke (push tt j) i)
    cap i j =
      fill
        (λ i → D (spoke (push tt j) (~ i)))
        (λ i → λ
          { (j = i0) → inl* (Y .snd) (~ i)
          ; (j = i1) → inr* (Z .snd) (~ i)
          })
        (inS (inj* (push (X .snd) j)))
        (~ i)

    cap0 : (j : I) → D hub
    cap0 = cap i0

    face-i≡0 : (k j : I) → D hub
    face-i≡0 k j =
      hfill
        (λ j → λ
          { (k = i0) → cap0 j
          ; (k = i1) → hub*
          })
        (inS hub*)
        j

    inrFiller : ∀ z → (k i : I) → D (spoke (inr z) i)
    inrFiller z k i =
     hfill
       (λ k → λ
         { (i = i0) → face-i≡0 k i1
         ; (i = i1) → inj* (inr z)
         })
       (inS (inr* z i))
       k

    fun : ∀ c → D c
    fun (inj w) = inj* w
    fun hub = hub*
    fun (spoke (inl y) i) = inl* y i
    fun (spoke (inr z) i) = inrFiller z i1 i
    fun (spoke (push tt j) i) =
      hcomp
        (λ k → λ
          { (i = i0) → face-i≡0 k j
          ; (i = i1) → inj* (push (X .snd) j)
          ; (j = i0) → inl* (Y .snd) i
          })
        (cap i j)

  equiv : Cone wedgeToPushout ≃ Susp (X .fst)
  equiv = isoToEquiv (iso fwd bwd fwdBwd bwdFwd)
    where
    fwd : Cone wedgeToPushout → Susp (X .fst)
    fwd (inj w) = pushoutToSusp w
    fwd hub = north
    fwd (spoke (inl y) i) = north
    fwd (spoke (inr z) i) = merid (X .snd) i
    fwd (spoke (push tt j) i) = merid (X .snd) (i ∧ j)

    bwd : Susp (X .fst) → Cone wedgeToPushout
    bwd north = hub
    bwd south = hub
    bwd (merid x i) =
      hcomp
        (λ k → λ
          { (i = i0) → spoke (inl (f x)) (~ k)
          ; (i = i1) → spoke (inr (g x)) (~ k)
          })
        (inj (push x i))

    bwdPushout : (w : Pushout f g) → bwd (pushoutToSusp w) ≡ inj w
    bwdPushout (inl y) = spoke (inl y)
    bwdPushout (inr z) = spoke (inr z)
    bwdPushout (push x i) k =
      hfill
        (λ k → λ
          { (i = i0) → spoke (inl (f x)) (~ k)
          ; (i = i1) → spoke (inr (g x)) (~ k)
          })
        (inS (inj (push x i)))
        (~ k)

    bwdMeridPt : refl ≡ cong bwd (merid (X .snd))
    bwdMeridPt j i =
      hcomp
        (λ k → λ
          { (i = i0) → spoke (inl (Y .snd)) (~ k)
          ; (i = i1) → spoke (inr (Z .snd)) (~ k)
          ; (j = i0) → spoke (push _ i) (~ k)
          })
        (inj (push (X .snd) i))

    bwdFwd : (c : Cone wedgeToPushout) → bwd (fwd c) ≡ c
    bwdFwd =
      Helper.fun
        bwdPushout
        refl
        (λ y i k → spoke (inl y) (i ∧ k))
        (λ z i k →
          hcomp
            (λ l → λ
              { (i = i0) → hub
              ; (i = i1) → spoke (inr z) k
              ; (k = i0) → bwdMeridPt l i
              ; (k = i1) → spoke (inr z) i
              })
            (spoke (inr z) (i ∧ k)))

    fwdBwd : (s : Susp (X .fst)) → fwd (bwd s) ≡ s
    fwdBwd north = refl
    fwdBwd south = merid (X .snd)
    fwdBwd (merid a i) j =
      fill
        (λ _ → Susp (X .fst))
        (λ j → λ
          { (i = i0) → north
          ; (i = i1) → merid (X .snd) (~ j)
          })
        (inS (merid a i))
        (~ j)

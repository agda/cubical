module Cubical.Algebra.CommRing.Instances.Fast.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Fast.Int as Int renaming (_+_ to _+ℤ_; _·_ to _·ℤ_ ; -_ to -ℤ_)

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)

ℤCommRing : CommRing ℓ-zero
fst ℤCommRing = ℤ
0r (snd ℤCommRing) = pos 0
1r (snd ℤCommRing) = pos 1
_+_ (snd ℤCommRing) = _+ℤ_
_·_ (snd ℤCommRing) = _·ℤ_
- snd ℤCommRing = -ℤ_
isCommRing (snd ℤCommRing) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing (pos 0) (pos 1) _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc +IdR
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·IdR ·DistR+ Int.·Comm

private
  variable
    ℓ : Level

module CanonicalHomFromℤ (R : CommRing ℓ) where

  private
    module R where
      open CommRingStr (snd R) public
      open RingTheory (CommRing→Ring R) public

  suc-fromℕ : ∀ x → R.fromℕ (suc x) ≡ R.1r R.+ R.fromℕ x
  suc-fromℕ zero    = sym (R.+IdR R.1r)
  suc-fromℕ (suc x) = refl

  fromℕ-pres+ : (x y : ℕ) → R.fromℕ (x ℕ.+ y) ≡ R.fromℕ x R.+ R.fromℕ y
  fromℕ-pres+ zero          y = sym (R.+IdL _)
  fromℕ-pres+ (suc zero)    y = suc-fromℕ y
  fromℕ-pres+ (suc (suc x)) y = cong (R.1r R.+_) (fromℕ-pres+ (suc x) y) ∙ R.+Assoc _ _ _

  fromℤ-pres- : (x : ℤ) → R.fromℤ (-ℤ x) ≡ R.- R.fromℤ x
  fromℤ-pres- (pos zero)    = sym R.0Selfinverse
  fromℤ-pres- (pos (suc n)) = refl
  fromℤ-pres- (negsuc n)    = sym (R.-Idempotent _)

  suc-fromℤ : ∀ z → R.fromℤ (1 +ℤ z) ≡ R.1r R.+ R.fromℤ (z)
  suc-fromℤ (pos n)          = suc-fromℕ n
  suc-fromℤ (negsuc zero)    = sym (R.+InvR R.1r)
  suc-fromℤ (negsuc (suc n)) =
       sym (cong (R._+ (R.- R.fromℕ (suc n))) (R.+InvR _) ∙ R.+IdL _)
    ∙∙ sym (R.+Assoc _ _ _)
    ∙∙ cong (R.1r R.+_) (R.-Dist _ _)

  fromℤ-pres+' : (n m : ℕ) →
    R.fromℤ (pos n +ℤ negsuc m) ≡
    R.fromℤ (pos n) R.+ R.fromℤ (negsuc m)
  fromℤ-pres+' zero    m = sym (R.+IdL _)
  fromℤ-pres+' (suc n) m =
      (cong R.fromℤ (sym (+Assoc 1 (pos n) (negsuc m)))
    ∙ suc-fromℤ (pos n +ℤ negsuc m))
    ∙∙ cong (R.1r R.+_) (fromℤ-pres+' n m)
    ∙∙ R.+Assoc _ _ _
    ∙ cong (R._+ R.fromℤ (negsuc m))
     (sym (suc-fromℕ n))

  fromℤ-pres+ : (x y : ℤ) → R.fromℤ (x +ℤ y) ≡ R.fromℤ x R.+ R.fromℤ y
  fromℤ-pres+ (pos n)    (pos m)    = fromℕ-pres+  n m
  fromℤ-pres+ (pos n)    (negsuc m) = fromℤ-pres+' n m
  fromℤ-pres+ (negsuc n) (pos m)    = fromℤ-pres+' m n ∙ R.+Comm _ _
  fromℤ-pres+ (negsuc n) (negsuc m) =
      cong (R.-_)
      (cong (R.1r R.+_) (cong R.fromℕ (sym (ℕ.+-suc n m)))
        ∙ sym (suc-fromℕ (n ℕ.+ suc m))
        ∙ fromℕ-pres+ (suc n) (suc m))
    ∙ sym (R.-Dist _ _)

  fromℕ-pres· : (x y : ℕ) → R.fromℕ (x ℕ.· y) ≡ R.fromℕ x R.· R.fromℕ y
  fromℕ-pres· zero y    = sym (R.0LeftAnnihilates _)
  fromℕ-pres· (suc x) y =
      fromℕ-pres+ y (x ℕ.· y)
    ∙∙ cong₂ (R._+_) (sym (R.·IdL _)) (fromℕ-pres· x y)
    ∙∙ sym (R.·DistL+ _ _ _)
    ∙ cong (R._· R.fromℕ y) (sym (suc-fromℕ x))
  fromℤ-pres· : (x y : ℤ) → R.fromℤ (x ·ℤ y) ≡ R.fromℤ x R.· R.fromℤ y
  fromℤ-pres· (pos n) (pos m)    = fromℕ-pres· n m
  fromℤ-pres· (pos n) (negsuc m) =
      cong R.fromℤ (sym (-DistR· (pos n) (pos (suc m))))
    ∙∙ (fromℤ-pres- (pos (n ℕ.· suc m))
      ∙ cong R.-_ (fromℕ-pres· n (suc m)))
    ∙∙ sym (R.-DistR· _ _)
  fromℤ-pres· (negsuc n) (pos m) =
      cong R.fromℤ (sym (-DistL· (pos (suc n)) (pos m)))
    ∙∙ (fromℤ-pres- (pos ((suc n) ℕ.· m))
      ∙ cong R.-_ (fromℕ-pres· (suc n) m))
    ∙∙ sym (R.-DistL· _ _)
  fromℤ-pres· (negsuc n) (negsuc m) =
       fromℕ-pres· (suc n) (suc m)
    ∙∙ cong₂ R._·_ (sym (R.-Idempotent _)) refl
    ∙∙ R.-Swap· _ _

  isHomFromℤ : IsCommRingHom (ℤCommRing .snd) R.fromℤ (R .snd)
  isHomFromℤ .IsCommRingHom.pres0 = refl
  isHomFromℤ .IsCommRingHom.pres1 = refl
  isHomFromℤ .IsCommRingHom.pres+ = fromℤ-pres+
  isHomFromℤ .IsCommRingHom.pres· = fromℤ-pres·
  isHomFromℤ .IsCommRingHom.pres- = fromℤ-pres-

  fromℤHom : CommRingHom ℤCommRing R
  fst fromℤHom = R.fromℤ
  snd fromℤHom = isHomFromℤ

  module _ (φ : CommRingHom ℤCommRing R) where

    open IsCommRingHom (snd φ)

    isUniqueFromℕ : ∀ n → R.fromℕ n ≡ φ $cr pos n
    isUniqueFromℕ zero            = sym pres0
    isUniqueFromℕ (suc zero)      = sym pres1
    isUniqueFromℕ (suc k@(suc n)) = cong₂ R._+_ (sym pres1) (isUniqueFromℕ k)
                                  ∙ sym (pres+ 1 (pos k))

    isUniqueFromℤ : ∀ n → R.fromℤ n ≡ φ $cr n
    isUniqueFromℤ (pos n)    = isUniqueFromℕ n
    isUniqueFromℤ (negsuc n) = cong R.-_ (isUniqueFromℕ (suc n))
                             ∙ sym (pres- (pos (suc n)))

  isContrHom[ℤCR,-] : isContr (CommRingHom ℤCommRing R)
  fst isContrHom[ℤCR,-] = fromℤHom
  snd isContrHom[ℤCR,-] = CommRingHom≡ ∘ funExt ∘ isUniqueFromℤ

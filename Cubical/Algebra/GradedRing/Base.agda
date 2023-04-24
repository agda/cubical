{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.GradedRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.Algebra.GradedRing.DirectSumHIT

private variable
  ℓ ℓ' : Level

open AbGroupStr
open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆


-----------------------------------------------------------------------------
-- Definition

record IsGradedRing (R    : Ring (ℓ-max ℓ ℓ'))
                    (IdM  : Monoid ℓ)
                    (G    : (k : (fst IdM)) → Type ℓ')
                    (Gstr : (k : fst IdM) → AbGroupStr (G k))
                    (1⋆   : G (MonoidStr.ε (snd IdM)))
                    (_⋆_  : {k l : fst IdM} → G k → G l → G (MonoidStr._·_ (snd IdM) k l))
                    : Type (ℓ-max ℓ ℓ')
                    where

  constructor isgradedring

  private
    Idx = fst IdM
    open MonoidStr (snd IdM)

  field
    0-⋆     : {k l : Idx} → (b : G l) → (0g (Gstr k)) ⋆ b ≡ 0g (Gstr (k · l))
    ⋆-0     : {k l : Idx} → (a : G k) → a ⋆ (0g (Gstr l)) ≡ 0g (Gstr (k · l))
    ⋆Assoc  : {k l m : Idx} → (a : G k) → (b : G l) → (c : G m) →
              ((k · (l · m)) , (a ⋆ (b ⋆ c))) ≡ (((k · l) · m) , ((a ⋆ b) ⋆ c))
    ⋆IdR    : {k : Idx} → (a : G k) → ( k · ε , a ⋆ 1⋆ ) ≡ (k , a)
    ⋆IdL    : {l : Idx} → (b : G l) → ( ε · l , 1⋆ ⋆ b ) ≡ (l , b)
    ⋆DistR+ : {k l : Idx} → (a : G k) → (b c : G l) →
              a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (k · l) ._+_ (a ⋆ b) (a ⋆ c)
    ⋆DistL+ : {k l : Idx} → (a b : G k) → (c : G l) →
              ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (k · l) ._+_ (a ⋆ c) (b ⋆ c)
    equivRing : RingEquiv R (⊕HITgradedRing-Ring IdM G Gstr 1⋆ _⋆_
                             0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+)


record GradedRingStr (R : Ring (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor gradedringstr

  field
    IdM  : Monoid ℓ
    G    : (k : (fst IdM)) → Type ℓ'
    Gstr : (k : fst IdM) → AbGroupStr (G k)
    1⋆   : G (MonoidStr.ε (snd IdM))
    _⋆_  : {k l : fst IdM} → G k → G l → G (MonoidStr._·_ (snd IdM) k l)
    isGradedRing : IsGradedRing R IdM G Gstr 1⋆ _⋆_

  open IsGradedRing isGradedRing public


GradedRing : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
GradedRing ℓ ℓ' = Σ[ R ∈ Ring (ℓ-max ℓ ℓ') ] GradedRingStr R


-----------------------------------------------------------------------------
-- make

open MonoidStr

makeIsGradedRing : {R : Ring (ℓ-max ℓ ℓ')} {IdM : Monoid ℓ}
                   {G       : (k : (fst IdM)) → Type ℓ'}
                   {Gstr    : (k : fst IdM) → AbGroupStr (G k)}
                   {1⋆      : G (ε (snd IdM))}
                   {_⋆_     : {k l : fst IdM} → G k → G l → G (_·_ (snd IdM) k l)}
                   (0-⋆     : {k l : fst IdM} (b : G l) → (0g (Gstr k) ⋆ b) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                   (⋆-0     : {k l : fst IdM} (a : G k) → (a ⋆ 0g (Gstr l)) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                   (⋆Assoc  : {k l m : fst IdM} (a : G k) (b : G l) (c : G m) →
                                 (((snd IdM ._·_ k) ((snd IdM ._·_ l) m) , (a ⋆ (b ⋆ c))))
                               ≡ ((snd IdM ._·_ ((snd IdM ._·_ k) l) m) , ((a ⋆ b) ⋆ c)))
                   (⋆IdR    : {k : fst IdM} → (a : G k) → ( snd IdM ._·_ k (snd IdM .ε) , a ⋆ 1⋆ ) ≡ (k , a))
                   (⋆IdL    : {l : fst IdM} → (b : G l) → ( snd IdM ._·_ (snd IdM .ε) l , 1⋆ ⋆ b ) ≡ (l , b))
                   (⋆DistR+ : {k l : fst IdM} → (a : G k) → (b c : G l) →
                              a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ b) (a ⋆ c))
                   (⋆DistL+ : {k l : fst IdM} → (a b : G k) → (c : G l) →
                              ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ c) (b ⋆ c))
                   (equivRing : RingEquiv R (⊕HITgradedRing-Ring IdM G Gstr 1⋆ _⋆_
                                             0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+))
           → IsGradedRing R IdM G Gstr 1⋆ _⋆_
makeIsGradedRing 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing =
  isgradedring 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing



makeGradedRing : (R : Ring (ℓ-max ℓ ℓ')) (IdM : Monoid ℓ)
                 (G      : (k : (fst IdM)) → Type ℓ')
                 (Gstr   : (k : fst IdM) → AbGroupStr (G k))
                 (1⋆     : G (ε (snd IdM)))
                 (_⋆_    : {k l : fst IdM} → G k → G l → G (_·_ (snd IdM) k l))
                 (0-⋆    : {k l : fst IdM} (b : G l) → (0g (Gstr k) ⋆ b) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                 (⋆-0    : {k l : fst IdM} (a : G k) → (a ⋆ 0g (Gstr l)) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                 (⋆Assoc : {k l m : fst IdM} (a : G k) (b : G l) (c : G m) →
                              (((snd IdM ._·_ k) ((snd IdM ._·_ l) m) , (a ⋆ (b ⋆ c))))
                            ≡ ((snd IdM ._·_ ((snd IdM ._·_ k) l) m) , ((a ⋆ b) ⋆ c)))
                 (⋆IdR    : {k : fst IdM} → (a : G k) → (snd IdM ._·_ k (snd IdM .ε) , a ⋆ 1⋆ ) ≡ (k , a))
                 (⋆IdL    : {l : fst IdM} → (b : G l) → (snd IdM ._·_ (snd IdM .ε) l , 1⋆ ⋆ b ) ≡ (l , b))
                 (⋆DistR+ : {k l : fst IdM} → (a : G k) → (b c : G l) →
                            a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ b) (a ⋆ c))
                 (⋆DistL+ : {k l : fst IdM} → (a b : G k) → (c : G l) →
                            ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ c) (b ⋆ c))
                 (equivRing : RingEquiv R (⊕HITgradedRing-Ring IdM G Gstr 1⋆ _⋆_
                                             0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+))
                  → GradedRing ℓ ℓ'
fst (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing) = R
GradedRingStr.IdM (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) = IdM
GradedRingStr.G (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) = G
GradedRingStr.Gstr (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) = Gstr
GradedRingStr.1⋆ (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) = 1⋆
GradedRingStr._⋆_ (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) = _⋆_
GradedRingStr.isGradedRing (snd (makeGradedRing R IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing)) =
  makeIsGradedRing 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ equivRing



makeGradedRingSelf : (IdM : Monoid ℓ)
                     (G      : (k : (fst IdM)) → Type ℓ')
                     (Gstr   : (k : fst IdM) → AbGroupStr (G k))
                     (1⋆     : G (ε (snd IdM)))
                     (_⋆_    : {k l : fst IdM} → G k → G l → G (_·_ (snd IdM) k l))
                     (0-⋆    : {k l : fst IdM} (b : G l) → (0g (Gstr k) ⋆ b) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                     (⋆-0    : {k l : fst IdM} (a : G k) → (a ⋆ 0g (Gstr l)) ≡ 0g (Gstr ((snd IdM MonoidStr.· k) l)))
                     (⋆Assoc : {k l m : fst IdM} (a : G k) (b : G l) (c : G m) →
                                _≡_ {A = Σ[ k ∈ fst IdM ] G k} (((snd IdM ._·_ k) ((snd IdM ._·_ l) m) , (a ⋆ (b ⋆ c))))
                                                               ((snd IdM ._·_ ((snd IdM ._·_ k) l) m) , ((a ⋆ b) ⋆ c)))
                     (⋆IdR    : {k : fst IdM} → (a : G k) →
                                _≡_ {A = Σ[ k ∈ fst IdM ] G k} ( snd IdM ._·_ k (snd IdM .ε) , a ⋆ 1⋆ ) (k , a))
                     (⋆IdL    : {l : fst IdM} → (b : G l) →
                                _≡_ {A = Σ[ k ∈ fst IdM ] G k} ( snd IdM ._·_ (snd IdM .ε) l , 1⋆ ⋆ b ) (l , b))
                     (⋆DistR+ : {k l : fst IdM} → (a : G k) → (b c : G l) →
                                a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ b) (a ⋆ c))
                     (⋆DistL+ : {k l : fst IdM} → (a b : G k) → (c : G l) →
                                ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (snd IdM ._·_ k l) ._+_ (a ⋆ c) (b ⋆ c))
                     → GradedRing ℓ ℓ'
makeGradedRingSelf IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+ =
  makeGradedRing (⊕HITgradedRing-Ring IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+)
                 IdM G Gstr 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+
                 ((idEquiv _) , (makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)))

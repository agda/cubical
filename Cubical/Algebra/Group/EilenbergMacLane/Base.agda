{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1 hiding (elim)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec) hiding (elim)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat hiding (_·_ ; elim)
open import Cubical.HITs.Susp
open import Cubical.Functions.Morphism
open import Cubical.Foundations.Path

private
  variable ℓ ℓ' : Level

  _* = AbGroup→Group

EM-raw : (G : AbGroup ℓ) (n : ℕ) → Type ℓ
EM-raw G zero = fst G
EM-raw G (suc zero) = EM₁ (G *)
EM-raw G (suc (suc n)) = Susp (EM-raw G (suc n))

ptEM-raw : {n : ℕ} {G : AbGroup ℓ} → EM-raw G n
ptEM-raw {n = zero} {G = G} = AbGroupStr.0g (snd G)
ptEM-raw {n = suc zero} {G = G} = embase
ptEM-raw {n = suc (suc n)} {G = G} = north

raw-elim : (G : AbGroup ℓ) (n : ℕ) {A : EM-raw G (suc n) → Type ℓ'}
            → ((x : _) → isOfHLevel (suc n) (A x) )
            → A ptEM-raw
            → (x : _) → A x
raw-elim G zero hlev b = elimProp _ hlev b
raw-elim G (suc n) hlev b north = b
raw-elim G (suc n) {A = A} hlev b south = subst A (merid ptEM-raw) b
raw-elim G (suc n) {A = A} hlev b (merid a i) = help a i
  where
  help : (a : _) → PathP (λ i → A (merid a i)) b (subst A (merid ptEM-raw) b)
  help = raw-elim G n (λ _ → isOfHLevelPathP' (suc n) (hlev _) _ _)
         λ i → transp (λ j → A (merid ptEM-raw (j ∧ i))) (~ i) b

EM : (G : AbGroup ℓ) (n : ℕ) → Type ℓ
EM G zero = EM-raw G zero
EM G (suc zero) = EM-raw G 1
EM G (suc (suc n)) = hLevelTrunc (4 + n) (EM-raw G (suc (suc n)))

0ₖ : {G : AbGroup ℓ} (n : ℕ) → EM G n
0ₖ {G = G} zero = AbGroupStr.0g (snd G)
0ₖ (suc zero) = embase
0ₖ (suc (suc n)) = ∣ ptEM-raw ∣

EM∙ : (G : AbGroup ℓ) (n : ℕ) → Pointed ℓ
EM∙ G n = EM G n , (0ₖ n)

EM-raw∙ : (G : AbGroup ℓ) (n : ℕ) → Pointed ℓ
EM-raw∙ G n = EM-raw G n , ptEM-raw

hLevelEM : (G : AbGroup ℓ) (n : ℕ) → isOfHLevel (2 + n) (EM G n)
hLevelEM G zero = AbGroupStr.is-set (snd G)
hLevelEM G (suc zero) = emsquash
hLevelEM G (suc (suc n)) = isOfHLevelTrunc (4 + n)

EM-raw→EM : (G : AbGroup ℓ) (n : ℕ) → EM-raw G n → EM G n
EM-raw→EM G zero x = x
EM-raw→EM G (suc zero) x = x
EM-raw→EM G (suc (suc n)) = ∣_∣

elim : {G : AbGroup ℓ} (n : ℕ) {A : EM G n → Type ℓ'}
        → ((x : _) → isOfHLevel (2 + n) (A x))
        → ((x : EM-raw G n) → A (EM-raw→EM G n x))
        → (x : _) → A x
elim zero hlev hyp x = hyp x
elim (suc zero) hlev hyp x = hyp x
elim (suc (suc n)) hlev hyp = trElim (λ _ → hlev _) hyp


EM' : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ) → Type ℓ
EM' G zero = fst G
EM' G (suc zero) = EM₁-raw (AbGroup→Group G)
EM' G (suc (suc n)) = EM-raw G (suc (suc n))

EM'∙ : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ) → Pointed ℓ
fst (EM'∙ G n) = EM' G n
snd (EM'∙ G zero) = AbGroupStr.0g (snd G)
snd (EM'∙ G (suc zero)) = embase-raw
snd (EM'∙ G (suc (suc n))) = north

EM'→EM : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ) → EM' G n → EM G n
EM'→EM G zero x = x
EM'→EM G (suc zero) x = EM₁-raw→EM₁ _ x
EM'→EM G (suc (suc n)) x = ∣ x ∣ₕ

EM'→EM∙ : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ) → EM'→EM G n (EM'∙ G n .snd) ≡ EM∙ G n .snd
EM'→EM∙ G zero = refl
EM'→EM∙ G (suc zero) = refl
EM'→EM∙ G (suc (suc n)) = refl

EM'-elim : ∀ {ℓ ℓ'} (G : AbGroup ℓ) (n : ℕ) {B : EM G n → Type ℓ'}
         → ((x : _) → isOfHLevel (suc n) (B x))
         → ((x : EM' G n) → (B (EM'→EM _ _ x)))
         → (x : _ ) → B x
EM'-elim G zero {B = B} hlev ind = ind
EM'-elim G (suc zero) {B = B} hlev ind =
  elimSet _ hlev (ind embase-raw) λ g → cong ind (emloop-raw g)
EM'-elim G (suc (suc n)) {B = B} hlev ind =
  Trunc.elim (λ _ → isOfHLevelSuc (3 + n) (hlev _)) ind

EM'-trivElim : (G : AbGroup ℓ) (n : ℕ) {A : EM' G (suc n) → Type ℓ'}
            → ((x : _) → isOfHLevel (suc n) (A x) )
            → A (snd (EM'∙ G (suc n)))
            → (x : _) → A x
EM'-trivElim G zero {A = A} prop x embase-raw = x
EM'-trivElim G zero {A = A} prop x (emloop-raw g i) =
  isProp→PathP {B = λ i → A (emloop-raw g i)} (λ _ → prop _) x x i
EM'-trivElim G (suc n) {A = A} = raw-elim G (suc n)

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Nat.Lower where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

isMono : (ℕ → Bool) → Type
isMono f = ∀ n → f n ≥ f (suc n)

isMonoIsProp : ∀ f → isProp (isMono f)
isMonoIsProp f = isPropΠ λ n → ≥-isProp (f n) (f (suc n))

isMonoIsPropDep : isPropDep isMono
isMonoIsPropDep = isOfHLevel→isOfHLevelDep 1 isMonoIsProp {_}

Mono : Type
Mono = Σ _ isMono

MonoIsSet : isSet Mono
MonoIsSet = isSetΣ (isSet→ isSetBool) (isProp→isSet ∘ isMonoIsProp)

private
  variable
    ℓ : Level
    m n : Mono

private
  mz : ℕ → Bool
  mz _ = false

  ms : (ℕ → Bool) → (ℕ → Bool)
  ms _ zero = true
  ms f (suc m) = f m

  msm : ∀{f} → isMono f → isMono (ms f)
  msm _ zero = _
  msm mf (suc m) = mf m

  mp : (ℕ → Bool) → (ℕ → Bool)
  mp f k = f (suc k)

  ms-mp : ∀ f → f 0 ≡ true → ms (mp f) ≡ f
  ms-mp f p i 0 = p (~ i)
  ms-mp f p i (suc k) = f (suc k)

  mz-lemma : ∀ f → isMono f → f 0 ≡ false → ∀ k → false ≡ f k
  mz-lemma f  _ p zero = sym p
  mz-lemma f mf p (suc k)
    with f 1
      | inspect f 1
      | subst (_≥ f 1) p (mf 0)
  ... | false | [ q ]ᵢ | _ = mz-lemma (mp f) (mf ∘ suc) q k


msuc : Mono → Mono
msuc m .fst = ms (fst m)
msuc m .snd = msm (snd m)

mpred : Mono → Mono
mpred f .fst k = f .fst (suc k)
mpred f .snd k = f .snd (suc k)

data MView (m : ℕ → Bool) : Type where
  mzv : mz ≡ m → MView m
  msv : ∀ n → ms n ≡ m → MView m

mview : ∀ f → isMono f → MView f
mview f mf with f 0 | inspect f 0
... |  true | [ p ]ᵢ = msv (mp f) (ms-mp f p)
... | false | [ p ]ᵢ = mzv λ i k → mz-lemma f mf p k i

∞ : Mono
∞ .fst _ = true
∞ .snd _ = _

Detached : (ℕ → Bool) → Type
Detached p = Σ[ n ∈ ℕ ] Bool→Type (p n)

Lower : Mono → Type
Lower m = Detached (fst m)

Detached-ext
  : ∀{p : ℕ → Bool} (k l : Detached p) → k .fst ≡ l .fst → k ≡ l
Detached-ext {p} (k , q) (l , r) s
  = ΣPathP (s , isPropDep∘ p isPropDep-Bool→Type q r s)

Lower∞≃ℕ : Lower ∞ ≃ ℕ
Lower∞≃ℕ = isoToEquiv λ where
    .fun → fst
    .inv n → n , _
    .rightInv _ → refl
    .leftInv _ → refl
  where open Iso

private
  apart : ℕ → ℕ → Type
  apart zero zero = ⊥
  apart (suc m) (suc n) = apart m n
  apart _ _ = Unit

  ≢→apart : (i j : ℕ) → ¬ i ≡ j → apart i j
  ≢→apart zero zero ¬p = ¬p refl
  ≢→apart (suc i) (suc j) ¬p = ≢→apart i j (¬p ∘ cong suc)
  ≢→apart zero (suc _) _ = _
  ≢→apart (suc _) zero _ = _

  apart→≢ : (i j : ℕ) → apart i j → ¬ i ≡ j
  apart→≢ (suc _) zero _ = snotz
  apart→≢ zero (suc _) _ = znots
  apart→≢ (suc i) (suc j) i#j = apart→≢ i j i#j ∘ cong predℕ

  apart-isProp : ∀ i j → isProp (apart i j)
  apart-isProp 0 0 = isProp⊥
  apart-isProp (suc i) (suc j) = apart-isProp i j
  apart-isProp 0 (suc _) = isPropUnit
  apart-isProp (suc _) 0 = isPropUnit

_#_ : ∀{P : ℕ → Type ℓ} → Σ ℕ P → Σ ℕ P → Type
u # v = apart (fst u) (fst v)

_#?_ : ∀{P : ℕ → Type ℓ} → (u v : Σ ℕ P) → (u # v) ⊎ (fst u ≡ fst v)
u #? v = decide (fst u) (fst v) where
  decide : (m n : ℕ) → apart m n ⊎ (m ≡ n)
  decide zero zero = inr refl
  decide zero (suc _) = inl _
  decide (suc _) zero = inl _
  decide (suc m) (suc n) = map (idfun _) (cong suc) (decide m n)

#→≢ : ∀{P : ℕ → Type ℓ} (u v : Σ ℕ P) → u # v → ¬ u ≡ v
#→≢ u v d = apart→≢ (fst u) (fst v) d ∘ cong fst

#-isProp : ∀{P : ℕ → Type ℓ} (u v : Σ ℕ P) → isProp (u # v)
#-isProp u v = apart-isProp (fst u) (fst v)

#-isPropDepᵣ : ∀{P : ℕ → Type ℓ} (v : Σ ℕ P) → isPropDep (λ u → u # v)
#-isPropDepᵣ v = isOfHLevel→isOfHLevelDep 1 (λ u → #-isProp u v) {_} {_}

≢→# : ∀{p} (u v : Detached p) → ¬ u ≡ v → u # v
≢→# u v ¬p = ≢→apart (fst u) (fst v) (¬p ∘ Detached-ext u v)

dzero : ∀{f} → Detached (ms f)
dzero = zero , _

dsuc : ∀{f} → Detached f → Detached (ms f)
dsuc (l , p) = suc l , p

module Untangle
    {α β}
    (f : Detached (ms α) → Detached (ms β))
    (g : Detached (ms β) → Detached (ms α))
    (rinv : section f g)
    (linv : retract f g)
  where

  default : ∀{γ} → (v d : Detached (ms γ)) → v # d → Detached γ
  default (suc l , p) _ _ = l , p
  default (0 , _) (suc l , p) _ = l , p

  #-f : ∀ u v → u # v → f u # f v
  #-f u v u#v with f u #? f v
  ... | inl fu#fv = fu#fv
  ... | inr fu≡fv = Empty.rec (#→≢ u v u#v u≡v)
    where
    u≡v : u ≡ v
    u≡v = sym (linv u)
       ∙∙ cong g (Detached-ext (f u) (f v) fu≡fv)
       ∙∙ linv v

  #-g : ∀ u v → u # v → g u # g v
  #-g u v u#v with g u #? g v
  ... | inl gu#gv = gu#gv
  ... | inr gu≡gv = Empty.rec (#→≢ u v u#v u≡v)
    where
    u≡v : u ≡ v
    u≡v = sym (rinv u)
       ∙∙ cong f (Detached-ext (g u) (g v) gu≡gv)
       ∙∙ rinv v

  f- : Detached α → Detached β
  f- v = default (f (dsuc v)) (f dzero) (#-f (dsuc v) dzero _)

  g- : Detached β → Detached α
  g- v = default (g (dsuc v)) (g dzero) (#-g (dsuc v) dzero _)

  g-f-z : ∀ v u → g dzero ≡ dsuc v → g (dsuc u) ≡ dzero → g- u ≡ v
  g-f-z v u r s with g (dsuc u) | g dzero | #-g (dsuc u) dzero _
  ... | zero , _ | suc k , q | #gf
    = Detached-ext (k , q) v (cong (predℕ ∘ fst) r)
  ... | w@(suc k , _) | _ | #gf = Empty.rec (snotz (cong fst s))

  g-f-s : ∀ v u → g (dsuc u) ≡ dsuc v → g- u ≡ v
  g-f-s v u r with g (dsuc u) | #-g (dsuc u) dzero _
  ... | suc k , q | #gf = Detached-ext (k , q) v (cong (predℕ ∘ fst) r)
  ... |  zero , _ | #gf = Empty.rec (znots (cong fst r))

  g-f- : ∀(v : Detached α) → g- (f- v) ≡ v
  g-f- v with f (dsuc v) | linv (dsuc v) | #-f (dsuc v) dzero _
  g-f- v | suc j , p | r | #f = g-f-s v (j , p) r
  ... | zero , _ | r | #f with f dzero | linv dzero
  ... | suc j , p | s = g-f-z v (j , p) r s

  f-g-z : ∀ v u → f dzero ≡ dsuc v → f (dsuc u) ≡ dzero → f- u ≡ v
  f-g-z v u r s with f (dsuc u) | f dzero | #-f (dsuc u) dzero _
  ... | zero , _ | suc k , q | #fg
    = Detached-ext (k , q) v (cong (predℕ ∘ fst) r)
  ... | (suc _ , _) | _ | _ = Empty.rec (snotz (cong fst s))

  f-g-s : ∀ v u → f (dsuc u) ≡ dsuc v → f- u ≡ v
  f-g-s v u r with f (dsuc u) | #-f (dsuc u) dzero _
  ... | suc k , q | _ = Detached-ext (k , q) v (cong (predℕ ∘ fst) r)
  ... |  zero , _ | _ = Empty.rec (znots (cong fst r))

  f-g- : ∀ v → f- (g- v) ≡ v
  f-g- v with g (dsuc v) | rinv (dsuc v) | #-g (dsuc v) dzero _
  ... | suc j , q | r | _ = f-g-s v (j , q) r
  ... | zero , _ | r | _ with g dzero | rinv dzero
  ... | suc k , q | s = f-g-z v (k , q) r s

  open Iso
  iso- : Iso (Detached α) (Detached β)
  iso- .fun = f-
  iso- .inv = g-
  iso- .rightInv = f-g-
  iso- .leftInv = g-f-

iso-pred
  : ∀{α β}
  → Iso (Detached (ms α)) (Detached (ms β))
  → Iso (Detached α) (Detached β)
iso-pred i = Untangle.iso- fun inv rightInv leftInv
  where open Iso i

Lower-lemma
  : ∀ α β → isMono α → isMono β
  → Iso (Detached α) (Detached β)
  → α ≡ β
Lower-lemma α β mα mβ I i k with mview α mα | mview β mβ
... | mzv p | mzv q = transport (λ i → p i k ≡ q i k) refl i
Lower-lemma α β mα mβ I i 0 | msv _ p | msv _ q
  = transport (λ i → p i 0 ≡ q i 0) refl i
Lower-lemma α β mα mβ I i (suc k) | msv α' p | msv β' q
  = hcomp (λ τ → λ where
        (i = i0) → p τ (suc k)
        (i = i1) → q τ (suc k))
      (ind i k)
  where
  I' : Iso (Detached (ms α')) (Detached (ms β'))
  I' = transport (λ i → Iso (Detached (p (~ i))) (Detached (q (~ i)))) I

  mα' : isMono α'
  mα' k = subst⁻ isMono p mα (suc k)
  mβ' : isMono β'
  mβ' k = subst⁻ isMono q mβ (suc k)

  ind : α' ≡ β'
  ind = Lower-lemma α' β' mα' mβ' (iso-pred I')
  {-# INLINE ind #-}

Lower-lemma α β mα mβ I i k | mzv p | msv β' q
  = Empty.rec {A = α k ≡ β k} (subst⁻ Detached p (Iso.inv I v) .snd) i
  where
  v : Detached β
  v = subst Detached q dzero
Lower-lemma α β mα mβ I i k | msv _ p | mzv q
  = Empty.rec {A = α k ≡ β k} (subst⁻ Detached q (Iso.fun I v) .snd) i
  where
  v : Detached α
  v = subst Detached p dzero

Lower-inj : Lower m ≡ Lower n → m ≡ n
Lower-inj {m} {n} P
  = curry ΣPathP
      (Lower-lemma (m .fst) (n .fst) (m .snd) (n .snd) (pathToIso P))
      (isMonoIsPropDep (m .snd) (n .snd) _)

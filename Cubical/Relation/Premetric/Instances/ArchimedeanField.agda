module Cubical.Relation.Premetric.Instances.ArchimedeanField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Transport

open import Cubical.Algebra.ArchimedeanField

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals.Positive

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver

open PremetricStr

private
  variable
    ℓA ℓA' : Level

module AFSpace (A : ArchimedeanField ℓA ℓA') where
  private open module A = ArchimedeanFieldStr (snd A)

  open ArchimedeanFieldTheory A
  open ArchimedeanFieldReasoning A
  open IsPremetric

  infix 5 _≈ᴬ[_]_

  _≈ᴬ[_]_ : ⟨ A ⟩ → ℚ₊ → ⟨ A ⟩ → Type ℓA'
  x ≈ᴬ[ ε ] y = abs (x - y) < ι₊ ε

  isPremetricᴬ : IsPremetric _≈ᴬ[_]_
  isPremetricᴬ .is-set        = A.is-set
  isPremetricᴬ .isProp≈       = λ x y ε → is-prop-valued< (abs (x - y)) (ι₊ ε)
  isPremetricᴬ .isRefl≈       = λ x ε →
    subst (_< _) (sym (cong abs (+InvR x) ∙ abs0)) $ 0<ι₊ ε
  isPremetricᴬ .isSym≈        = λ x y ε → subst (_< _) $ abs-Comm x y
  isPremetricᴬ .isSeparated≈  = λ x y x≈y →
    equalByDifference x y $
    abs≤0→≡0 (x - y) $
    ¬<→≥ 0f (abs(x - y)) $
    PT.rec isProp⊥
      (λ (q , 0<ιq , ιq<∣x-y∣) → is-asym _ _ ιq<∣x-y∣ (x≈y (q , 0<ι→0< q 0<ιq)))
    ∘ isArchimedeanWithι 0f (abs(x - y))
  isPremetricᴬ .isTriangular≈ = λ x y z ε δ <ε <δ → begin<
    abs (x - z)                 ≤⟨ triangularInequality- x z y ⟩
    abs (x - y) + abs (y - z)   <⟨ +Mono< _ _ _ _ <ε <δ ⟩
    ι₊ ε + ι₊ δ               ≡→≤⟨ sym $ ιpres+ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
    ι₊ (ε +₊ δ)                 ◾
  isPremetricᴬ .isRounded≈    = λ x y ε x≈y → do
    (q , ∣x-y∣<ιq , ιq<ιε) ← isArchimedeanWithι (abs (x - y)) (ι₊ ε) x≈y
    return
      ((_ , 0<ι→0< q (≤-<-trans _ _ _ (0≤abs _) ∣x-y∣<ιq))
      , ιreflect< q ⟨ ε ⟩₊ ιq<ιε
      , ∣x-y∣<ιq)

  ArchimedeanField→PremetricSpace : PremetricSpace ℓA ℓA'
  fst ArchimedeanField→PremetricSpace               = fst A
  _≈[_]_ (snd ArchimedeanField→PremetricSpace)      = _≈ᴬ[_]_
  isPremetric (snd ArchimedeanField→PremetricSpace) = isPremetricᴬ

module AFSpaceProperties (A : ArchimedeanField ℓA ℓA') where
  private ACR = ArchimedeanField→CommRing A

  open ArchimedeanFieldStr (snd A)
  open ArchimedeanFieldTheory A
  open AFSpace A renaming (ArchimedeanField→PremetricSpace to APrSpace)

  open IsIsometry

  [_]+ᴵ : ⟨ A ⟩ → Isometry[ APrSpace , APrSpace ]
  fst [ z ]+ᴵ         = z +_
  pres≈ (snd [ z ]+ᴵ) = λ _ ε _ → substEquiv (_< ι₊ ε) $ cong abs $ solve! ACR

  +ᴵ[_] : ⟨ A ⟩ → Isometry[ APrSpace , APrSpace ]
  fst +ᴵ[ z ]         = _+ z
  pres≈ (snd +ᴵ[ z ]) = λ _ ε _ → substEquiv (_< ι₊ ε) $ cong abs $ solve! ACR

  [_]+ⁿ : ⟨ A ⟩ → NE[ APrSpace , APrSpace ]
  [_]+ⁿ = Isometry→NE ∘ [_]+ᴵ

  +ⁿ[_] : ⟨ A ⟩ → NE[ APrSpace , APrSpace ]
  +ⁿ[_] = Isometry→NE ∘ +ᴵ[_]

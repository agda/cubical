module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto hiding (id)
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Premetric

private
  variable
    ℓ ℓ' ℓM ℓM' ℓN ℓN' ℓO ℓO' : Level

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A)
  (f : A → B)
  (N : PremetricStr ℓN' B)
  where

  private
    module M where
      open PremetricStr M public
      open PremetricTheory (_ , M) public
    module N where
      open PremetricStr N public
      open PremetricTheory (_ , N) public

  record IsContinuousAt (x : A) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor iscontinuousat
    field
      pres≈ : ∀ ε → ∃[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → f x N.≈[ ε ] f y)

  unquoteDecl IsContinuousAtIsoΣ = declareRecordIsoΣ IsContinuousAtIsoΣ (quote IsContinuousAt)

  isPropIsContinuousAt : ∀ x → isProp (IsContinuousAt x)
  isPropIsContinuousAt x = isOfHLevelRetractFromIso 1
    IsContinuousAtIsoΣ $ isPropΠ λ _ → squash₁

  isContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuous = ∀ x → IsContinuousAt x

  isPropIsContinuous : isProp isContinuous
  isPropIsContinuous = isPropΠ isPropIsContinuousAt

  record IsSeqContinuousAt (l : A) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isseqcontinuousat
    field
      presLim : ∀ x → M.isLimitSeq x l → N.isLimitSeq (f ∘ x) (f l)

  unquoteDecl IsSeqContinuousAtIsoΣ = declareRecordIsoΣ IsSeqContinuousAtIsoΣ (quote IsSeqContinuousAt)

  isPropIsSeqContinuousAt : ∀ l → isProp (IsSeqContinuousAt l)
  isPropIsSeqContinuousAt l = isOfHLevelRetractFromIso 1
    IsSeqContinuousAtIsoΣ $ isPropΠ2 λ x _ → N.isPropIsLimitSeq (f ∘ x) (f l)

  isSeqContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isSeqContinuous = ∀ l → IsSeqContinuousAt l

  isPropIsSeqContinuous : isProp isSeqContinuous
  isPropIsSeqContinuous = isPropΠ isPropIsSeqContinuousAt

  record IsUContinuousWith (μ : ℚ₊ → ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isucontinuouswith
    field
      pres≈ : ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsUContinuousWithIsoΣ = declareRecordIsoΣ IsUContinuousWithIsoΣ (quote IsUContinuousWith)

  isPropIsUContinuousWith : ∀ μ → isProp (IsUContinuousWith μ)
  isPropIsUContinuousWith μ = isOfHLevelRetractFromIso 1
    IsUContinuousWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  record IsUContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isucontinuous
    field
      pres≈ : ∀ ε → ∃[ μ ∈ ℚ₊ ] (∀ x y → x M.≈[ μ ] y → f x N.≈[ ε ] f y)

  unquoteDecl IsUContinuousIsoΣ = declareRecordIsoΣ IsUContinuousIsoΣ (quote IsUContinuous)

  isPropIsUContinuous : isProp IsUContinuous
  isPropIsUContinuous = isOfHLevelRetractFromIso 1
    IsUContinuousIsoΣ (isPropΠ λ _ → squash₁)

  ∥ΣIsUContinuous∥₁→isUContinuous : ∥ Σ _ IsUContinuousWith ∥₁ → IsUContinuous
  IsUContinuous.pres≈ (∥ΣIsUContinuous∥₁→isUContinuous is-uc) ε = do
    (μ , μ-uc) ← is-uc
    return (μ ε , λ x y → μ-uc .IsUContinuousWith.pres≈ x y ε)

  record IsLipschitzWith (L : ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor islipschitzwith
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  unquoteDecl IsLipschitzWithIsoΣ = declareRecordIsoΣ IsLipschitzWithIsoΣ (quote IsLipschitzWith)

  isPropIsLipschitzWith : ∀ L → isProp (IsLipschitzWith L)
  isPropIsLipschitzWith L = isOfHLevelRetractFromIso 1
    IsLipschitzWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitz : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitz = ∃[ L ∈ ℚ₊ ] IsLipschitzWith L

  isPropIsLipschitz : isProp isLipschitz
  isPropIsLipschitz = squash₁

  record IsNonExpansive : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isnonexpansive
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsNonExpansiveIsoΣ = declareRecordIsoΣ IsNonExpansiveIsoΣ (quote IsNonExpansive)

  isPropIsNonExpansive : isProp IsNonExpansive
  isPropIsNonExpansive = isOfHLevelRetractFromIso 1 IsNonExpansiveIsoΣ $
    isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  -- NonExpansive mappings are equivalent to Lipschitz mappings with constant 1:

  isNonExpansive→isLipschitzWith1 : IsNonExpansive → IsLipschitzWith 1
  IsLipschitzWith.pres≈ (isNonExpansive→isLipschitzWith1 is-ne) x y ε =
    N.subst≈ (f x) (f y) (sym (ℚ.·IdL ⟨ ε ⟩₊)) ∘ is-ne .IsNonExpansive.pres≈ x y ε

  isLipschitzWith1→isNonExpansive : IsLipschitzWith 1 → IsNonExpansive
  IsNonExpansive.pres≈ (isLipschitzWith1→isNonExpansive 1-lip) x y ε =
    N.subst≈ (f x) (f y) (ℚ.·IdL ⟨ ε ⟩₊) ∘ 1-lip .IsLipschitzWith.pres≈ x y ε

  IsNonExpansive≃IsLipschitzWith1 : IsNonExpansive ≃ IsLipschitzWith 1
  IsNonExpansive≃IsLipschitzWith1 = propBiimpl→Equiv
    isPropIsNonExpansive (isPropIsLipschitzWith 1)
    isNonExpansive→isLipschitzWith1 isLipschitzWith1→isNonExpansive

  record IsIsometry : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isisometry
    field
      pres≈ : ∀ x ε y → x M.≈[ ε ] y ≃ f x N.≈[ ε ] f y

  unquoteDecl IsIsometryIsoΣ = declareRecordIsoΣ IsIsometryIsoΣ (quote IsIsometry)

  isPropIsIsometry : isProp IsIsometry
  isPropIsIsometry = isOfHLevelRetractFromIso 1 IsIsometryIsoΣ $
    isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (M.isProp≈ _ _ _) (N.isProp≈ _ _ _)

  -- Here below we prove the implications
  -- Isometry ⇒ NonExpansive ⇒ Lipschitz ⇒ UContinuous ⇒ Continuous ⇒ SeqContinuous :

  isIsometry→isNonExpansive : IsIsometry → IsNonExpansive
  IsNonExpansive.pres≈ (isIsometry→isNonExpansive is-iso) =
    λ x y ε → equivFun (IsIsometry.pres≈ is-iso x ε y)

  isNonExpansive→isLipschitz : IsNonExpansive → isLipschitz
  isNonExpansive→isLipschitz is-ne = ∣ 1 , isNonExpansive→isLipschitzWith1 is-ne ∣₁

  isLipschitzWith→isUContinuousWith/ :
    ∀ L → IsLipschitzWith L → IsUContinuousWith (_₊/₊ L)
  IsUContinuousWith.pres≈ (isLipschitzWith→isUContinuousWith/ L L-lip) x y ε =
    N.subst≈ (f x) (f y) (·₊/₊ ε L) ∘ L-lip .IsLipschitzWith.pres≈ x y (ε ₊/₊ L)

  isLipschitz→isUContinuous : isLipschitz → IsUContinuous
  isLipschitz→isUContinuous = PT.rec isPropIsUContinuous $
    ∥ΣIsUContinuous∥₁→isUContinuous ∘ ∣_∣₁ ∘ uncurry λ L L-lip →
      (_₊/₊ L , isLipschitzWith→isUContinuousWith/ L L-lip)

  isUContinuousWith→isContinuous : ∀ μ → IsUContinuousWith μ → isContinuous
  IsContinuousAt.pres≈ (isUContinuousWith→isContinuous μ μ-uc x) ε =
    return (μ ε , λ y → μ-uc .IsUContinuousWith.pres≈ x y ε)

  isUContinuous→isContinuous : IsUContinuous → isContinuous
  IsContinuousAt.pres≈ (isUContinuous→isContinuous is-uc x) ε = do
    (δ , ≈δ→f≈ε) ← is-uc .IsUContinuous.pres≈ ε
    return (δ , ≈δ→f≈ε x)

  isContinuous→isSeqContinuous : isContinuous → isSeqContinuous
  isContinuous→isSeqContinuous is-c l .IsSeqContinuousAt.presLim x l-lim ε = do
    (δ , l≈→fl≈) ← IsContinuousAt.pres≈ (is-c l) ε
    (N , N≤→≈l ) ← l-lim δ
    return (N , λ n → N.isSym≈ _ _ _ ∘ (l≈→fl≈ (x n)) ∘ M.isSym≈ _ _ _ ∘ (N≤→≈l n))

  -- UContinuous ⇒ SeqContinuous

  isUContinuous→IsSeqContinuous : IsUContinuous → isSeqContinuous
  isUContinuous→IsSeqContinuous =
    isContinuous→isSeqContinuous ∘ isUContinuous→isContinuous

  -- Lipschitz ⇒ Continuous, SeqContinuous

  isLipschitz→isContinuous : isLipschitz → isContinuous
  isLipschitz→isContinuous = isUContinuous→isContinuous ∘ isLipschitz→isUContinuous

  isLipschitz→isSeqContinuous : isLipschitz → isSeqContinuous
  isLipschitz→isSeqContinuous = isContinuous→isSeqContinuous ∘ isLipschitz→isContinuous

  -- Nonexpansive ⇒ UContinuous, Continuous, SeqContinuous

  -- we prove this two implications directly, instead of passing through
  -- `isNonExpansive→isLipschitz` to avoid a " / 1" in the definition of μ
  isNonExpansive→isUContinuousWithId : IsNonExpansive → IsUContinuousWith (idfun ℚ₊)
  IsUContinuousWith.pres≈ (isNonExpansive→isUContinuousWithId is-ne) =
    IsNonExpansive.pres≈ is-ne

  isNonExpansive→isUContinuous : IsNonExpansive → IsUContinuous
  isNonExpansive→isUContinuous =
    curry (∥ΣIsUContinuous∥₁→isUContinuous ∘ ∣_∣₁) _ ∘ isNonExpansive→isUContinuousWithId

  isNonExpansive→isContinuous : IsNonExpansive → isContinuous
  isNonExpansive→isContinuous = isUContinuous→isContinuous ∘ isNonExpansive→isUContinuous

  isNonExpansive→isSeqContinuous : IsNonExpansive → isSeqContinuous
  isNonExpansive→isSeqContinuous =
    isContinuous→isSeqContinuous ∘ isNonExpansive→isContinuous

  -- Isometry ⇒ Lipschitz, UContinuous, Continuous, SeqContinuous

  isIsometry→isLipschitz : IsIsometry → isLipschitz
  isIsometry→isLipschitz = isNonExpansive→isLipschitz ∘ isIsometry→isNonExpansive

  isIsometry→isUContinuous : IsIsometry → IsUContinuous
  isIsometry→isUContinuous = isNonExpansive→isUContinuous ∘ isIsometry→isNonExpansive

  isIsometry→isContinuous : IsIsometry → isContinuous
  isIsometry→isContinuous = isUContinuous→isContinuous ∘ isIsometry→isUContinuous

  isIsometry→isSeqContinuous : IsIsometry → isSeqContinuous
  isIsometry→isSeqContinuous = isContinuous→isSeqContinuous ∘ isIsometry→isContinuous

C[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
C[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isContinuous (M .snd) f (N .snd)

UC[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
UC[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsUContinuous (M .snd) f (N .snd)

L[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
L[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isLipschitz (M .snd) f (N .snd)

NE[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
NE[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsNonExpansive (M .snd) f (N .snd)

Isometry[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
Isometry[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsIsometry (M .snd) f (N .snd)

module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} where
  private
    module M where
      open PremetricStr (snd M) public
      open PremetricTheory M    public
    module N where
      open PremetricStr (snd N) public
      open PremetricTheory N    public

  C≡ : {f g : C[ M , N ]} → fst f ≡ fst g → f ≡ g
  C≡ = ΣPathPProp (flip (isPropIsContinuous _) _)

  UC≡ : {f g : UC[ M , N ]} → fst f ≡ fst g → f ≡ g
  UC≡ = ΣPathPProp (flip (isPropIsUContinuous _) _)

  L≡ : {f g : L[ M , N ]} → fst f ≡ fst g → f ≡ g
  L≡ = ΣPathPProp λ _ → squash₁

  NE≡ : {f g : NE[ M , N ]} → fst f ≡ fst g → f ≡ g
  NE≡ = ΣPathPProp (flip (isPropIsNonExpansive _) _)

  Isometry≡ : {f g : Isometry[ M , N ]} → fst f ≡ fst g → f ≡ g
  Isometry≡ = ΣPathPProp (flip (isPropIsIsometry _) _)

  Isometry→NE : Isometry[ M , N ] → NE[ M , N ]
  fst (Isometry→NE f) = fst f
  snd (Isometry→NE f) = isIsometry→isNonExpansive _ (fst f) _ (snd f)

  NE→L : NE[ M , N ] → L[ M , N ]
  fst (NE→L f) = fst f
  snd (NE→L f) = isNonExpansive→isLipschitz _ (fst f) _ (snd f)

  NE→UC : NE[ M , N ] → UC[ M , N ]
  fst (NE→UC f) = fst f
  snd (NE→UC f) = isNonExpansive→isUContinuous _ (fst f) _ (snd f)

  L→UC : L[ M , N ] → UC[ M , N ]
  fst (L→UC f) = fst f
  snd (L→UC f) = isLipschitz→isUContinuous _ (fst f) _ (snd f)

  UC→C : UC[ M , N ] → C[ M , N ]
  fst (UC→C f) = fst f
  snd (UC→C f) = isUContinuous→isContinuous _ (fst f) _ (snd f)

  L→C : L[ M , N ] → C[ M , N ]
  L→C = UC→C ∘ L→UC

  NE→C : NE[ M , N ] → C[ M , N ]
  NE→C = UC→C ∘ NE→UC

  Isometry→L : Isometry[ M , N ] → L[ M , N ]
  Isometry→L = NE→L ∘ Isometry→NE

  Isometry→UC : Isometry[ M , N ] → UC[ M , N ]
  Isometry→UC = NE→UC ∘ Isometry→NE

  Isometry→C : Isometry[ M , N ] → C[ M , N ]
  Isometry→C = NE→C ∘ Isometry→NE

  presLimNE : (f : NE[ M , N ])
            → ∀ x l → M.isLimit x l → N.isLimit (fst f ∘ x) (fst f l)
  presLimNE f x l l-lim ε θ = IsNonExpansive.pres≈ (snd f) (x ε) l (ε +₊ θ) (l-lim ε θ)

  presLimIsometry : (f : Isometry[ M , N ])
                  → ∀ x l → M.isLimit x l → N.isLimit (fst f ∘ x) (fst f l)
  presLimIsometry f x l = presLimNE (Isometry→NE f) x l

-- The identity function is Isometric, NonExpansive, Continuous, UContinuous, Lipschitz:
module _ {M : PremetricSpace ℓM ℓM'} where

  idᴵ : Isometry[ M , M ]
  fst idᴵ = idfun _
  IsIsometry.pres≈ (snd idᴵ) = λ _ _ _ → idEquiv _

  idⁿ : NE[ M , M ]
  fst idⁿ = idfun _
  IsNonExpansive.pres≈ (snd idⁿ) = λ _ _ _ → idfun _

  idᶜ : C[ M , M ]
  fst idᶜ = idfun _
  snd idᶜ = isNonExpansive→isContinuous _ _ _ (idⁿ .snd)

  idᵘᶜ : UC[ M , M ]
  fst idᵘᶜ = idfun _
  snd idᵘᶜ = isNonExpansive→isUContinuous _ _ _ (idⁿ .snd)

  idᴸ : L[ M , M ]
  fst idᴸ = idfun _
  snd idᴸ = isNonExpansive→isLipschitz _ _ _ (idⁿ .snd)

-- Composiontions of mappings:
module _
  {M : PremetricSpace ℓM ℓM'}
  {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} where

  _∘Isometry_ : Isometry[ N , O ] → Isometry[ M , N ] → Isometry[ M , O ]
  fst (g ∘Isometry f) = fst g ∘ fst f
  IsIsometry.pres≈ (snd (g ∘Isometry f)) =
    λ x ε y → f .snd .pres≈ x ε y ∙ₑ g .snd .pres≈ (fst f x) ε (fst f y)
    where open IsIsometry

  _∘NE_ : NE[ N , O ] → NE[ M , N ] → NE[ M , O ]
  fst (g ∘NE f) = fst g ∘ fst f
  IsNonExpansive.pres≈ (snd (g ∘NE f)) =
    λ x y ε → g .snd .pres≈ (fst f x) (fst f y) ε ∘ f .snd .pres≈ x y ε
    where open IsNonExpansive

  _∘C_ : C[ N , O ] → C[ M , N ] → C[ M , O ]
  fst (g ∘C f) = fst g ∘ fst f
  IsContinuousAt.pres≈ (snd (g ∘C f) x) = λ ε → do
    (δ , ≈δ→≈ε) ← g .snd (fst f x) .pres≈ ε
    (η , ≈η→≈δ) ← f .snd x .pres≈ δ
    return (η , λ y → ≈δ→≈ε (fst f y) ∘ ≈η→≈δ y)
    where open IsContinuousAt

  _∘UC_ : UC[ N , O ] → UC[ M , N ] → UC[ M , O ]
  fst (g ∘UC f) = fst g ∘ fst f
  IsUContinuous.pres≈ (snd (g ∘UC f)) ε = do
    (ν , ν-uc) ← g .snd .pres≈ ε
    (μ , μ-uc) ← f .snd .pres≈ ν
    return (μ , λ x y → ν-uc (fst f x) (fst f y) ∘ μ-uc x y)
    where open IsUContinuous

  _∘L_ : L[ N , O ] → L[ M , N ] → L[ M , O ]
  fst (g ∘L f) = fst g ∘ fst f
  snd (g ∘L f) = do
    (L , L-lip) ← f .snd
    (R , R-lip) ← g .snd
    return λ where
      .fst → R ·₊ L
      .snd .pres≈ x y ε →
        subst≈ (fst g (fst f x)) (fst g (fst f y)) (ℚ.·Assoc ⟨ R ⟩₊ ⟨ L ⟩₊ _)
        ∘ R-lip .pres≈ (fst f x) (fst f y) (L ·₊ ε)
        ∘ L-lip .pres≈ x y ε
    where
      open IsLipschitzWith
      open PremetricTheory O

-- Isometric equivalences
record IsIsometric≃ {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
  where
  no-eta-equality
  constructor isisometricequiv
  -- Shorter qualified names
  private
    module M = PremetricStr M
    module N = PremetricStr N

  field
    pres≈ : ∀ x ε y → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y

unquoteDecl IsIsometric≃IsoΣ = declareRecordIsoΣ IsIsometric≃IsoΣ (quote IsIsometric≃)

Isometric≃[_,_] : (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') → Type _
Isometric≃[ M , N ] = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsIsometric≃ (M .snd) e (N .snd)

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B) where

  private
    module M = PremetricStr M
    module N = PremetricStr N

  open IsNonExpansive
  open IsIsometry
  open IsIsometric≃

  isPropIsIsometric≃ : isProp (IsIsometric≃ M e N)
  isPropIsIsometric≃ = isOfHLevelRetractFromIso 1 IsIsometric≃IsoΣ $
    isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (M.isProp≈ _ _ _) (N.isProp≈ _ _ _)

  isIsometry→isIsometric≃ : IsIsometry M (equivFun e) N → IsIsometric≃ M e N
  pres≈ (isIsometry→isIsometric≃ is-iso) = pres≈ is-iso

  isIsometric≃→isIsometry : IsIsometric≃ M e N → IsIsometry M (equivFun e) N
  pres≈ (isIsometric≃→isIsometry is-iso) = pres≈ is-iso

  isIsometry≃isIsometric≃ : IsIsometry M (equivFun e) N ≃ IsIsometric≃ M e N
  isIsometry≃isIsometric≃ = propBiimpl→Equiv (isPropIsIsometry _ _ _) isPropIsIsometric≃
    isIsometry→isIsometric≃ isIsometric≃→isIsometry

  isIsometryInvEq : IsIsometry M (equivFun e) N → IsIsometry N (invEq e) M
  pres≈ (isIsometryInvEq ise) x ε y = invEquiv $
       pres≈ ise (invEq e x) ε (invEq e y)
    ∙ₑ pathToEquiv (cong₂ N._≈[ ε ]_ (secEq e x) (secEq e y))

  isIsometric≃InvEq : IsIsometric≃ M e N → IsIsometric≃ N (invEquiv e) M
  pres≈ (isIsometric≃InvEq is-iso) =
    pres≈ $ isIsometryInvEq $ isIsometric≃→isIsometry is-iso

module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} where

  Isometric≃≡ : {f g : Isometric≃[ M , N ]} → fst f ≡ fst g → f ≡ g
  Isometric≃≡ = ΣPathPProp (flip (isPropIsIsometric≃ _) _)

  invIsometric≃ : Isometric≃[ M , N ] → Isometric≃[ N , M ]
  fst (invIsometric≃ f) = invEquiv (fst f)
  snd (invIsometric≃ f) = isIsometric≃InvEq _ (fst f) _ (snd f)

  Isometric≃→Isometry : Isometric≃[ M , N ] → Isometry[ M , N ]
  fst (Isometric≃→Isometry e) = equivFun (fst e)
  snd (Isometric≃→Isometry e) = isIsometric≃→isIsometry _ (fst e) _ (snd e)

  Isometric≃→NE : Isometric≃[ M , N ] → NE[ M , N ]
  Isometric≃→NE = Isometry→NE ∘ Isometric≃→Isometry

  Isometric≃→L : Isometric≃[ M , N ] → L[ M , N ]
  Isometric≃→L = NE→L ∘ Isometric≃→NE

  Isometric≃→UC : Isometric≃[ M , N ] → UC[ M , N ]
  Isometric≃→UC = NE→UC ∘ Isometric≃→NE

  Isometric≃→C : Isometric≃[ M , N ] → C[ M , N ]
  Isometric≃→C = NE→C ∘ Isometric≃→NE

𝒮ᴰ-Premetric : ∀ {ℓ ℓ'} → DUARel (𝒮-Univ ℓ) (PremetricStr ℓ') (ℓ-suc (ℓ-max ℓ ℓ'))
𝒮ᴰ-Premetric =
  𝒮ᴰ-Record (𝒮-Univ _) IsIsometric≃
    (fields:
      data[ _≈[_]_ ∣ ternRel ∣ pres≈ ]
      prop[ isPremetric ∣ (λ _ _ → isPropIsPremetric _) ])
  where
  open PremetricStr
  open IsIsometric≃

  ternRel = autoDUARel (𝒮-Univ _) (λ A → A → ℚ₊ → A → Type _)

PremetricSIP : ∀ {ℓ ℓ'} (M N : PremetricSpace ℓ ℓ') → Isometric≃[ M , N ] ≃ (M ≡ N)
PremetricSIP = ∫ 𝒮ᴰ-Premetric .UARel.ua

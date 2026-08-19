module Cubical.Algebra.OrderedCommRing.Morphisms where
{-
  The notion of homomorphism/monomorphism of Ordered Commutative Rings is derived
  from homomorphisms of Ordered Heyting Fields, following definition 4.3.1 of
  Analysis in univalent type theory, A.B.Booij, PhD Thesis, 2020
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ<≤ ℓ<≤' : Level

record IsOrderedCommRingHom {A : Type ℓ} {B : Type ℓ'}
  (R : OrderedCommRingStr ℓ<≤ A)
  (f : A → B)
  (S : OrderedCommRingStr ℓ<≤' B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤')))
  where
  no-eta-equality
  private
    module R = OrderedCommRingStr R
    module S = OrderedCommRingStr S
    Rcring = str (OrderedCommRing→CommRing (_ , R))
    Scring = str (OrderedCommRing→CommRing (_ , S))

  field
    isCommRingHom : IsCommRingHom Rcring f Scring
    pres≤         : ∀ x y → x R.≤ y → f x S.≤ f y
    reflect<      : ∀ x y → f x S.< f y → x R.< y

  open IsCommRingHom isCommRingHom public

unquoteDecl IsOrderedCommRingHomIsoΣ = declareRecordIsoΣ IsOrderedCommRingHomIsoΣ (quote IsOrderedCommRingHom)

OrderedCommRingHom : OrderedCommRing ℓ ℓ<≤ → OrderedCommRing ℓ' ℓ<≤' → Type _
OrderedCommRingHom R S =
  Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsOrderedCommRingHom (R .snd) f (S .snd)

isPropIsOrderedCommRingHom : {A : Type ℓ} {B : Type ℓ'}
                           → (R : OrderedCommRingStr ℓ<≤ A)
                           → (f : A → B)
                           → (S : OrderedCommRingStr ℓ<≤' B)
                           → isProp (IsOrderedCommRingHom R f S)
isPropIsOrderedCommRingHom R f S = isOfHLevelRetractFromIso 1
  IsOrderedCommRingHomIsoΣ $
  isProp×2 (isPropIsCommRingHom _ f _)
           (isPropΠ2 λ _ _ → isProp→ (S.is-prop-valued≤ _ _))
           (isPropΠ2 λ _ _ → isProp→ (R.is-prop-valued< _ _))
  where
    open module R = OrderedCommRingStr R
    open module S = OrderedCommRingStr S

isSetOrderedCommRingHom : (R : OrderedCommRing ℓ ℓ<≤) (S : OrderedCommRing ℓ' ℓ<≤')
                        → isSet (OrderedCommRingHom R S)
isSetOrderedCommRingHom R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f →
  isPropIsOrderedCommRingHom (snd R) f (snd S))
    where open OrderedCommRingStr (str S) using (is-set)

module _
  {R : OrderedCommRing ℓ  ℓ<≤}
  {S : OrderedCommRing ℓ' ℓ<≤'}
  {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = OrderedCommRingStr (str R)
    module S = OrderedCommRingStr (str S)
    RCR = OrderedCommRing→CommRing R
    SCR = OrderedCommRing→CommRing S

  module _
    (p1  : f R.1r ≡ S.1r)
    (p+  : ∀ x y → f (x R.+ y) ≡ f x S.+ f y)
    (p·  : ∀ x y → f (x R.· y) ≡ f x S.· f y)
    (p<⁻ : ∀ x y → f x S.< f y → x R.< y)
    where

    open IsOrderedCommRingHom

    private
      p≤ : ∀ x y → x R.≤ y → f x S.≤ f y
      p≤ x y = invEq (S.≤≃¬> (f x) (f y)) ∘ (_∘ p<⁻ y x) ∘ equivFun (R.≤≃¬> x y)

    makeIsOrderedCommRingHom : IsOrderedCommRingHom (str R) f (str S)
    makeIsOrderedCommRingHom .isCommRingHom = makeIsCommRingHom p1 p+ p·
    makeIsOrderedCommRingHom .pres≤         = p≤
    makeIsOrderedCommRingHom .reflect<      = p<⁻

  module _ (isHomf : IsOrderedCommRingHom (str R) f (str S)) where

    isOrderedCommRingHom→IsCommRingHom : IsCommRingHom (str RCR) f (str SCR)
    isOrderedCommRingHom→IsCommRingHom = isCommRingHom
      where open IsOrderedCommRingHom isHomf

OrderedCommRingHom→CommRingHom : {A : OrderedCommRing ℓ  ℓ<≤}
                               → {B : OrderedCommRing ℓ' ℓ<≤'}
                               → OrderedCommRingHom A B
                               → CommRingHom
                                  (OrderedCommRing→CommRing A)
                                  (OrderedCommRing→CommRing B)
fst (OrderedCommRingHom→CommRingHom f) = fst f
snd (OrderedCommRingHom→CommRingHom f) = isOrderedCommRingHom→IsCommRingHom (snd f)

_$ocr_ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
       → (φ : OrderedCommRingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $ocr x = φ .fst x

opaque
  OrderedCommRingHom≡ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
                      → {φ ψ : OrderedCommRingHom R S}
                      → fst φ ≡ fst ψ
                      → φ ≡ ψ
  OrderedCommRingHom≡ = Σ≡Prop λ f → isPropIsOrderedCommRingHom _ f _

  OrderedCommRingHomPathP : (R : OrderedCommRing ℓ ℓ<≤) (S T : OrderedCommRing ℓ' ℓ<≤')
                          → (p : S ≡ T)
                          → (φ : OrderedCommRingHom R S)
                          → (ψ : OrderedCommRingHom R T)
                          → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
                          → PathP (λ i → OrderedCommRingHom R (p i)) φ ψ
  OrderedCommRingHomPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ →
    isPropIsOrderedCommRingHom _ _ _) _ _)

record IsOrderedCommRingMono {A : Type ℓ} {B : Type ℓ'}
  (R : OrderedCommRingStr ℓ<≤ A)
  (f : A → B)
  (S : OrderedCommRingStr ℓ<≤' B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤')))
  where
  no-eta-equality
  private
    module R = OrderedCommRingStr R
    module S = OrderedCommRingStr S

  field
    isOrderedCommRingHom : IsOrderedCommRingHom R f S
    pres<                : (x y : A) → x R.< y → f x S.< f y

  open IsOrderedCommRingHom isOrderedCommRingHom public

unquoteDecl IsOrderedCommRingMonoIsoΣ = declareRecordIsoΣ IsOrderedCommRingMonoIsoΣ (quote IsOrderedCommRingMono)

OrderedCommRingMono : OrderedCommRing ℓ ℓ<≤ → OrderedCommRing ℓ' ℓ<≤' → Type _
OrderedCommRingMono R S =
  Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsOrderedCommRingMono (R .snd) f (S .snd)

OrderedCommRingMono→OrderedCommRingHom : {A : OrderedCommRing ℓ  ℓ<≤}
                                       → {B : OrderedCommRing ℓ' ℓ<≤'}
                                       → OrderedCommRingMono A B
                                       → OrderedCommRingHom A B
fst (OrderedCommRingMono→OrderedCommRingHom f) = fst f
snd (OrderedCommRingMono→OrderedCommRingHom f) = isOrderedCommRingHom
  where open IsOrderedCommRingMono (snd f)

OrderedCommRingMono→CommRingHom : {A : OrderedCommRing ℓ  ℓ<≤}
                                → {B : OrderedCommRing ℓ' ℓ<≤'}
                                → OrderedCommRingMono A B
                                → CommRingHom
                                   (OrderedCommRing→CommRing A)
                                   (OrderedCommRing→CommRing B)
OrderedCommRingMono→CommRingHom =
  OrderedCommRingHom→CommRingHom ∘ OrderedCommRingMono→OrderedCommRingHom

isPropIsOrderedCommRingMono : {A : Type ℓ} {B : Type ℓ'}
                            → (R : OrderedCommRingStr ℓ<≤ A)
                            → (f : A → B)
                            → (S : OrderedCommRingStr ℓ<≤' B)
                            → isProp (IsOrderedCommRingMono R f S)
isPropIsOrderedCommRingMono R f S = isOfHLevelRetractFromIso 1
  IsOrderedCommRingMonoIsoΣ $
  isProp× (isPropIsOrderedCommRingHom R f S)
          (isPropΠ2 λ _ _ → isProp→ (S.is-prop-valued< _ _))
  where
    open module S = OrderedCommRingStr S

isSetOrderedCommRingMono : (R : OrderedCommRing ℓ ℓ<≤) (S : OrderedCommRing ℓ' ℓ<≤')
                         → isSet (OrderedCommRingMono R S)
isSetOrderedCommRingMono R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f →
  isPropIsOrderedCommRingMono (snd R) f (snd S))
    where open OrderedCommRingStr (str S) using (is-set)

module _
  {R : OrderedCommRing ℓ  ℓ<≤}
  {S : OrderedCommRing ℓ' ℓ<≤'}
  {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = OrderedCommRingStr (str R)
    module S = OrderedCommRingStr (str S)

  module _
    (p1  : f R.1r ≡ S.1r)
    (p+  : ∀ x y → f (x R.+ y) ≡ f x S.+ f y)
    (p·  : ∀ x y → f (x R.· y) ≡ f x S.· f y)
    (p<  : ∀ x y → x R.< y → f x S.< f y)
    (p<⁻ : ∀ x y → f x S.< f y → x R.< y)
    where

    open IsOrderedCommRingMono

    makeIsOrderedCommRingMono : IsOrderedCommRingMono (str R) f (str S)
    makeIsOrderedCommRingMono .isOrderedCommRingHom = makeIsOrderedCommRingHom p1 p+ p· p<⁻
    makeIsOrderedCommRingMono .pres< = p<

  module _ (isMonof : IsOrderedCommRingMono (str R) f (str S)) where

    isOrderedCommRingMono→reflect≤ : ∀ x y → f x S.≤ f y → x R.≤ y
    isOrderedCommRingMono→reflect≤ x y =
      invEq (R.≤≃¬> x y) ∘ (_∘ pres< y x) ∘ equivFun (S.≤≃¬> (f x) (f y))
      where open IsOrderedCommRingMono isMonof

    isOrderedCommRingMono→isOrderedCommRingHom : IsOrderedCommRingHom (str R) f (str S)
    isOrderedCommRingMono→isOrderedCommRingHom = isOrderedCommRingHom
      where open IsOrderedCommRingMono isMonof

    isOrderedCommRingMono→isInjective : ∀ x y → f x ≡ f y → x ≡ y
    isOrderedCommRingMono→isInjective x y fx≡fy = R.is-antisym x y
      (isOrderedCommRingMono→reflect≤ x y (subst (S._≤_ (f x)) fx≡fy (S.is-refl _)))
      (isOrderedCommRingMono→reflect≤ y x (subst (S._≤_ (f y)) (sym fx≡fy) (S.is-refl _)))

opaque
  OrderedCommRingMono≡ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
                       → {φ ψ : OrderedCommRingMono R S}
                       → fst φ ≡ fst ψ
                       → φ ≡ ψ
  OrderedCommRingMono≡ = Σ≡Prop λ f → isPropIsOrderedCommRingMono _ f _

  OrderedCommRingMonoPathP : (R : OrderedCommRing ℓ ℓ<≤) (S T : OrderedCommRing ℓ' ℓ<≤')
                           → (p : S ≡ T)
                           → (φ : OrderedCommRingMono R S)
                           → (ψ : OrderedCommRingMono R T)
                           → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
                           → PathP (λ i → OrderedCommRingMono R (p i)) φ ψ
  OrderedCommRingMonoPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ →
    isPropIsOrderedCommRingMono _ _ _) _ _)

record IsOrderedCommRingEquiv {A : Type ℓ} {B : Type ℓ'}
  (R : OrderedCommRingStr ℓ<≤ A) (e : A ≃ B) (S : OrderedCommRingStr ℓ<≤' B)
  : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ<≤) ℓ') ℓ<≤')
  where
  no-eta-equality
  private
    module R = OrderedCommRingStr R
    module S = OrderedCommRingStr S
    Rcring = str (OrderedCommRing→CommRing (_ , R))
    Scring = str (OrderedCommRing→CommRing (_ , S))
    f = equivFun e

  field
    pres0 : f R.0r ≡ S.0r
    pres1 : f R.1r ≡ S.1r
    pres+ : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres· : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres- : (x : A) → f (R.- x) ≡ S.- (f x)
    pres≤ : (x y : A) → (x R.≤ y) ≃ (f x S.≤ f y)
    pres< : (x y : A) → (x R.< y) ≃ (f x S.< f y)

unquoteDecl IsOrderedCommRingEquivIsoΣ = declareRecordIsoΣ IsOrderedCommRingEquivIsoΣ (quote IsOrderedCommRingEquiv)

OrderedCommRingEquiv : OrderedCommRing ℓ ℓ<≤ → OrderedCommRing ℓ' ℓ<≤' → Type _
OrderedCommRingEquiv R S =
  Σ[ e ∈ (R .fst ≃ S .fst) ] IsOrderedCommRingEquiv (R .snd) e (S .snd)


OrderedCommRingEquiv→OrderedCommRingMono : {A : OrderedCommRing ℓ  ℓ<≤}
                                         → {B : OrderedCommRing ℓ' ℓ<≤'}
                                         → OrderedCommRingEquiv A B
                                         → OrderedCommRingMono A B
fst (OrderedCommRingEquiv→OrderedCommRingMono e) = equivFun (fst e)
snd (OrderedCommRingEquiv→OrderedCommRingMono e) = isOCRMono
  where
    module E = IsOrderedCommRingEquiv (snd e)
    open IsCommRingHom
    open IsOrderedCommRingHom  renaming (isCommRingHom to isCRHom)
    open IsOrderedCommRingMono renaming (isOrderedCommRingHom to isOCRHom)

    isOCRMono : IsOrderedCommRingMono _ _ _
    isOCRMono .isOCRHom .isCRHom .pres0 = E.pres0
    isOCRMono .isOCRHom .isCRHom .pres1 = E.pres1
    isOCRMono .isOCRHom .isCRHom .pres+ = E.pres+
    isOCRMono .isOCRHom .isCRHom .pres· = E.pres·
    isOCRMono .isOCRHom .isCRHom .pres- = E.pres-
    isOCRMono .isOCRHom .pres≤          = (equivFun ∘_) ∘ E.pres≤
    isOCRMono .isOCRHom .reflect<       = (invEq ∘_) ∘ E.pres<
    isOCRMono .pres<                    = (equivFun ∘_) ∘ E.pres<

OrderedCommRingEquiv→OrderedCommRingHom : {A : OrderedCommRing ℓ  ℓ<≤}
                                        → {B : OrderedCommRing ℓ' ℓ<≤'}
                                        → OrderedCommRingEquiv A B
                                        → OrderedCommRingHom A B
OrderedCommRingEquiv→OrderedCommRingHom =
  OrderedCommRingMono→OrderedCommRingHom ∘ OrderedCommRingEquiv→OrderedCommRingMono

OrderedCommRingEquiv→CommRingHom : {A : OrderedCommRing ℓ  ℓ<≤}
                                 → {B : OrderedCommRing ℓ' ℓ<≤'}
                                 → OrderedCommRingEquiv A B
                                 → CommRingHom
                                    (OrderedCommRing→CommRing A)
                                    (OrderedCommRing→CommRing B)
OrderedCommRingEquiv→CommRingHom =
  OrderedCommRingHom→CommRingHom ∘ OrderedCommRingEquiv→OrderedCommRingHom

isPropIsOrderedCommRingEquiv : {A : Type ℓ} {B : Type ℓ'}
                             → (R : OrderedCommRingStr ℓ<≤ A)
                             → (e : A ≃ B)
                             → (S : OrderedCommRingStr ℓ<≤' B)
                             → isProp (IsOrderedCommRingEquiv R e S)
isPropIsOrderedCommRingEquiv R e S = isOfHLevelRetractFromIso 1
  IsOrderedCommRingEquivIsoΣ $
  isProp× (S.is-set _ _) $
  isProp× (S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ  λ _   → S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → isOfHLevel≃ 1 (R.is-prop-valued≤ _ _) (S.is-prop-valued≤ _ _))
          (isPropΠ2 λ _ _ → isOfHLevel≃ 1 (R.is-prop-valued< _ _) (S.is-prop-valued< _ _))
  where
    open module R = OrderedCommRingStr R
    open module S = OrderedCommRingStr S

isSetOrderedCommRingEquiv : (R : OrderedCommRing ℓ ℓ<≤) (S : OrderedCommRing ℓ' ℓ<≤')
                          → isSet (OrderedCommRingEquiv R S)
isSetOrderedCommRingEquiv R S = isSetΣSndProp (isOfHLevel≃ 2 R.is-set S.is-set) (λ e →
  isPropIsOrderedCommRingEquiv (snd R) e (snd S))
    where
      open module R = OrderedCommRingStr (str R)
      open module S = OrderedCommRingStr (str S)

-- an easier way of establishing an equivalence of ordered commutative rings
module _ {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'} (e : ⟨ R ⟩ ≃ ⟨ S ⟩)
  where
  private
    module R = OrderedCommRingStr (str R)
    module S = OrderedCommRingStr (str S)

  module _ (isMono : IsOrderedCommRingMono (str R) (equivFun e) (str S)) where

    private
      module M = IsOrderedCommRingMono isMono

    open IsOrderedCommRingEquiv

    makeIsOrderedCommRingEquivFromIsMono : IsOrderedCommRingEquiv (str R) e (str S)
    makeIsOrderedCommRingEquivFromIsMono .pres0 = M.pres0
    makeIsOrderedCommRingEquivFromIsMono .pres1 = M.pres1
    makeIsOrderedCommRingEquivFromIsMono .pres+ = M.pres+
    makeIsOrderedCommRingEquivFromIsMono .pres· = M.pres·
    makeIsOrderedCommRingEquivFromIsMono .pres- = M.pres-
    makeIsOrderedCommRingEquivFromIsMono .pres≤ = λ x y → propBiimpl→Equiv
      (R.is-prop-valued≤ _ _) (S.is-prop-valued≤ _ _)
      (M.pres≤ x y) (isOrderedCommRingMono→reflect≤ isMono x y)
    makeIsOrderedCommRingEquivFromIsMono .pres< = λ x y → propBiimpl→Equiv
      (R.is-prop-valued< _ _) (S.is-prop-valued< _ _)
      (M.pres< x y) (M.reflect< x y)

  module _
    (p1  : equivFun e R.1r ≡ S.1r)
    (p+  : ∀ x y → equivFun e (x R.+ y) ≡ equivFun e x S.+ equivFun e y)
    (p·  : ∀ x y → equivFun e (x R.· y) ≡ equivFun e x S.· equivFun e y)
    (p<  : ∀ x y → x R.< y → equivFun e x S.< equivFun e y)
    (p<⁻ : ∀ x y → equivFun e x S.< equivFun e y → x R.< y)
    where

    makeIsOrderedCommRingEquiv : IsOrderedCommRingEquiv (str R) e (str S)
    makeIsOrderedCommRingEquiv = makeIsOrderedCommRingEquivFromIsMono
      (makeIsOrderedCommRingMono p1 p+ p· p< p<⁻)

{-# OPTIONS --safe #-}
module Cubical.Homotopy.Connected where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure

open import Cubical.Functions.Fibration
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection

open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (elim; _≤_)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Properties

open import Cubical.HITs.Nullification hiding (elim)
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.S1 hiding (elim)
open import Cubical.HITs.Truncation as Trunc
  renaming (rec to trRec) hiding (elim)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level
    A B X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type ℓ

-- Note that relative to most sources, this notation is off by +2
isConnected : ∀ {ℓ} (n : HLevel) (A : Type ℓ) → Type ℓ
isConnected n A = isContr (hLevelTrunc n A)

isConnectedFun : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isConnectedFun n f = ∀ b → isConnected n (fiber f b)

isConnectedZero : ∀ {ℓ} (A : Type ℓ) → isConnected 0 A
isConnectedZero A = isContrUnit*

isConnectedSubtr : ∀ {ℓ} {A : Type ℓ} (n m : HLevel)
                → isConnected (m + n) A
                → isConnected n A
isConnectedSubtr {A = A} n m iscon =
  isOfHLevelRetractFromIso 0 (truncOfTruncIso n m) (helper n iscon)
  where
  helper : (n : ℕ) → isConnected (m + n) A → isContr (hLevelTrunc n (hLevelTrunc (m + n) A))
  helper zero iscon = isContrUnit*
  helper (suc n) iscon = ∣ iscon .fst ∣ , (Trunc.elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → cong ∣_∣ (iscon .snd a))

isConnectedSubtr' : ∀ {ℓ} {A : Type ℓ} (n m : HLevel)
                → isConnected (m + n) A
                → isConnected m A
isConnectedSubtr' {A = A} n m iscon =
  isConnectedSubtr m n (subst (λ k → isConnected k A) (+-comm m n) iscon)

isConnectedFunSubtr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : HLevel) (f : A → B)
                → isConnectedFun (m + n) f
                → isConnectedFun n f
isConnectedFunSubtr n m f iscon b = isConnectedSubtr n m (iscon b)

isConnectedFun≤ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : HLevel) (f : A → B)
  → n ≤ m → isConnectedFun m f → isConnectedFun n f
isConnectedFun≤ n m f hnm hf =
  isConnectedFunSubtr n (hnm .fst) f
    (subst (λ d → isConnectedFun d f) (sym (hnm .snd)) hf)

private
  typeToFiberIso : ∀ {ℓ} (A : Type ℓ) → Iso A (fiber (λ (x : A) → tt) tt)
  Iso.fun (typeToFiberIso A) x = x , refl
  Iso.inv (typeToFiberIso A) = fst
  Iso.rightInv (typeToFiberIso A) b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
  Iso.leftInv (typeToFiberIso A) a = refl

  typeToFiber : ∀ {ℓ} (A : Type ℓ) → A ≡ fiber (λ (x : A) → tt) tt
  typeToFiber A = isoToPath (typeToFiberIso A)

private
  truncTypeToFiberIso : (n : HLevel) (X : Type ℓ) → Iso (∥ X ∥ n) (∥ fiber (λ x → tt) tt ∥ n)
  truncTypeToFiberIso n X = mapCompIso {n = n} (typeToFiberIso X)

isConnectedFun→isConnected : {X : Type ℓ} (n : HLevel)
  → isConnectedFun n (λ (_ : X) → tt) → isConnected n X
isConnectedFun→isConnected {X = X} zero _ = isConnectedZero X
isConnectedFun→isConnected {X = X} n@(suc _) h =
  isOfHLevelRetractFromIso 0 (truncTypeToFiberIso n X) is-contr-fiber
  where
    is-contr-fiber : isContr (∥ fiber (λ (_ : X) → tt) tt ∥ n)
    is-contr-fiber = h tt

isConnected→isConnectedFun : {X : Type ℓ} (n : HLevel)
  → isConnected n X → isConnectedFun n (λ (_ : X) → tt)
isConnected→isConnectedFun {X = X} zero h = isConnectedZero ∘ fiber {A = X} (λ _ → tt)
isConnected→isConnectedFun {X = X} n@(suc _) h tt = isOfHLevelRetractFromIso 0 (invIso (truncTypeToFiberIso n X)) h

-- Being a connected type is a proposition.
isPropIsConnected : ∀ {n : ℕ} → isProp (isConnected n A)
isPropIsConnected {A = A} {n = n} = isPropIsContr {A = hLevelTrunc n A}

-- Being a connected function is a proposition.
isPropIsConnectedFun : ∀ {n : HLevel} {f : A → B} → isProp (isConnectedFun n f)
isPropIsConnectedFun = isPropΠ λ _ → isPropIsConnected

isOfHLevelIsConnectedStable : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → isOfHLevel n (isConnected n A)
isOfHLevelIsConnectedStable {A = A} zero =
  (tt* , (λ _ → refl)) , λ _ → refl
isOfHLevelIsConnectedStable {A = A} (suc n) =
  isProp→isOfHLevelSuc n isPropIsConnected

-- A k-connected k-type is contractible.
isOfHLevel×isConnected→isContr : ∀ {ℓ} (k : HLevel)
  → (A : Type ℓ)
  → (isOfHLevel k A)
  → (isConnected k A)
  → isContr A
isOfHLevel×isConnected→isContr zero A is-contr-A _ = is-contr-A
isOfHLevel×isConnected→isContr (suc k) A is-trunc-A is-conn-A = is-contr-A where
  universal-property-trunc : ∥ A ∥ suc k ≃ A
  universal-property-trunc = truncIdempotent≃ (suc k) is-trunc-A

  is-contr-A : isContr A
  is-contr-A = isOfHLevelRespectEquiv 0 universal-property-trunc is-conn-A

module elim {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  private
    inv : ∀ {ℓ'''} (n : HLevel) (P : B → TypeOfHLevel ℓ''' (suc n))
        → ((a : A) → P (f a) .fst)
        → (b : B)
        → hLevelTrunc (suc n) (fiber f b) → P b .fst
    inv n P t b =
      Trunc.rec
        (P b .snd)
        (λ {(a , p) → subst (fst ∘ P) p (t a)})

  isIsoPrecompose : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
  Iso.fun (isIsoPrecompose _ P fConn) = _∘ f
  Iso.inv (isIsoPrecompose zero P fConn) =
    Iso.inv (isContr→Iso' (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd) (_∘ f))
  Iso.rightInv (isIsoPrecompose zero P fConn) =
    Iso.rightInv (isContr→Iso' (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd) (_∘ f))
  Iso.leftInv (isIsoPrecompose zero P fConn) =
    Iso.leftInv (isContr→Iso' (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd) (_∘ f))
  Iso.inv (isIsoPrecompose (suc n) P fConn) t b = inv n P t b (fConn b .fst)
  Iso.rightInv (isIsoPrecompose (suc n) P fConn) t =
    funExt λ a → cong (inv n P t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
               ∙ substRefl {B = fst ∘ P} (t a)
  Iso.leftInv (isIsoPrecompose (suc n) P fConn) s =
    funExt λ b →
          Trunc.elim
            {B = λ d → inv n P (s ∘ f) b d ≡ s b}
            (λ _ → isOfHLevelPath (suc n) (P b .snd) _ _)
            (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
            (fConn b .fst)

  isIsoPrecomposeβ : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
                   → (e : isConnectedFun n f)
                   → (g : ((a : A) → P (f a) .fst))
                   → (a : A)
                   → Iso.inv (isIsoPrecompose n P e) g (f a) ≡ g a
  isIsoPrecomposeβ zero P e g a = P (f a) .snd .snd (g a)
  isIsoPrecomposeβ (suc n) P e g a =
      cong (inv n P g (f a)) (e (f a) .snd ∣ a , refl ∣)
    ∙ transportRefl _

  isEquivPrecompose : ∀ {ℓ'''} (n : ℕ) (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
  isEquivPrecompose zero P fConn = isoToIsEquiv theIso
    where
    theIso : Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
    Iso.fun theIso = λ(s : (b : B) → P b .fst) → s ∘ f
    Iso.inv theIso = λ _ b → P b .snd .fst
    Iso.rightInv theIso g = funExt λ x → P (f x) .snd .snd (g x)
    Iso.leftInv theIso g = funExt λ x → P x .snd .snd (g x)
  isEquivPrecompose (suc n) P fConn = isoToIsEquiv (isIsoPrecompose (suc n) P fConn)

  isConnectedPrecompose : (n : ℕ) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
                                    → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                       → isConnectedFun n f
  isConnectedPrecompose zero P→sect b = isContrUnit*
  isConnectedPrecompose (suc n) P→sect b = c n P→sect b , λ y →  sym (fun n P→sect b y)
    where
    P : (n : HLevel) → ((P : B → TypeOfHLevel ℓ (suc n))
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
     → B → Type _
    P n s b = hLevelTrunc (suc n) (fiber f b)

    c : (n : HLevel) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
     → hLevelTrunc (suc n) (fiber f b)
    c n s = (s λ b → (hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _)) .fst
              λ a → ∣ a , refl ∣

    fun : (n : HLevel) (P→sect : ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') (suc n))
                     → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
      → (b : B) (w : (hLevelTrunc (suc n) (fiber f b)))
      → w ≡ c n P→sect b
    fun n P→sect b = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) _ _)
                                       λ a → J (λ b p → ∣ (fst a) , p ∣ ≡ c n P→sect b)
                                               (c* (fst a))
                                               (snd a)
        where
        c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c n P→sect (f a))
        c* a = sym (cong (λ x → x a) (P→sect (λ b → hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _) .snd λ a → ∣ a , refl ∣))

isOfHLevelPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (k : HLevel) (n : HLevel)
  {A : Type ℓ} {B : Type ℓ'} (P : B → TypeOfHLevel ℓ'' (k + n)) (f : A → B)
  → isConnectedFun n f
  → isOfHLevelFun k (λ(s : (b : B) → P b .fst) → s ∘ f)
isOfHLevelPrecomposeConnected zero n P f fConn =
  elim.isEquivPrecompose f n P fConn .equiv-proof
isOfHLevelPrecomposeConnected (suc k) n P f fConn t =
  isOfHLevelPath'⁻ k
    λ {(s₀ , p₀) (s₁ , p₁) →
      isOfHLevelRetractFromIso k (invIso ΣPathIsoPathΣ)
         (subst (isOfHLevel k)
           (sym (fiberPath (s₀ , p₀) (s₁ , p₁)))
           (isOfHLevelRetract k
            (λ {(q , α) → (funExt⁻ q) , (cong funExt⁻ α)})
            (λ {(h , β) → (funExt h) , (cong funExt β)})
            (λ _ → refl)
            (isOfHLevelPrecomposeConnected k n
              (λ b → (s₀ b ≡ s₁ b) , isOfHLevelPath' (k + n) (P b .snd) _ _)
              f fConn
              (funExt⁻ (p₀ ∙∙ refl ∙∙ sym p₁)))))}

-- A type A is n-connected if the map `λ b a → b : B → (A → B)` has a section for any n-type B.
indMapHasSection→conType : ∀ {ℓ} {A : Type ℓ} (n : HLevel)
                   → ((B : TypeOfHLevel ℓ n) → hasSection (λ (b : (fst B)) → λ (a : A) → b))
                   → isConnected n A
indMapHasSection→conType {A = A} zero _ = isConnectedZero A
indMapHasSection→conType {A = A} (suc n) ind-map-has-section =
  isConnectedFun→isConnected (suc n) is-conn-fun-const
  where
    module _ (P : Unit → TypeOfHLevel _ (suc n)) where
      B' : Type _
      B' = ⟨ P tt ⟩

      has-section : hasSection λ (b : B') (a : A) → b
      has-section = ind-map-has-section (P tt)

      point : (A → B') → B'
      point = has-section .fst

      precomp-section : ((a : A) → B') → (b : Unit) → B'
      precomp-section = (λ b (_ : Unit) → b) ∘ point

      precomp-has-section : hasSection (λ s → s ∘ (λ (a : A) → tt))
      precomp-has-section .fst = precomp-section
      precomp-has-section .snd = has-section .snd

    is-conn-fun-const : isConnectedFun (suc n) (λ (a : A) → tt)
    is-conn-fun-const = elim.isConnectedPrecompose _ _ precomp-has-section

-- Corollary: A is n-connected if the constant map `B → (A → B)` is an equivalence for any n-type B.
indMapEquiv→conType : ∀ {ℓ} {A : Type ℓ} (n : HLevel)
                   → ((B : TypeOfHLevel ℓ n)
                      → isEquiv (λ (b : (fst B)) → λ (a : A) → b))
                   → isConnected n A
indMapEquiv→conType n is-equiv-ind = indMapHasSection→conType n λ B → _ , secIsEq (is-equiv-ind B)

conType→indMapEquiv : ∀ (n : HLevel)
  → isConnected n A
  → isOfHLevel n B
  → isEquiv (λ (b : B) → λ (a : A) → b)
conType→indMapEquiv {A = A} {B = B} 0 _ is-contr-B = isoToIsEquiv (isContr→Iso' is-contr-B (isContrΠ λ _ → is-contr-B) (λ b a → b))
conType→indMapEquiv {A = A} {B = B} n@(suc _) conn-A is-of-hlevel-B = subst isEquiv fun-equiv≡const (equivIsEquiv fun-equiv) where
  fun-equiv : B ≃ (A → B)
  fun-equiv =
    B ≃⟨ invEquiv $ Π-contractDom conn-A ⟩
    (∥ A ∥ n → B) ≃⟨ isoToEquiv (univTrunc n {B = B , is-of-hlevel-B}) ⟩
    (A → B) ■

  fun-equiv≡const : equivFun fun-equiv ≡ (λ b a → b)
  fun-equiv≡const = funExt λ b → funExt λ a → transportRefl b

-- Corollary 7.5.9 of the HoTT book:
-- A type is n-connected if and only every map into an n-type is constant.
indMapEquiv≃conType : ∀ {ℓ} {A : Type ℓ} (n : HLevel)
  → ((B : TypeOfHLevel ℓ n) → isEquiv (λ (b : ⟨ B ⟩) → λ (a : A) → b))
      ≃
    isConnected n A
indMapEquiv≃conType n = propBiimpl→Equiv
  (isPropΠ λ B → isPropIsEquiv (λ b a → b))
  (isPropIsConnected)
  (indMapEquiv→conType n)
  (λ conn-A (B , is-of-hlevel-B) → conType→indMapEquiv n conn-A is-of-hlevel-B)

isConnected→constEquiv : ∀ (n : HLevel)
  → isConnected n A
  → isOfHLevel n B
  → B ≃ (A → B)
isConnected→constEquiv n conn-A is-of-hlevel-B .fst = λ b a → b
isConnected→constEquiv n conn-A is-of-hlevel-B .snd = conType→indMapEquiv n conn-A is-of-hlevel-B

isConnectedComp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
     (f : B → C) (g : A → B) (n : ℕ)
   → isConnectedFun n f
   → isConnectedFun n g
   → isConnectedFun n (f ∘ g)
isConnectedComp  {C = C} f g n con-f con-g =
  elim.isConnectedPrecompose (f ∘ g) n
    λ P →
      isEquiv→hasSection
        (compEquiv
         (_ , elim.isEquivPrecompose f n P con-f)
         (_ , elim.isEquivPrecompose g n (λ b → P (f b)) con-g) .snd)

isConnectedFunCancel : ∀ {ℓ} {X Y Z : Type ℓ} (f : X → Y) (g : Y → Z) (n : HLevel)
  → isConnectedFun n f → isConnectedFun (1 + n) (g ∘ f) → isConnectedFun (1 + n) g
isConnectedFunCancel {ℓ = ℓ} {X = X} {Y = Y} {Z = Z} f g n nconf con∘ =
  elim.isConnectedPrecompose g (suc n)
    λ P → (d P) , d-sec P
  where
    module _ (P : Z → TypeOfHLevel ℓ (suc n)) where
      d : ((a : Y) → P (g a) .fst) → (b : Z) → P b .fst
      d F z =
        equiv-proof (elim.isEquivPrecompose (g ∘ f) (suc n) P con∘)
          (λ x → F (f x))
          .fst .fst z

      d-sec : section (λ s → s ∘ g) d
      d-sec F =
        funExt
          (equiv-proof
            (elim.isEquivPrecompose f n
             (λ x → ((d F ∘ g) x ≡ F x) , isOfHLevelPath' n (P (g x) .snd) _ _) nconf)
             (λ a → (λ i → rec₊ (P (g (f a)) .snd)
                                 (λ { (a , p) → subst (λ x → fst (P x)) p (F (f a)) })
                                 (con∘ (g (f a)) .snd ∣ a , refl ∣ i))
                   ∙ transportRefl (F (f a)))
          .fst .fst)

isConnectedFunCancel' : (f : X₀ → X₁) (g : X₁ → X₂) (n : HLevel)
  → isConnectedFun (1 + n) g → isConnectedFun n (g ∘ f) → isConnectedFun n f
isConnectedFunCancel' f g zero con-g con-f b =
  tt* , (λ {tt* → refl})
isConnectedFunCancel' {X₀ = X} {X₁ = Y} {X₂ = Z} f g (suc n) con-g con-f =
  elim.isConnectedPrecompose f (suc n)
    λ P → d P , d-sec P
  where
  ℓ' : Level
  ℓ' = _
  module _ (P : Y → TypeOfHLevel ℓ' (suc n)) where
    pre-d : (y : Y) (a : X) (p : _) → ∥ Path (fiber g (g y)) (y , refl) (f a , p) ∥ (suc n)
    pre-d y a p =
      Iso.fun (PathIdTruncIso (suc n))
        (isContr→isProp (con-g (g y)) ∣ y , refl ∣ ∣ (f a , p) ∣)

    pre-d-refl : (x : X) → pre-d (f x) x refl ≡ ∣ (λ b → f x , refl) ∣
    pre-d-refl x =
        (λ i → Iso.fun (PathIdTruncIso (suc n))
                 (isProp→isSet (isContr→isProp (con-g (g (f x)))) _ _
                  (isContr→isProp (con-g (g (f x))) _ _) refl i))
      ∙ cong ∣_∣ₕ (transportRefl (λ b → f x , refl))

    d : ((a : X) → P (f a) .fst) → (b : Y) → P b .fst
    d F y = Trunc.rec (snd (P y))
            (λ {(a , p) →
              Trunc.rec (P y .snd)
                (λ p → subst (fst ∘ P) (cong fst (sym p)) (F a))
                (pre-d y a p)})
            (con-f (g y) .fst)

    d-sec : section (λ s → s ∘ f) d
    d-sec F =
      funExt λ x
        → (λ i → Trunc.rec (snd (P (f x)))
            (λ {(a , p) →
              Trunc.rec (P (f x) .snd)
                (λ p → subst (fst ∘ P) (cong fst (sym p)) (F a))
                (pre-d (f x) a p)})
            (con-f (g (f x)) .snd ∣ x , refl ∣ i))
          ∙ (λ i → Trunc.rec (P (f x) .snd)
               (λ p → subst (fst ∘ P) (cong fst (sym p)) (F x))
               (pre-d-refl x i))
          ∙ transportRefl (F x)

isEquiv→isConnected : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    (f : A → B)
  → isEquiv f
  → (n : ℕ) → isConnectedFun n f
isEquiv→isConnected f iseq n b =
  isContr→isContr∥ n (equiv-proof iseq b)

isConnectedId : ∀ {ℓ} {A : Type ℓ} {n : HLevel} → isConnectedFun n (idfun A)
isConnectedId = isEquiv→isConnected _ (idIsEquiv _) _


isConnectedPath : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isConnected (suc n) A
  → (a₀ a₁ : A) → isConnected n (a₀ ≡ a₁)
isConnectedPath zero connA a₀ a₁ = isContrUnit*
isConnectedPath (suc n) {A = A} connA a₀ a₁ =
  isOfHLevelRetractFromIso 0 (invIso (PathIdTruncIso (suc n))) (isContr→isContrPath connA _ _)

isConnectedPathP : ∀ {ℓ} (n : HLevel) {A : I → Type ℓ}
  → isConnected (suc n) (A i1)
  → (a₀ : A i0) (a₁ : A i1) → isConnected n (PathP A a₀ a₁)
isConnectedPathP n con a₀ a₁ =
  subst (isConnected n) (sym (PathP≡Path _ _ _))
        (isConnectedPath n con _ _)

isConnectedCong : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → isConnectedFun (suc n) f
  → ∀ {a₀ a₁} → isConnectedFun n {A = a₀ ≡ a₁} (cong f)
isConnectedCong n f cf {a₀} {a₁} q =
  subst (isConnected n)
    (sym (fiberCong f q))
    (isConnectedPath n (cf (f a₁)) (a₀ , q) (a₁ , refl))

isConnectedCong² : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B)
    → isConnectedFun (suc (suc n)) f
    → ∀ {a₀ a₁ a₂ a₃} {p : a₀ ≡ a₁} {q : a₂ ≡ a₃}
                       {r : a₀ ≡ a₂} {s : a₁ ≡ a₃}
    → isConnectedFun n
         {A = Square p q r s}
         {B = Square (cong f p) (cong f q) (cong f r) (cong f s)}
         (λ p i j → f (p i j))
isConnectedCong² n {A = A} f cf {a₀} {a₁} {r = r} {s = s}
  = isConnectedCong²' _ r _ s
  where
  isConnectedCong²' : (a₂ : A) (r : a₀ ≡ a₂) (a₃ : A) (s : a₁ ≡ a₃)
       {p : a₀ ≡ a₁} {q : a₂ ≡ a₃}
    → isConnectedFun n
         {A = Square p q r s}
         {B = Square (cong f p) (cong f q) (cong f r) (cong f s)}
         (λ p i j → f (p i j))
  isConnectedCong²' =
    J> (J> isConnectedCong n (cong f) (isConnectedCong (suc n) f cf))

isConnectedCong' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x : A} {y : B}
     (n : ℕ) (f : A → B)
  → isConnectedFun (suc n) f
  → (p : f x ≡ y)
  → isConnectedFun n
      λ (q : x ≡ x) → sym p ∙∙ cong f q ∙∙ p
isConnectedCong' {x = x} n f conf p =
  transport (λ i → (isConnectedFun n
                    λ (q : x ≡ x)
                    → doubleCompPath-filler (sym p) (cong f q) p i))
    (isConnectedCong n f conf)

isConnectedΩ→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → (f : A →∙ B)
  → isConnectedFun (suc n) (fst f)
  → isConnectedFun n (fst (Ω→ f))
isConnectedΩ→ n f g =
  transport (λ i → isConnectedFun n λ b
                 → doubleCompPath-filler (sym (snd f)) (cong (fst f) b) (snd f) i)
            (isConnectedCong n _ g)

isConnectedΩ^→ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n m : ℕ)
  → (f : A →∙ B)
  → isConnectedFun (suc n) (fst f)
  → isConnectedFun ((suc n) ∸ m) (fst (Ω^→ m f))
isConnectedΩ^→ n zero f conf = conf
isConnectedΩ^→ n (suc zero) f conf = isConnectedΩ→ n f conf
isConnectedΩ^→ {A = A} {B = B} n (suc (suc m)) f conf =
  transport (λ i → isConnectedFun (suc n ∸ suc (suc m))
    λ q → doubleCompPath-filler
            (sym (snd (Ω^→ (suc m) f)))
            (cong (fst (Ω^→ (suc m) f)) q)
            (snd (Ω^→ (suc m) f)) i)
    (main n m (isConnectedΩ^→ n (suc m) f conf))
  where
  open import Cubical.Data.Sum
  lem : (n m : ℕ) → ((suc n ∸ m ≡ suc (n ∸ m))) ⊎ (suc n ∸ suc m ≡ 0)
  lem n zero = inl refl
  lem zero (suc m) = inr refl
  lem (suc n) (suc m) = lem n m

  main : (n m : ℕ)
      → isConnectedFun (suc n ∸ suc m) (fst (Ω^→ (suc m) f))
      → isConnectedFun (suc n ∸ suc (suc m))
          {A = Path ((Ω^ (suc m)) (_ , pt A) .fst)
          refl refl}
          (cong (fst (Ω^→ (suc m) f)))
  main n m conf with (lem n (suc m))
  ... | (inl x) =
    isConnectedCong (n ∸ suc m) (fst (Ω^→ (suc m) f))
      (subst (λ x → isConnectedFun x (fst (Ω^→ (suc m) f))) x conf)
  ... | (inr x) =
    subst (λ x → isConnectedFun x (cong {x = refl} {y = refl}
                   (fst (Ω^→ (suc m) f))))
      (sym x)
      λ b → tt* , λ _ → refl

isConnectedRetract : ∀ {ℓ ℓ'} (n : HLevel)
  {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isConnected n B → isConnected n A
isConnectedRetract zero _ _ _ _ = isContrUnit*
isConnectedRetract (suc n) f g h =
  isContrRetract
    (Trunc.map f)
    (Trunc.map g)
    (Trunc.elim
      (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
      (λ a → cong ∣_∣ (h a)))

isConnectedRetractFromIso :  ∀ {ℓ ℓ'} (n : HLevel)
    {A : Type ℓ} {B : Type ℓ'}
  → Iso A B
  → isConnected n B → isConnected n A
isConnectedRetractFromIso n e =
  isConnectedRetract n
    (Iso.fun e)
    (Iso.inv e)
    (Iso.leftInv e)

-- Any (k+1)-connected type is (merely) inhabited.
isConnectedSuc→merelyInh : ∀ (k : HLevel) → isConnected (suc k) A → ∥ A ∥₁
isConnectedSuc→merelyInh {A = A} k conn-A = propTruncTrunc1Iso .Iso.inv (is-1-conn-A .fst) where
  is-1-conn-A : isConnected 1 A
  is-1-conn-A = isConnectedSubtr' k 1 conn-A

-- A pointed type with k-connected path space is (k+1)-connected.
pointed×isConnectedPath→isConnectedSuc : ∀ (k : HLevel) → (a : A) → ((a b : A) → isConnected k (a ≡ b)) → isConnected (suc k) A
pointed×isConnectedPath→isConnectedSuc {A = A} k a conn-path = conn where
  is-of-hlevel-trunc : isOfHLevel (2 + k) (∥ A ∥ (suc k))
  is-of-hlevel-trunc = isOfHLevelSuc (1 + k) (isOfHLevelTrunc (1 + k))

  conn : isConnected (suc k) A
  conn .fst = ∣ a ∣ₕ
  conn .snd = Trunc.elim
    (λ y → is-of-hlevel-trunc ∣ a ∣ y)
    (λ b → PathIdTruncIso k .Iso.inv (conn-path a b .fst))

-- A merely inhabited type with k-connected path space is (k+1)-connected.
merelyInh×isConnectedPath→isConnectedSuc : ∀ (k : HLevel)
  → ∥ A ∥₁
  → ((a b : A) → isConnected k (a ≡ b))
  → isConnected (suc k) A
merelyInh×isConnectedPath→isConnectedSuc k = PT.rec
  (isProp→ isPropIsConnected)
  (pointed×isConnectedPath→isConnectedSuc k)

-- The converse: A (k+1)-connected type is merely inhabited and has k-connected paths.
isConnectedSuc→merelyInh×isConnectedPath : (k : HLevel)
  → isConnected (suc k) A
  → ∥ A ∥₁ × ((a b : A) → isConnected k (a ≡ b))
isConnectedSuc→merelyInh×isConnectedPath k suc-conn-A .fst = isConnectedSuc→merelyInh k suc-conn-A
isConnectedSuc→merelyInh×isConnectedPath k suc-conn-A .snd = isConnectedPath k suc-conn-A

-- HoTT book, Exercise 7.6:
-- A type is k+1-connected whenever it is merely inhabited and has k-connected paths.
merelyInh×isConnectedPath≃isConnectedSuc : ∀ {ℓ} {A : Type ℓ} (k : HLevel)
  → (∥ A ∥₁ × ((a b : A) → isConnected k (a ≡ b))) ≃ (isConnected (suc k) A)
merelyInh×isConnectedPath≃isConnectedSuc k = propBiimpl→Equiv
  (isProp× PT.isPropPropTrunc $ isPropΠ2 λ a b → isPropIsConnected)
  isPropIsConnected
  (uncurry $ merelyInh×isConnectedPath→isConnectedSuc k)
  (isConnectedSuc→merelyInh×isConnectedPath k)

-- If a type is (k+1)-inhabited and has k-connected paths, then it is (k+1)-connected.
inhTruncSuc×isConnectedPath→isConnectedSuc : ∀ (k : HLevel)
  → ∥ A ∥ (suc k)
  → ((a b : A) → isConnected k (a ≡ b))
  → isConnected (suc k) A
inhTruncSuc×isConnectedPath→isConnectedSuc k = Trunc.rec
  (isOfHLevelΠ (suc k) λ _ → isProp→isOfHLevelSuc k isPropIsConnected)
  (pointed×isConnectedPath→isConnectedSuc k)

-- A type is (k+1)-inhabited and has k-connected paths if and only if it is (k+1)-connected.
--
-- Note that the left hand side of the equivalence is not a priori a proposition.
inhTruncSuc×isConnectedPath≃isConnectedSuc : ∀ (k : HLevel)
  → (∥ A ∥ (suc k) × ((a b : A) → isConnected k (a ≡ b))) ≃ (isConnected (suc k) A)
inhTruncSuc×isConnectedPath≃isConnectedSuc {A = A} k = equiv where
  -- The left-to-right implication has been established above.
  impl : (∥ A ∥ (suc k) × ((a b : A) → isConnected k (a ≡ b))) → (isConnected (suc k) A)
  impl = uncurry (inhTruncSuc×isConnectedPath→isConnectedSuc k)

  -- Even though ∥ A ∥ₖ₊₁ is not a proposition in general, we know that this is the
  -- case whenever A is (k+1)-connected.  We can thus prove that fibers of the above
  -- implication are contractible, since we get to assume (k+1)-connectedness of A:
  is-contr-fiber-impl : (suc-conn-A : isConnected (suc k) A) → isContr (fiber impl suc-conn-A)
  is-contr-fiber-impl suc-conn-A = goal where
    -- (1). By assumption, having k-connected paths is an inhabited proposition, i.e. contractible.
    is-contr-is-conn-path : isContr (∀ (a b : A) → isConnected k (a ≡ b))
    is-contr-is-conn-path = inhProp→isContr (isConnectedPath k suc-conn-A) (isPropΠ2 λ _ _ → isPropIsConnected)

    -- (2). Being (k+1)-connected means that ∥ A ∥ₖ₊₁ is contractible.
    -- Together with (1), it follows that the domain of the implication is contractible.
    is-contr-trunc×conn-path : isContr (∥ A ∥ (suc k) × ∀ (a b : A) → isConnected k (a ≡ b))
    is-contr-trunc×conn-path = isContrΣ suc-conn-A λ _ → is-contr-is-conn-path

    -- (3). The codomain is a proposition, so its paths are contractible.  As such, there is a unique homotopy
    -- connecting points in the image of `impl` to our assumption of connectedness of A.
    is-contr-impl-conn-path : (trunc×conn : (∥ A ∥ suc k) × (∀ a b → isConnected k (a ≡ b))) → isContr (impl trunc×conn ≡ suc-conn-A)
    is-contr-impl-conn-path trunc×conn = isProp→isContrPath isPropIsConnected (impl trunc×conn) suc-conn-A

    -- Together, (2) and (3) say that `impl` has contractible fibers.
    goal : isContr (fiber impl suc-conn-A)
    goal = isContrΣ is-contr-trunc×conn-path is-contr-impl-conn-path

  equiv : _ ≃ _
  equiv .fst = impl
  equiv .snd .equiv-proof = is-contr-fiber-impl

isConnectedSuc→inhTruncSuc×isConnectedPath : ∀ (k : HLevel)
  → (isConnected (suc k) A)
  → (∥ A ∥ (suc k) × ((a b : A) → isConnected k (a ≡ b)))
isConnectedSuc→inhTruncSuc×isConnectedPath k = invEq $ inhTruncSuc×isConnectedPath≃isConnectedSuc k

-- In a (k+2)-connected space, all loop spaces are merely equivalent
isConnected→mereLoopSpaceEquiv : (k : HLevel) → isConnected (2 + k) A → (a b : A) → ∥ (a ≡ a) ≃ (b ≡ b) ∥₁
isConnected→mereLoopSpaceEquiv {A = A} k conn-A a b = do
  -- Paths in A are (k+1)-connected:
  let conn-path-A : (a b : A) → isConnected (suc k) (a ≡ b)
      conn-path-A = isConnectedPath (suc k) conn-A
  -- Therefore, there merely exists a path a ≡ b:
  a≡b ← isConnectedSuc→merelyInh k (conn-path-A a b)
  -- Conjugation by this path induces an equivance of loop spaces
  return (conjugatePathEquiv a≡b)
  where
    open import Cubical.HITs.PropositionalTruncation.Monad

isConnectedPoint : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isConnected (suc n) A
  → (a : A) → isConnectedFun n (λ(_ : Unit) → a)
isConnectedPoint n connA a₀ a =
  isConnectedRetract n
    snd (_ ,_) (λ _ → refl)
    (isConnectedPath n connA a₀ a)

isConnectedPoint2 : ∀ {ℓ} (n : HLevel) {A : Type ℓ} (a : A)
   → isConnectedFun n (λ(_ : Unit) → a)
   → isConnected (suc n) A
isConnectedPoint2 n {A = A} a connMap = indMapEquiv→conType _ λ B → isoToIsEquiv (theIso B)
  where
  module _  {ℓ' : Level} (B : TypeOfHLevel ℓ' (suc n))
    where
    helper : (f : A → fst B) → (a2 : A) → f a2 ≡ f a
    helper f = equiv-proof (elim.isEquivPrecompose (λ _ → a) n (λ a2 → (f a2 ≡ f a) ,
                             isOfHLevelPath' n (snd B) (f a2) (f a)) connMap) (λ _ → refl) .fst .fst

    theIso : Iso (fst B) (A → fst B)
    Iso.fun theIso b a = b
    Iso.inv theIso f = f a
    Iso.rightInv theIso f = funExt λ y → sym (helper f y)
    Iso.leftInv theIso _ = refl

module isConnectedPoint {ℓ ℓ'} (n : HLevel) {A : Type ℓ}
     {B : A → Type ℓ'}
     (conA : isConnected (suc n) A)
     (hlevB : (a : A) → isOfHLevel n (B a))
     (p : Σ[ a ∈ A ] (B a)) where
  private
    module m = elim (λ (tt : Unit) → fst p)
    P : A → TypeOfHLevel ℓ' n
    P a = B a , hlevB a
    con* = isConnectedPoint n conA (fst p)

  elim : (a : A) → B a
  elim = Iso.inv (m.isIsoPrecompose n P con*) λ _ → snd p

  β : elim (fst p) ≡ snd p
  β = m.isIsoPrecomposeβ n P con* (λ _ → snd p) tt

connectedTruncIso : ∀ {ℓ} {A B : Type ℓ} (n : HLevel) (f : A → B)
                   → isConnectedFun n f
                   → Iso (hLevelTrunc n A) (hLevelTrunc n B)
connectedTruncIso {A = A} {B = B} zero f con = isContr→Iso isContrUnit* isContrUnit*
connectedTruncIso {A = A} {B = B} (suc n) f con = g
  where
  back : B → hLevelTrunc (suc n) A
  back y = map fst ((con y) .fst)

  backSection :  (b : B) → Path (hLevelTrunc (suc n) B)
                                (Trunc.rec (isOfHLevelTrunc (suc n))
                                           (λ a → ∣ f a ∣)
                                           (Trunc.rec (isOfHLevelTrunc (suc n))
                                                      back ∣ b ∣))
                               ∣ b ∣
  backSection b = helper (λ p → map f p ≡ ∣ b ∣)
                         (λ x → (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n)))
                                   (map f (map fst x)) ∣ b ∣)
                         (λ a p → cong ∣_∣ p)
                         (fst (con b))
    where
    helper : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} (P : hLevelTrunc (suc n) A → Type ℓ'')
           → ((x : hLevelTrunc (suc n) (Σ A B)) → isOfHLevel (suc n) (P (map fst x)))
           → ((a : A) (b : B a) → P ∣ a ∣)
           → (p : hLevelTrunc (suc n) (Σ A B))
           →  P (map fst p)
    helper P hlev pf = Trunc.elim hlev λ pair → pf (fst pair) (snd pair)

  g : Iso (hLevelTrunc (suc n) A) (hLevelTrunc (suc n) B)
  Iso.fun g = map f
  Iso.inv g = Trunc.rec (isOfHLevelTrunc _) back
  Iso.leftInv g = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) _ _)
                               λ a → cong (map fst) (con (f a) .snd  ∣ a , refl ∣)
  Iso.rightInv g = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) _ _)
                              backSection

connectedTruncIso2 : ∀ {ℓ} {A B : Type ℓ} (n m : HLevel) (f : A → B)
                   → Σ[ x ∈ ℕ ] x + n ≡ m
                   → isConnectedFun m f
                   → Iso (hLevelTrunc n A) (hLevelTrunc n B)
connectedTruncIso2 {A = A} {B = B} n m f (x , pf) con =
  connectedTruncIso n f (isConnectedFunSubtr n x f (transport (λ i → isConnectedFun (pf (~ i)) f) con))

connectedTruncEquiv : ∀ {ℓ} {A B : Type ℓ} (n : HLevel) (f : A → B)
                   → isConnectedFun n f
                   → hLevelTrunc n A ≃ hLevelTrunc n B
connectedTruncEquiv {A = A} {B = B} n f con = isoToEquiv (connectedTruncIso n f con)

isConnectedSuc→isSurjection : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n : HLevel}
  → isConnectedFun (suc n) f → isSurjection f
isConnectedSuc→isSurjection hf b =
  Iso.inv propTruncTrunc1Iso (isConnectedFun≤ 1 _ _ (suc-≤-suc zero-≤) hf b .fst)

isConnectedSuspFun : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
       (f : X → Y) (n : HLevel)
    → isConnectedFun n f
    → isConnectedFun (suc n) (suspFun f)
isConnectedSuspFun {X = X} {Y = Y} f n con-f =
  elim.isConnectedPrecompose _ (suc n)
    λ P → d P , d-sec P
  where
  ℓ'' : Level
  ℓ'' = _
  module _ (P : Susp Y → TypeOfHLevel ℓ'' (suc n)) where
    module _ (a : _) (F : ((a : Susp X) → P (suspFun f a) .fst)) where
      d-pre₁ : fiber f a → PathP (λ i → P (merid a i) .fst) (F north) (F south)
      d-pre₁ (x , p) =
        subst (λ a → PathP (λ i₁ → P (merid a i₁) .fst) (F north) (F south)) p
         (cong F (merid x))

      d-pre₂ :  hLevelTrunc n (fiber f a)
             → PathP (λ i → P (merid a i) .fst) (F north) (F south)
      d-pre₂ s =
        trRec (isOfHLevelPathP' n (snd (P south)) _ _)
              (d-pre₁)
              s

    d : ((a : Susp X) → P (suspFun f a) .fst) → (b : Susp Y) → P b .fst
    d F north = F north
    d F south = F south
    d F (merid a i) = d-pre₂ a F (con-f a .fst) i

    d-sec : section (λ s → s ∘ (λ z → suspFun f z)) d
    d-sec F =
      funExt λ { north → refl
               ; south → refl
               ; (merid a i) j → help a j i}
      where
      help : (a : _) → cong (d F ∘ suspFun f) (merid a) ≡ cong F (merid a)
      help a =
        (λ i → d-pre₂ (f a) F (con-f (f a) .snd ∣ a , refl ∣ₕ i))
        ∙ recₕ n (a , refl)
        ∙ transportRefl (cong F (merid a))

isConnectedSusp : ∀ {ℓ} {X : Type ℓ} (n : HLevel)
  → isConnected n X
  → isConnected (suc n) (Susp X)
isConnectedSusp {X = X} n h = isConnectedFun→isConnected (suc n) $
  isConnectedComp _ (suspFun (λ (x : X) → tt)) (suc n)
    (isEquiv→isConnected _ (equivIsEquiv (invEquiv Unit≃SuspUnit)) (suc n))
    (isConnectedSuspFun _ n (isConnected→isConnectedFun n h))

-- See also `sphereConnected` for S₊
isConnectedSphere : ∀ (n : ℕ) → isConnected n (S (-1+ n))
isConnectedSphere zero = isConnectedZero (S (-1+ 0))
isConnectedSphere (suc n) = isConnectedSusp n (isConnectedSphere n)

isConnected-map-× : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : HLevel)
  (f : B → C) → isConnectedFun n f → isConnectedFun n (map-× (idfun A) f)
isConnected-map-× n f hf z =
  isConnectedRetractFromIso _ (invIso $ fiber-map-× f (fst z) (snd z)) (hf (snd z))

-- TODO : Reorganise the following proofs.

inrConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : HLevel)
            → (f : C → A) (g : C → B)
            → isConnectedFun n f
            → isConnectedFun n {A = B} {B = Pushout f g} inr
inrConnected {A = A} {B = B} {C = C} n f g iscon =
  elim.isConnectedPrecompose inr n λ P → (k P) , λ b → refl
  where
  module _ {ℓ : Level} (P : (Pushout f g) → TypeOfHLevel ℓ n)
                   (h : (b : B) → typ (P (inr b)))
    where
    Q : A → TypeOfHLevel _ n
    Q a = (P (inl a))

    fun : (c : C) → typ (Q (f c))
    fun c = transport (λ i → typ (P (push c (~ i)))) (h (g c))

    k : (d : Pushout f g) → typ (P d)
    k (inl x) = equiv-proof (elim.isEquivPrecompose f n Q iscon) fun .fst .fst x
    k (inr x) = h x
    k (push a i) =
      hcomp (λ k → λ { (i = i0) → equiv-proof (elim.isEquivPrecompose f n Q iscon) fun .fst .snd i0 a
                     ; (i = i1) → transportTransport⁻ (λ j → typ (P (push a j))) (h (g a)) k })
            (transp (λ j → typ (P (push a (i ∧ j))))
                    (~ i)
                    (equiv-proof (elim.isEquivPrecompose f n Q iscon)
                                 fun .fst .snd i a))

inlConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : ℕ)
            → (f : C → A) (g : C → B)
            → isConnectedFun n g
            → isConnectedFun n {A = A} {B = Pushout f g} inl
inlConnected {A = A} {B = B} {C = C} n f g iscon =
  transport (λ i → isConnectedFun n (lem i))
    (inrConnected n g f iscon)
  where
  lem : PathP (λ i → A → ua (symPushout g f) i) inr inl
  lem = toPathP (λ j x → inl (transportRefl (transportRefl x j) j))

isConnectedPushout→ :
  (f₁ : X₀ → X₁) (f₂ : X₀ → X₂) (g₁ : Y₀ → Y₁) (g₂ : Y₀ → Y₂)
  (h₀ : X₀ → Y₀) (h₁ : X₁ → Y₁) (h₂ : X₂ → Y₂)
  (e₁ : h₁ ∘ f₁ ≡ g₁ ∘ h₀) (e₂ : h₂ ∘ f₂ ≡ g₂ ∘ h₀)
  (n : HLevel)
  → isConnectedFun n h₀ → isConnectedFun (1 + n) h₁ → isConnectedFun (1 + n) h₂
  → isConnectedFun (1 + n) (Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂)
isConnectedPushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂ n con₀ con₁ con₂ =
  elim.isConnectedPrecompose _ (suc n)
    λ P → d P , d-sec P
  where
  ℓ' : Level
  ℓ' = _

  Push→ = Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂
  module _ (P : Pushout g₁ g₂ → TypeOfHLevel ℓ' (suc n)) where
    module _ (F : ((a : Pushout f₁ f₂) →
       P (Pushout→ f₁ f₂ g₁ g₂ h₀ h₁ h₂ e₁ e₂ a) .fst) ) where
       incₗ : (x : _) → hLevelTrunc (suc n) (fiber h₁ x) → P (inl x) .fst
       incₗ x = Trunc.rec (snd (P _))
                  (uncurry (λ a → J (λ x y → fst (P (inl x))) (F (inl a))))

       incᵣ : (x : _) → hLevelTrunc (suc n) (fiber h₂ x) → P (inr x) .fst
       incᵣ x = Trunc.rec (snd (P _))
                  (uncurry (λ a → J (λ x y → fst (P (inr x))) (F (inr a))))

       push-lem : (x : _)
         → PathP (λ i₁ → P (push (h₀ x) i₁) .fst)
                  (incₗ (g₁ (h₀ x)) ∣ f₁ x , funExt⁻ e₁ x ∣)
                  (incᵣ (g₂ (h₀ x)) ∣ f₂ x , funExt⁻ e₂ x ∣)
       push-lem x i =
         comp (λ k → P (doubleCompPath-filler
                         (λ j → inl (e₁ j x))
                         (push (h₀ x))
                         (λ j → inr (e₂ (~ j) x)) (~ k) i) .fst)
              (λ k → λ {(i = i0) → transp (λ i₁ → fst (P (inl (e₁ (i₁ ∧ k) x))))
                                       (~ k) (F (inl (f₁ x)))
                       ; (i = i1) → transp (λ i₁ → fst (P (inr (e₂ (i₁ ∧ k) x))))
                                       (~ k) (F (inr (f₂ x)))})
              (F (push x i))

       pre-pushFun : (x : _) → PathP (λ i₁ → P (push (h₀ x) i₁) .fst)
                                 (incₗ (g₁ (h₀ x)) (con₁ (g₁ (h₀ x)) .fst))
                                 (incᵣ (g₂ (h₀ x)) (con₂ (g₂ (h₀ x)) .fst))
       pre-pushFun x = cong (incₗ (g₁ (h₀ x)))
                   (con₁ (g₁ (h₀ x)) .snd ∣ (f₁ x) , (funExt⁻ e₁ x) ∣)
                ◁ (push-lem x)
                ▷ (cong (incᵣ (g₂ (h₀ x)))
                   (sym (con₂ (g₂ (h₀ x)) .snd ∣ (f₂ x) , (funExt⁻ e₂ x) ∣)))

       pushFun : (a : _) → hLevelTrunc n (fiber h₀ a)
         → PathP (λ i → P (push a i) .fst)
                  (incₗ (g₁ a) (con₁ (g₁ a) .fst))
                  (incᵣ (g₂ a) (con₂ (g₂ a) .fst))
       pushFun a =
         trRec (isOfHLevelPathP' n (snd (P _)) _ _)
               (uncurry λ x → J (λ a y →
                 PathP (λ i₁ → P (push a i₁) .fst)
                  (incₗ (g₁ a) (con₁ (g₁ a) .fst))
                  (incᵣ (g₂ a) (con₂ (g₂ a) .fst)))
                (pre-pushFun x))

    d : ((a : Pushout f₁ f₂) → P (Push→ a) .fst) →
        (b : Pushout g₁ g₂) → P b .fst
    d F (inl x) = incₗ F x (con₁ x .fst)
    d F (inr x) = incᵣ F x (con₂ x .fst)
    d F (push a i) = pushFun F a (con₀ a .fst) i

    d-sec : section (λ s → s ∘ Push→) d
    d-sec F =
      funExt λ { (inl x) → cong (incₗ F (h₁ x)) (con₁ (h₁ x) .snd ∣ x , refl ∣)
                           ∙ transportRefl (F (inl x))
               ; (inr x) → cong (incᵣ F (h₂ x)) (con₂ (h₂ x) .snd ∣ x , refl ∣)
                           ∙ transportRefl (F (inr x))
               ; (push a i) → push-case a i}
      where
      push-case : (a : _) →
        PathP (λ i → d F (Push→ (push a i)) ≡ F (push a i))
              (cong (incₗ F (h₁ (f₁ a))) (con₁ (h₁ (f₁ a)) .snd ∣ f₁ a , refl ∣)
              ∙ transportRefl (F (inl (f₁ a))))
              (cong (incᵣ F (h₂ (f₂ a))) (con₂ (h₂ (f₂ a)) .snd ∣ f₂ a , refl ∣)
              ∙ transportRefl (F (inr (f₂ a))))
      push-case a i j =
        comp (λ k → P (doubleCompPath-filler
                        (λ j → inl (e₁ j a))
                        (push (h₀ a))
                        (λ j → inr (e₂ (~ j) a)) (k ∨ j) i) .fst)
             (λ k → λ {(i = i0) → ((cong (incₗ F (e₁ (~ k ∧ ~ j) a))
                                     (con₁ (e₁ (~ k ∧ ~ j) a) .snd
                                      ∣ (f₁ a) , (λ i → e₁ ((~ k ∧ i) ∧ ~ j) a) ∣))
                                   ∙ λ i → transp (λ i₁ → fst (P (inl (e₁ ((~ k ∧ i₁) ∧ ~ j) a))))
                                             (i ∧ k) (F (inl (f₁ a)))) j
                      ; (i = i1) → ((cong (incᵣ F (e₂ (~ k ∧ ~ j) a))
                                     (con₂ (e₂ (~ k ∧ ~ j) a) .snd
                                       ∣ (f₂ a) , (λ i → e₂ ((~ k ∧ i) ∧ ~ j) a) ∣))
                                   ∙ λ i → transp (λ i₁ → fst (P (inr (e₂ ((~ k ∧ i₁) ∧ ~ j) a))))
                                             (i ∧ k) (F (inr (f₂ a)))) j
                      ; (j = i0) → lem₂ k i
                      ; (j = i1) → transportRefl (F (push a i)) k})
             (btm₂ i j)
        where
        lem₁ : cong (d F) (push (h₀ a))
             ≡ (cong (incₗ F (g₁ (h₀ a)))
                (con₁ (g₁ (h₀ a)) .snd ∣ (f₁ a) , (funExt⁻ e₁ a) ∣)
             ◁ push-lem F a
             ▷ sym (cong (incᵣ F (g₂ (h₀ a)))
                (con₂ (g₂ (h₀ a)) .snd ∣ (f₂ a) , (funExt⁻ e₂ a) ∣)))
        lem₁ = cong (pushFun F (h₀ a)) (con₀ (h₀ a) .snd ∣ a , refl ∣ₕ)
             ∙ recₕ n (a , refl)
             ∙ transportRefl _

        lem₂ : SquareP
                (λ k i → P (doubleCompPath-filler
                             (λ j₁ → inl (e₁ j₁ a))
                             (push (h₀ a))
                             (λ j₁ → inr (e₂ (~ j₁) a)) k i) .fst)
                (lem₁ i1)
                (cong (d F) ((λ j₁ → inl (e₁ j₁ a))
                           ∙∙ push (h₀ a)
                           ∙∙ λ j₁ → inr (e₂ (~ j₁) a)))
                (λ k → d F (inl (e₁ (~ k) a)))
                λ k → d F (inr (e₂ (~ k) a))
        lem₂ = sym lem₁
          ◁ λ k i → d F (doubleCompPath-filler
                          (λ j₁ → inl (e₁ j₁ a))
                          (push (h₀ a))
                          (λ j₁ → inr (e₂ (~ j₁) a)) k i)

        btm : (i j : I)
          → P (doubleCompPath-filler
                 (λ j₁ → inl (e₁ j₁ a))
                 (push (h₀ a))
                 (λ j₁ → inr (e₂ (~ j₁) a)) j i) .fst
        btm i j =
          comp (λ k → P (doubleCompPath-filler
                           (λ j₁ → inl (e₁ j₁ a))
                           (push (h₀ a))
                           (λ j₁ → inr (e₂ (~ j₁) a)) (~ k ∨ j) i) .fst)
             (λ k → λ {(i = i0) → transp (λ i₁ → fst (P (inl (e₁ (i₁ ∧ (k ∧ ~ j)) a))))
                                           (~ k ∧ ~ j) (F (inl (f₁ a)))
                      ; (i = i1) → transp (λ i₁ → fst (P (inr (e₂ (i₁ ∧ (k ∧ ~ j)) a))))
                                           (~ k ∧ ~ j) (F (inr (f₂ a)))
                      ; (j = i1) → transport refl (F (push a i))})
             (transportRefl (F (push a i)) (~ j))

        btm₂ : (i j : I) →
          P (doubleCompPath-filler
             (λ j₂ → inl (e₁ j₂ a))
             (push (h₀ a))
             (λ j₂ → inr (e₂ (~ j₂) a)) j i) .fst
        btm₂ i j =
          hcomp
           (λ k → λ {(i = i0) → compPath-filler'
                                   (cong (incₗ F (e₁ (~ j) a))
                                    (con₁ (e₁ (~ j) a) .snd
                                      ∣ (f₁ a) , (λ i → e₁ (i ∧ ~ j) a) ∣))
                                   refl k j
                      ; (i = i1) → compPath-filler'
                                     (cong (incᵣ F (e₂ (~ j) a))
                                      (con₂ (e₂ (~ j) a) .snd
                                       ∣ (f₂ a) , (λ i → e₂ (i ∧ ~ j) a) ∣))
                                     refl k j
                      ; (j = i0) → doubleWhiskFiller
                                      (cong (incₗ F (g₁ (h₀ a)))
                                       (con₁ (g₁ (h₀ a)) .snd
                                        ∣ (f₁ a) , (funExt⁻ e₁ a) ∣))
                                      (push-lem F a)
                                      (sym (cong (incᵣ F (g₂ (h₀ a)))
                                       (con₂ (g₂ (h₀ a)) .snd
                                        ∣ (f₂ a) , (funExt⁻ e₂ a) ∣))) k i
                      ; (j = i1) → transport refl (F (push a i))})
              (btm i j)


module _ {ℓ' ℓ'' : Level}
  (m n : HLevel) {A : Type ℓ} {A' : Type ℓ'} {v : A → A'} {B : Type ℓ''}
  (hA : isConnectedFun m v) (hB : isConnected n B) where

  private module _ {ℓ''' : Level} (P : join A' B → TypeOfHLevel ℓ''' (m + n)) where
    module _ (k : (x : join A B) → P (join→ v (idfun B) x) .fst) where
      -- We encode k as a section f of the family
      --   A
      -- v ↓  X
      --   A' → Type
      -- over A, and use the connectivity assumption on v
      -- to extend it to a section f' over A'.

      X : A' → Type _
      X a' =
        Σ[ x ∈ P (inl a') .fst ]
          ∀ (b : B) → PathP (λ i → P (push a' b i) .fst) x (k (inr b))

      f : (a : A) → X (v a)
      fst (f a) = k (inl a)
      snd (f a) = λ b i → k (push a b i)

      -- Equivalent type to X, whose h-level we can estimate.
      X' : A' → Type _
      X' a' =
        Σ[ x' ∈ (Unit → P (inl a') .fst) ]
          (λ (b : B) → x' tt) ≡
          (λ (b : B) → subst⁻ (λ y → P y .fst) (push a' b) (k (inr b)))

      X≃X' : (a' : A') → X a' ≃ X' a'
      X≃X' a' =
        (Σ[ x ∈ P (inl a') .fst ]
          ∀ (b : B) → PathP (λ i → P (push a' b i) .fst) x (k (inr b)))
        ≃⟨ invEquiv (Σ-cong-equiv-fst (UnitToType≃ _)) ⟩
        (Σ[ x' ∈ (Unit → P (inl a') .fst) ]
          ∀ (b : B) → PathP (λ i → P (push a' b i) .fst) (x' tt) (k (inr b)))
        ≃⟨ Σ-cong-equiv-snd (λ x' → equivΠCod (λ b → pathToEquiv (PathP≡Path⁻ _ _ _))) ⟩
        (Σ[ x' ∈ (Unit → P (inl a') .fst) ]
          ∀ (b : B) → x' tt ≡ subst⁻ (λ y → P y .fst) (push a' b) (k (inr b)))
        ≃⟨ Σ-cong-equiv-snd (λ x' → funExtEquiv) ⟩
        (Σ[ x' ∈ (Unit → P (inl a') .fst) ]
          (λ (b : B) → x' tt) ≡
          (λ (b : B) → subst⁻ (λ y → P y .fst) (push a' b) (k (inr b))))
        ■

      X'level : (a' : A') → isOfHLevel m (X' a')
      X'level a' =
        isOfHLevelPrecomposeConnected m n
          (λ (_ : Unit) → P (inl a')) (λ (b : B) → tt)
          (λ _ → isConnectedRetractFromIso _ fiberUnitIso hB) _

      Xl : (a' : A') → TypeOfHLevel _ m
      fst (Xl a') = X a'
      snd (Xl a') = isOfHLevelRespectEquiv _ (invEquiv (X≃X' a')) (X'level a')

      H : Iso ((a' : A') → X a') ((a : A) → X (v a))
      H = elim.isIsoPrecompose v _ Xl hA

      f' : (a' : A') → X a'
      f' = Iso.inv H f

      hf' : (a : A) → f' (v a) ≡ f a
      hf' = funExt⁻ (Iso.rightInv H f)

      k' : (x : join A' B) → P x .fst
      k' (inl a') = f' a' .fst
      k' (inr b) = k (inr b)
      k' (push a' b i) = f' a' .snd b i

      hk' : (x : join A B) → k' (join→ v (idfun B) x) ≡ k x
      hk' (inl a) j = hf' a j .fst
      hk' (inr b) j = k (inr b)
      hk' (push a b i) j = hf' a j .snd b i

    joinConnectedAux :
      hasSection (λ (k : (x : join A' B) → P x .fst) → k ∘ join→ v (idfun B))
    fst joinConnectedAux k = k' k
    snd joinConnectedAux k = funExt (hk' k)

  joinConnected : isConnectedFun (m + n) (join→ v (idfun B))
  joinConnected = elim.isConnectedPrecompose _ _ joinConnectedAux

{- Given two fibration B , C : A → Type and a family of maps on fibres
   f : (a : A) → B a → C a, we have that f a is n-connected for all (a : A)
   iff the induced map on totalspaces Σ A B → Σ A C is n-connected -}
module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
  (f : ((a : A) → B a → C a))
  where
  open Iso

  TotalFun : Σ A B → Σ A C
  TotalFun (a , b) = a , f a b

  fibTotalFun→fibFun : (x : Σ A C)
    → Σ[ y ∈ Σ A B ] TotalFun y ≡ x
    → Σ[ y ∈ B (fst x) ] f (fst x) y ≡ snd x
  fibTotalFun→fibFun x =
    uncurry
      λ r → J (λ x _ → Σ[ y ∈ B (fst x) ] f (fst x) y ≡ snd x)
               ((snd r) , refl)

  fibFun→fibTotalFun : (x : Σ A C)
    → Σ[ y ∈ B (fst x) ] f (fst x) y ≡ snd x
    → Σ[ y ∈ Σ A B ] TotalFun y ≡ x
  fibFun→fibTotalFun x (b , p) = (_ , b) , ΣPathP (refl , p)

  Iso-fibTotalFun-fibFun : (x : Σ A C)
    → Iso (Σ[ y ∈ Σ A B ] TotalFun y ≡ x)
           (Σ[ y ∈ B (fst x) ] f (fst x) y ≡ snd x)
  fun (Iso-fibTotalFun-fibFun x) = fibTotalFun→fibFun x
  inv (Iso-fibTotalFun-fibFun x) = fibFun→fibTotalFun x
  rightInv (Iso-fibTotalFun-fibFun x) (r , y) j =
    transp (λ i → Σ[ b ∈ B (fst x) ] (f (fst x) b ≡ y (i ∨ j))) j
           (r , λ i → y (i ∧ j))
  leftInv (Iso-fibTotalFun-fibFun x) =
    uncurry λ r
      → J (λ x y → inv (Iso-fibTotalFun-fibFun x)
                      (fun (Iso-fibTotalFun-fibFun x) (r , y))
                   ≡ (r , y))
           (cong (fibFun→fibTotalFun (TotalFun r))
             (transportRefl (snd r , refl)))

  TotalFunConnected→FunConnected : (n : ℕ)
    → isConnectedFun n TotalFun
    → ((a : A) → isConnectedFun n (f a))
  TotalFunConnected→FunConnected n con a r =
    isConnectedRetractFromIso n
     (invIso (Iso-fibTotalFun-fibFun (a , r))) (con (a , r))

  FunConnected→TotalFunConnected : (n : ℕ)
    → ((a : A) → isConnectedFun n (f a))
    → isConnectedFun n TotalFun
  FunConnected→TotalFunConnected n con r =
    isConnectedRetractFromIso n
     (Iso-fibTotalFun-fibFun r) (con (fst r) (snd r))

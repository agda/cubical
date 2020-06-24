{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Homotopy.Connected where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Data.Nat
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn.Base
open import Cubical.Data.Unit

-- Note that relative to most sources, this notation is off by +2
isConnected : ∀ {ℓ} (n : HLevel) (A : Type ℓ) → Type ℓ
isConnected n A = isContr (hLevelTrunc n A)

isConnectedFun : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isConnectedFun n f = ∀ b → isConnected n (fiber f b)

isTruncatedFun : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isTruncatedFun n f = ∀ b → isOfHLevel n (fiber f b)

isConnectedSubtr : ∀ {ℓ} {A : Type ℓ} (n m : HLevel)
                → isConnected (m + n) A
                → isConnected n A
isConnectedSubtr {A = A} n m iscon =
  transport (λ i → isContr (ua (truncOfTruncEq {A = A} n m) (~ i)))
             (∣ iscon .fst ∣ , Trunc.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → cong ∣_∣ (iscon .snd a))

isConnectedFunSubtr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : HLevel) (f : A → B)
                → isConnectedFun (m + n) f
                → isConnectedFun n f
isConnectedFunSubtr n m f iscon b = isConnectedSubtr n m (iscon b)

private
  typeToFiber : ∀ {ℓ} (A : Type ℓ) → A ≡ fiber (λ (x : A) → tt) tt
  typeToFiber A = isoToPath typeToFiberIso
    where
    typeToFiberIso : Iso A (fiber (λ (x : A) → tt) tt)
    Iso.fun typeToFiberIso x = x , refl
    Iso.inv typeToFiberIso = fst
    Iso.rightInv typeToFiberIso b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
    Iso.leftInv typeToFiberIso a = refl


module elim {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (n : HLevel) where

  isIsoPrecompose : ∀ {ℓ'''} (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → Iso ((b : B) → P b .fst) ((a : A) → P (f a) .fst)
  isIsoPrecompose P fConn =
      (iso (_∘ f)
        (λ t b → inv t b (fConn b .fst))
        (λ t → funExt λ a →
          cong (inv t (f a)) (fConn (f a) .snd ∣ a , refl ∣)
          ∙ substRefl {B = fst ∘ P} (t a))
        (λ s → funExt λ b →
          Trunc.elim
            {B = λ d → inv (s ∘ f) b d ≡ s b}
            (λ _ → isOfHLevelPath n (P b .snd) _ _)
            (λ {(a , p) i → transp (λ j → P (p (j ∨ i)) .fst) i (s (p i))})
            (fConn b .fst)))
       where
    inv : ((a : A) → P (f a) .fst) → (b : B) → hLevelTrunc n (fiber f b) → P b .fst
    inv t b =
      Trunc.rec
        (P b .snd)
        (λ {(a , p) → subst (fst ∘ P) p (t a)})

  isEquivPrecompose : ∀ {ℓ'''} (P : B → TypeOfHLevel ℓ''' n)
                   → isConnectedFun n f
                   → isEquiv (λ(s : (b : B) → P b .fst) → s ∘ f)
  isEquivPrecompose P fConn = isoToIsEquiv (isIsoPrecompose P fConn)

  isConnectedPrecompose : ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
                                    → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                       → isConnectedFun n f
  isConnectedPrecompose P→sect b = c n P→sect b , λ y →  sym (fun n P→sect b y) -- (c n P→sect b) , λ y → sym (fun n P→sect b y)
    where
    P : (n : HLevel) → ((P : B → TypeOfHLevel ℓ n)
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
     → B → Type _
    P n s b = hLevelTrunc n (fiber f b)

    c : (n : HLevel) → ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
     → hLevelTrunc n (fiber f b)
    c n s = (s λ b → (hLevelTrunc n (fiber f b) , isOfHLevelTrunc _)) .fst
              λ a → ∣ a , refl ∣

    fun : (n : HLevel) (P→sect : ((P : B → TypeOfHLevel (ℓ-max ℓ ℓ') n)
                     → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
      → (b : B) (w : (hLevelTrunc n (fiber f b)))
      → w ≡ c n P→sect b
    fun zero P→sect b w = isOfHLevelSuc zero (isOfHLevelTrunc _) w (c zero P→sect b)
    fun (suc n) P→sect b = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) x (c (suc n) P→sect b))
                                 λ a → transport eqtyp c* b (fst a) (snd a)
        where
        eqtyp : ((a : A) → ∣ (a , refl {x = f a}) ∣
                          ≡ c (suc n) P→sect (f a))
              ≡ ((b : B) (a : A) (p : f (a) ≡ b) → ∣ (a , p) ∣
                                                  ≡ c (suc n) P→sect b)
        eqtyp =
            isoToPath
              (iso (λ g b a → J (λ b p → ∣ a , p ∣ ≡ c (suc n) P→sect b) (g a))
                   (λ g a → g (f a) a refl)
                   (λ h i b a p → (J (λ b x → (J (λ b₂ p → ∣ a , p ∣ ≡ c (suc n) P→sect b₂)
                                                   (h (f a) a (λ _ → f a)) x ≡ h b a x))
                                      (JRefl (λ b₂ p → ∣ a , p ∣ ≡ c (suc n) P→sect b₂) (h (f a) a (λ _ → f a))))
                                    p i)
                   λ h i a p → JRefl (λ b₁ p → ∣ a , p ∣ ≡ c (suc n) P→sect b₁) (h a) i p)
        c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c (suc n) P→sect (f a))
        c* a = sym (cong (λ x → x a) (P→sect (λ b → hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _) .snd λ a → ∣ a , refl ∣))

isOfHLevelPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (k : HLevel) (n : HLevel)
  {A : Type ℓ} {B : Type ℓ'} (P : B → TypeOfHLevel ℓ'' (k + n)) (f : A → B)
  → isConnectedFun n f
  → isOfHLevelFun k (λ(s : (b : B) → P b .fst) → s ∘ f)
isOfHLevelPrecomposeConnected zero n P f fConn =
  elim.isEquivPrecompose f n P fConn .equiv-proof
isOfHLevelPrecomposeConnected (suc k) n P f fConn t =
    isOfHLevelPath'⁻ k
      (λ {(s₀ , p₀) (s₁ , p₁) →
        subst (isOfHLevel k) (sym (fiber≡ (s₀ , p₀) (s₁ , p₁)))
          (isOfHLevelRetract k
            (λ {(q , α) → (funExt⁻ q) , (cong funExt⁻ α)})
            (λ {(h , β) → (funExt h) , (cong funExt β)})
            (λ _ → refl)
            (isOfHLevelPrecomposeConnected k n
              (λ b → (s₀ b ≡ s₁ b) , isOfHLevelPath' (k + n) (P b .snd) _ _)
              f fConn
              (funExt⁻ (p₀ ∙∙ refl ∙∙ sym p₁))))})

indMapEquiv→conType : ∀ {ℓ} {A : Type ℓ} (n : HLevel)
                   → ((B : TypeOfHLevel ℓ n)
                      → isEquiv (λ (b : (fst B)) → λ (a : A) → b))
                   → isConnected n A
indMapEquiv→conType {A = A} n BEq =
  transport (λ i → isContr (hLevelTrunc n (typeToFiber A (~ i))))
            (elim.isConnectedPrecompose (λ _ → tt) n
                                        (λ P → isEquiv→hasSection ((compEquiv ((λ Q → Q tt) , isoToIsEquiv (helper P))
                                                                              (_ , BEq (P tt)) .snd )))
                                        tt)
  where
  helper : ∀ {ℓ'} (P : Unit → TypeOfHLevel ℓ' n)
         → Iso ((b : Unit) → fst (P b)) (fst (P tt))
  Iso.fun (helper P) = λ Q → Q tt
  Iso.inv (helper P) = λ a _ → a
  Iso.rightInv (helper P) b = refl
  Iso.leftInv (helper P) b = refl

isConnectedPath : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isConnected (suc n) A
  → (a₀ a₁ : A) → isConnected n (a₀ ≡ a₁)
isConnectedPath n connA a₀ a₁ =
  subst isContr (PathIdTrunc _)
    (isContr→isContrPath connA _ _)

isConnectedRetract : ∀ {ℓ ℓ'} (n : HLevel)
  {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isConnected n B → isConnected n A
isConnectedRetract n f g h =
  isContrRetract
    (Trunc.map f)
    (Trunc.map g)
    (Trunc.elim
      (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      (λ a → cong ∣_∣ (h a)))

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

connectedTruncIso : ∀ {ℓ} {A B : Type ℓ} (n : HLevel) (f : A → B)
                   → isConnectedFun n f
                   → Iso (hLevelTrunc n A) (hLevelTrunc n B)
connectedTruncIso {A = A} {B = B} zero f con = g
  where
  g : Iso (hLevelTrunc zero A) (hLevelTrunc zero B)
  Iso.fun g = λ _ → fst (isOfHLevelTrunc 0)
  Iso.inv g = λ _ → fst (isOfHLevelTrunc 0)
  Iso.rightInv g = λ b → isOfHLevelTrunc 0 .snd b
  Iso.leftInv g = λ b → isOfHLevelTrunc 0 .snd b
connectedTruncIso {A = A} {B = B} (suc n) f con = g
  where
  back : B → hLevelTrunc (suc n) A
  back y = map fst ((con y) .fst)

  backSection :  (b : B) → Path (hLevelTrunc (suc n) B)
                                 (Trunc.rec (isOfHLevelTrunc (suc n))
                                            (λ a → ∣ f a ∣)
                                            (Trunc.rec {n = suc n }
                                                       {B = hLevelTrunc (suc n) A} (isOfHLevelTrunc (suc n)) back ∣ b ∣))
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

  backRetract : (a : A) → map fst (con (f a) .fst) ≡ ∣ a ∣
  backRetract a = cong (map fst) (con (f a) .snd ∣ a , refl ∣)

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


-- TODO : Reorganise the following proofs.

inrConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : HLevel)
            → (f : C → A) (g : C → B)
            → isConnectedFun n f
            → isConnectedFun n {A = B} {B = Pushout f g} inr
inrConnected {A = A} {B = B} {C = C} n f g iscon =
  elim.isConnectedPrecompose inr n λ P → (λ  l → k P l) , λ b → refl
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

sphereConnected : (n : HLevel) → isConnected (suc n) (S₊ n)
sphereConnected zero = ∣ north ∣ , isOfHLevelTrunc 1 ∣ north ∣
sphereConnected (suc n) =
  transport (λ i → isConnected (2 + n) (PushoutSusp≡Susp {A = S₊ n} i))
            (isConnectedPoint2 (suc n)
                                     {A = Pushout {A = S₊ n} (λ _ → tt) λ _ → tt}
                                     (inr tt)
                                     ((transport (λ i → isConnectedFun (suc n) (mapsAgree (~ i)))
                                                 (inrConnected _ (λ _ → tt) (λ _ → tt)
                                                               λ {tt → transport (λ i → isContr (hLevelTrunc (suc n) (fibId (S₊ n) (~ i))))
                                                                                  (sphereConnected n)}))))
  where
  mapsAgree : Path ((x : Unit) → Pushout {A = S₊ n} (λ x → tt) (λ x → tt))
                   (λ (x : Unit) → inr tt)
                   inr
  mapsAgree = funExt λ _ → refl

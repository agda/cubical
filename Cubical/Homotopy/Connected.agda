{-# OPTIONS --safe #-}
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
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec)
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.S1
open import Cubical.Data.Bool
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
  isOfHLevelRetractFromIso 0 (truncOfTruncIso n m) (helper n iscon)
  where
  helper : (n : ℕ) → isConnected (m + n) A → isContr (hLevelTrunc n (hLevelTrunc (m + n) A))
  helper zero iscon = isContrUnit*
  helper (suc n) iscon = ∣ iscon .fst ∣ , (Trunc.elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → cong ∣_∣ (iscon .snd a))


isConnectedFunSubtr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : HLevel) (f : A → B)
                → isConnectedFun (m + n) f
                → isConnectedFun n f
isConnectedFunSubtr n m f iscon b = isConnectedSubtr n m (iscon b)

private
  typeToFiberIso : ∀ {ℓ} (A : Type ℓ) → Iso A (fiber (λ (x : A) → tt) tt)
  Iso.fun (typeToFiberIso A) x = x , refl
  Iso.inv (typeToFiberIso A) = fst
  Iso.rightInv (typeToFiberIso A) b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
  Iso.leftInv (typeToFiberIso A) a = refl

  typeToFiber : ∀ {ℓ} (A : Type ℓ) → A ≡ fiber (λ (x : A) → tt) tt
  typeToFiber A = isoToPath (typeToFiberIso A)



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
  isIsoPrecompose zero P fConn = isContr→Iso (isOfHLevelΠ _ (λ b → P b .snd)) (isOfHLevelΠ _ λ a → P (f a) .snd)
  Iso.fun (isIsoPrecompose (suc n) P fConn) = _∘ f
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

indMapEquiv→conType : ∀ {ℓ} {A : Type ℓ} (n : HLevel)
                   → ((B : TypeOfHLevel ℓ n)
                      → isEquiv (λ (b : (fst B)) → λ (a : A) → b))
                   → isConnected n A
indMapEquiv→conType {A = A} zero BEq = isContrUnit*
indMapEquiv→conType {A = A} (suc n) BEq =
  isOfHLevelRetractFromIso 0 (mapCompIso {n = (suc n)} (typeToFiberIso A))
    (elim.isConnectedPrecompose (λ _ → tt) (suc n)
                                (λ P → ((λ a _ → a) ∘ invIsEq (BEq (P tt)))
                               , λ a → equiv-proof (BEq (P tt)) a .fst .snd)
                                tt)

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

{-# OPTIONS --cubical --safe #-}
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

open import Cubical.Data.NatMinusTwo.Base

isHLevelConnected : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
isHLevelConnected n A = isContr (hLevelTrunc n A)

isHLevelConnectedFun : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHLevelConnectedFun n f = ∀ b → isHLevelConnected n (fiber f b)

isHLevelTruncatedFun : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHLevelTruncatedFun n f = ∀ b → isOfHLevel n (fiber f b)

isConnectedSubtr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : A → B)
                → isHLevelConnectedFun (m + n) f
                → isHLevelConnectedFun n f
isConnectedSubtr n m f iscon b =
  transport (λ i → isContr (ua (truncOfTruncEq {A = fiber f b} n m) (~ i) ))
            (∣ iscon b .fst ∣ ,
              Trunc.elim (λ x → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
                     λ a → cong ∣_∣ (iscon b .snd a))

private
  typeToFiber : ∀ {ℓ} (A : Type ℓ)  (b : Unit) → A ≡ fiber (λ (x : A) → b) b
  typeToFiber A tt = isoToPath typeToFiberIso
    where
    typeToFiberIso : Iso A (fiber (λ (x : A) → tt) tt)
    Iso.fun typeToFiberIso x = x , refl
    Iso.inv typeToFiberIso = fst
    Iso.rightInv typeToFiberIso b i = fst b , (isOfHLevelSuc 1 (isPropUnit) tt tt (snd b) refl) i
    Iso.leftInv typeToFiberIso a = refl


module elim {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (n : ℕ) where

  isIsoPrecompose : ∀ {ℓ'''} (P : B → HLevel ℓ''' n)
                   → isHLevelConnectedFun n f
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

  isEquivPrecompose : ∀ {ℓ'''} (P : B → HLevel ℓ''' n)
                   → isHLevelConnectedFun n f
                   → isEquiv λ(s : (b : B) → P b .fst) → s ∘ f
  isEquivPrecompose P fConn = isoToIsEquiv (isIsoPrecompose P fConn)

  isConnectedPrecompose : ((∀ {ℓ'''} (P : B → HLevel ℓ''' n)
                                  → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
                       → isHLevelConnectedFun n f
  isConnectedPrecompose P→sect b = (c n P→sect b) , λ y → sym (fun n P→sect b y)
    where
    P : (n : ℕ) → (∀ {ℓ} (P : B → HLevel ℓ n)
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
     → B → Type _
    P n s b = hLevelTrunc n (fiber f b)

    c : (n : ℕ) → (∀ {ℓ} (P : B → HLevel ℓ n)
     → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
     → hLevelTrunc n (fiber f b)
    c n s = (s λ b → (hLevelTrunc n (fiber f b) , isOfHLevelTrunc _)) .fst
              λ a → ∣ a , refl ∣

    fun : (n : ℕ) (s : (∀ {ℓ} (P : B → HLevel ℓ n)
      → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
      → (b : B) (w : (hLevelTrunc n (fiber f b)))
      → w ≡ c n s b
    fun zero s b w = isOfHLevelSuc zero (isOfHLevelTrunc _) w (c zero s b)
    fun (suc n) s b = Trunc.elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc _) x (c (suc n) s b))
                                 λ a → transport eqtyp c* b (fst a) (snd a)
        where
        eqtyp : ((a : A) → ∣ (a , refl {x = f a}) ∣
                          ≡ c (suc n) s (f a))
              ≡ ((b : B) (a : A) (p : f (a) ≡ b) → ∣ (a , p) ∣
                                                  ≡ c (suc n) s b)
        eqtyp =
            isoToPath
              (iso (λ g b a → J (λ b p → ∣ a , p ∣ ≡ c (suc n) s b) (g a))
                   (λ g a → g (f a) a refl)
                   (λ h i b a p → (J (λ b x → (J (λ b₂ p → ∣ a , p ∣ ≡ c (suc n) s b₂)
                                                   (h (f a) a (λ _ → f a)) x ≡ h b a x))
                                      (JRefl (λ b₂ p → ∣ a , p ∣ ≡ c (suc n) s b₂) (h (f a) a (λ _ → f a))))
                                    p i)
                   λ h i a p → JRefl (λ b₁ p → ∣ a , p ∣ ≡ c (suc n) s b₁) (h a) i p)
        c* : ((a : A) → ∣ (a , refl {x = f a}) ∣ ≡ c (suc n) s (f a))
        c* a = sym (cong (λ x → x a) (s (λ b → hLevelTrunc (suc n) (fiber f b) , isOfHLevelTrunc _) .snd λ a → ∣ a , refl ∣))

isOfHLevelPrecomposeConnected : ∀ {ℓ ℓ' ℓ''} (k : ℕ) (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'} (P : B → HLevel ℓ'' (k + n)) (f : A → B)
  → isHLevelConnectedFun n f
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

indMapEquiv→conType : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → (∀ {ℓ'} (B : HLevel ℓ' n)
                     → isEquiv (λ (b : (fst B)) → λ (a : A) → b)) → isHLevelConnected n A
indMapEquiv→conType {A = A} n BEq =
  transport (λ i → isContr (hLevelTrunc n (typeToFiber A tt (~ i))))
            (elim.isConnectedPrecompose (λ _ → tt) n
                                        (λ {ℓ'} P → isEquiv-hasSection _ (compEquiv ((λ Q → Q tt) , isoToIsEquiv (helper P))
                                                                                     (_ , BEq (P tt)) .snd ))
                                        tt)
  where
  helper : ∀ {ℓ'} (P : Unit → HLevel ℓ' n)
         → Iso ((b : Unit) → fst (P b)) (fst (P tt))
  Iso.fun (helper P) = λ Q → Q tt
  Iso.inv (helper P) = λ a → λ {tt → a}
  Iso.rightInv (helper P) b = refl
  Iso.leftInv (helper P) b = refl

isHLevelConnectedPath : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a₀ a₁ : A) → isHLevelConnected n (a₀ ≡ a₁)
isHLevelConnectedPath n connA a₀ a₁ =
  subst isContr (PathIdTrunc _)
    (isContr→isContrPath connA _ _)

isHLevelConnectedRetract : ∀ {ℓ ℓ'} (n : ℕ)
  {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isHLevelConnected n B → isHLevelConnected n A
isHLevelConnectedRetract n f g h =
  isContrRetract
    (Trunc.map f)
    (Trunc.map g)
    (Trunc.elim
      (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      (λ a → cong ∣_∣ (h a)))

isHLevelConnectedPoint : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isHLevelConnected (suc n) A
  → (a : A) → isHLevelConnectedFun n (λ(_ : Unit) → a)
isHLevelConnectedPoint n connA a₀ a =
  isHLevelConnectedRetract n
    snd (_ ,_) (λ _ → refl)
    (isHLevelConnectedPath n connA a₀ a)


isHLevelConnectedPoint2 : ∀ {ℓ} (n : ℕ) {A : Type ℓ} (a : A)
   → isHLevelConnectedFun n (λ(_ : Unit) → a)
   → isHLevelConnected (suc n) A
isHLevelConnectedPoint2 n {A = A} a connMap = indMapEquiv→conType _ λ B → isoToIsEquiv (theIso B)
  where
  module _  {ℓ' : Level} (B : HLevel ℓ' (suc n))
    where
    helper : (f : A → fst B) → (a2 : A) → f a2 ≡ f a
    helper f = equiv-proof (elim.isEquivPrecompose (λ _ → a) n (λ a2 → (f a2 ≡ f a) ,
                             isOfHLevelPath' n (snd B) (f a2) (f a)) connMap) (λ _ → refl) .fst .fst

    theIso : Iso (fst B) (A → fst B)
    Iso.fun theIso b a = b
    Iso.inv theIso f = f a
    Iso.rightInv theIso f = funExt λ y → sym (helper f y)
    Iso.leftInv theIso _ = refl

connectedTruncIso : ∀ {ℓ} {A B : Type ℓ} (n : ℕ) (f : A → B)
                   → isHLevelConnectedFun n f
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

connectedTruncIso2 : ∀ {ℓ} {A B : Type ℓ} (n m : ℕ) (f : A → B)
                   → Σ[ x ∈ ℕ ] x + n ≡ m
                   → isHLevelConnectedFun m f
                   → Iso (hLevelTrunc n A) (hLevelTrunc n B)
connectedTruncIso2 {A = A} {B = B} n m f (x , pf) con =
  connectedTruncIso n f (isConnectedSubtr n x f (transport (λ i → isHLevelConnectedFun (pf (~ i)) f) con))

connectedTruncEquiv : ∀ {ℓ} {A B : Type ℓ} (n : ℕ) (f : A → B)
                   → isHLevelConnectedFun n f
                   → hLevelTrunc n A ≃ hLevelTrunc n B
connectedTruncEquiv {A = A} {B = B} n f con = isoToEquiv (connectedTruncIso n f con)

inrConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : ℕ)
            → (f : C → A) (g : C → B)
            → isHLevelConnectedFun n f
            → isHLevelConnectedFun n {A = B} {B = Pushout f g} inr
inrConnected {A = A} {B = B} {C = C} n f g iscon =
  elim.isConnectedPrecompose inr n λ P → (λ  l → k P l) , λ b → refl
  where
  module _ {ℓ : Level} (P : (Pushout f g) → HLevel ℓ n)
                   (h : (b : B) → typ (P (inr b)))
    where
    Q : A → HLevel _ n
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

sphereConnected : (n : ℕ) → isHLevelConnected (suc n) (S₊ n)
sphereConnected zero = ∣ north ∣ , isOfHLevelTrunc 1 ∣ north ∣
sphereConnected (suc n) =
  transport (λ i → isHLevelConnected (2 + n) (PushoutSusp≡Susp {A = S₊ n} i))
            (isHLevelConnectedPoint2 (suc n)
                                     {A = Pushout {A = S₊ n} (λ _ → tt) λ _ → tt}
                                     (inr tt)
                                     ((transport (λ i → isHLevelConnectedFun (suc n) (mapsAgree (~ i)))
                                                 (inrConnected _ (λ _ → tt) (λ _ → tt)
                                                               λ {tt → transport (λ i → isContr (hLevelTrunc (suc n) ((isoToPath fibIso) (~ i))))
                                                                                  (sphereConnected n)}))))
  where
  mapsAgree : Path ((x : Unit) → Pushout {A = S₊ n} (λ x → tt) (λ x → tt))
                   (λ (x : Unit) → inr tt)
                   inr
  mapsAgree = funExt λ {tt → refl}

  fibIso : Iso (fiber (λ (x : S₊ n) → tt) tt) (S₊ n)
  Iso.fun (fibIso) = fst
  Iso.inv (fibIso) a = a , refl
  Iso.leftInv (fibIso) b = refl
  Iso.rightInv (fibIso) b = refl


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ
    B' : Pointed ℓ'
    C' : Pointed ℓ''



-- isConnectedSmashIdfun2 : {A B C : Pointed₀}
--                       → (f : A →∙ B) (nf nc : ℕ)
--                       → isHLevelConnectedFun nf (fst f)
--                       → isHLevelConnected (2 + nc) (fst C)
--                       → isHLevelConnectedFun (1 + nc + nf) (Smash-map f (idfun∙ C))
-- isConnectedSmashIdfun2 {A = A , ptA} {B = B , ptB} {C = C , ptC} (f , fpt) nf nc conf conC = λ b → {!!} , {!!}
--   where
--   module proof {ℓ : Level} (P : (Smash (B , ptB) (C , ptC)) → HLevel ℓ (1 + nc + nf))
--            (d : (x : Smash (A , ptA) (C , ptC)) → P ((Smash-map (f , fpt) (idfun∙ (C , ptC)) ) x) .fst)
--     where
--     F : (c : C) → _
--     F c = λ(s : (b : B) → P (proj b  c) .fst) → s ∘ f

--     step1 : (c : C) → isHLevelTruncatedFun (1 + nc) (F c)
--     step1 c = isOfHLevelPrecomposeConnected (1 + nc) nf ((λ b → P (proj b  c) .fst , P (proj b c) .snd)) f conf

--     codomFun : (c : C) (a : A) → P (proj (f a)  c) .fst
--     codomFun c = d ∘ λ a → proj a c

--     Q : C → HLevel _ (1 + nc)
--     Q c = fiber (F c) (codomFun c) , step1 c _


--     helper : (a : A) → transport (λ i → P (gluel (f a) (~ i)) .fst) (d (basel))
--                      ≡ d (proj a ptC)
--     helper a = transport (PathP≡Path (λ i → P (gluel (f a) (~ i)) .fst) (d basel) (d (proj a ptC)))
--                          (transport (λ j → PathP (λ i → P (lUnit (gluel (f a)) (~ j) (~ i)) .fst) (d basel) (d (proj a ptC)))
--                                     λ i → d (gluel a (~ i)))

--     QptC : Q ptC .fst
--     QptC = (λ b → transport (λ i → P (gluel b (~ i)) .fst) (d basel)) ,
--            funExt helper


--     Q-constructor : (c : C) → Q c .fst
--     Q-constructor c = Iso.inv (elim.isIsoPrecompose (λ (_ : Unit) → ptC) (1 + nc) Q (isHLevelConnectedPoint _ conC ptC)) (λ _ → QptC) c

--     g : (b : B) (c : C) → P (proj b c) .fst
--     g b c = Q-constructor c .fst b

--     Q-constructor-β : (b : B) → Q-constructor ptC .fst b ≡ transport (λ i → P (gluel b (~ i)) .fst) (d basel)
--     Q-constructor-β b = ((λ i → (Trunc.rec (Q ptC .snd) (λ { (a , p) → subst (fst ∘ Q) p QptC}) (helper3 i)) .fst b)) ∙
--                         (λ i → transportRefl (QptC) i .fst b)

--       where
--       helper3 : (isHLevelConnectedPoint _ conC ptC) ptC .fst ≡ ∣ tt , refl ∣
--       helper3 = (isHLevelConnectedPoint _ conC ptC) ptC .snd ∣ tt , refl ∣

--     moveTransport : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) (x1 : B x) (y1 : B y)
--                   → transport (λ i → (B (p i))) x1 ≡ y1
--                   → transport⁻ (λ i → (B (p i))) y1 ≡ x1
--     moveTransport {B = B} p x1 y1 transp = ((λ i → transport⁻ (λ i → B (p i)) (transp (~ i))) ∙ (transport⁻Transport (λ i → B (p i)) x1))

--     otherway : (b : B) → transport (λ i → P (gluel b i) .fst) (g b ptC) ≡ d basel
--     otherway b = (λ i → transport (λ i → P (gluel b i) .fst) (Q-constructor-β b i)) ∙ transportTransport⁻ (λ i → P (gluel b i) .fst) (d basel)

--     path1 : (b : B) → PathP (λ i → P (gluel b i) .fst) (g b ptC) (d basel)
--     path1 b i = hcomp (λ k → λ {(i = i0) → g b ptC
--                                ; (i = i1) → otherway b k})
--                       (transp (λ j → P (gluel b (i ∧ j)) .fst) (~ i) (g b ptC))


--       where
--     massive : (c : C) → PathP _ (g ptB c) (d baser)
--     massive c = compPathP (λ i → g (fpt (~ i)) c) (compPathP (λ i → Q-constructor c .snd i (ptA)) (λ i → d (gluer c i)))

--     pathPCancel : (c : C)
--                 → ((λ z → P (proj (fpt (~ z)) c) .fst) ∙ (λ i → ((λ _ → P (proj (f ptA) c) .fst) ∙ (λ i₁ → P (((λ j₁ → proj (fpt j₁) c) ∙ gluer c) i₁) .fst)) i))
--                 ≡ (λ i → P (gluer c i) .fst)
--     pathPCancel c = (λ i → (λ z → P (proj (fpt (~ z)) c) .fst) ∙ lUnit ((λ i₁ → P (((λ j₁ → proj (fpt j₁) c) ∙ gluer c) i₁) .fst)) (~ i))
--                   ∙ (λ i → (λ z → P (proj (fpt (~ z ∨ i)) c) .fst) ∙ λ i₁ → P (((λ j₁ → proj (fpt (j₁ ∨ i)) c) ∙ gluer c) i₁) .fst )
--                   ∙ (λ i → lUnit (λ i₁ → P (lUnit (gluer c) (~ i) i₁) .fst) (~ i))

--     path2 : (c : C) → PathP (λ i → P (gluer c i) .fst) (g ptB c) (d baser)
--     path2 c = transport (λ i → PathP (λ j → pathPCancel c i j) (g ptB c) (d baser)) (massive c)

--     h : (x : Smash (B , ptB) (C , ptC)) → P x .fst
--     h basel = d basel
--     h baser = d baser
--     h (proj x y) = g x y
--     h (gluel b i) = {!!} -- path1 b i
--     h (gluer c i) = {!!} -- path2 c i

--     hsection : (x : Smash (A , ptA) (C , ptC)) → h (Smash-map (f , fpt) (idfun∙ (C , ptC)) x) ≡ d x
--     hsection basel = refl
--     hsection baser = refl
--     hsection (proj x y) i = Q-constructor y .snd i x
--     hsection (gluel a i) j = hcomp (λ k → λ { (i = i0) → transportRefl {!!} k
--                                               ; (i = i1) → transportRefl (d basel) k
--                                               ; (j = i0) → {!!}
--                                               ; (j = i1) → {!!}})
--                                    {!hcomp!} -- hcomp {!!} {!!}
--       where

--       helper2 :  Path ((P (proj (f a) ptC) .fst) ≡ (P basel .fst))
--                       (λ i → P (Smash-map (f , fpt) (idfun∙ (C , ptC)) (gluel a i)) .fst)
--                       λ i → P (gluel (f a) i) .fst
--       helper2 = (λ j i → P ((lUnit (gluel (f a)) (~ j)) i) .fst)
--       helper6 : (a : A) → PathP ((λ j → PathP (λ i → P {!Q-constructor ? .snd i ?!} .fst) {!P (proj (f a) ptC) .fst!} {!!})) (λ i → h (Smash-map (f , fpt) (idfun∙ (C , ptC)) (gluel a i))) (path1 (f a))
--       helper6 a = ((λ j i → h ((lUnit (gluel (f a)) (~ j)) i)))

--       helper3 : PathP {!!} (path1 (f a)) (λ i → d (gluel a i))
--       helper3 = compPathP {!!} {!!}
--       helper4 : PathP {!!} (path1 (f a)) λ i → d (gluel a i)
--       helper4 = {!!}
--     hsection (gluer b i) = {!!}



-- -- isConnectedSmashIdfun : (f : A' →∙ B') (nf nc : ℕ)
-- --                     → isHLevelConnectedFun nf (fst f)
-- --                     → isHLevelConnected (2 + nc) (fst C')
-- --                     → isHLevelConnectedFun (1 + nf + nc) (f ⋀⃗ idfun∙ C')
-- -- isConnectedSmashIdfun {A' = (A , ptA)} {B' = (B , ptB)} {C' = (C , ptC)} (f , fpt) nf nc conf conC = {!isHLel!}
-- --   where
-- --   module _ (P : ((B , ptB) ⋀ (C , ptC)) → HLevel (ℓ-max (ℓ-max ℓ ℓ') ℓ'') (1 + nc + nf))
-- --            (d : (x : (A , ptA) ⋀ (C , ptC)) → P (((f , fpt) ⋀⃗ idfun∙ (C , ptC) ) x) .fst)
-- --             where
-- --     F : (c : C) → _
-- --     F c = λ(s : (b : B) → P (inr (b , c)) .fst) → s ∘ f

-- --     step1 : (c : C) → isHLevelTruncatedFun (1 + nc) (F c)
-- --     step1 c = isOfHLevelPrecomposeConnected (1 + nc) nf ((λ b → P (inr (b , c)) .fst , P (inr (b , c)) .snd)) f conf

-- --     codomFun : (c : C) (a : A) → P (inr ((f a) , c)) .fst
-- --     codomFun c = d ∘ λ a → inr (a , c)

-- --     Q : C → HLevel _ (1 + nc)
-- --     Q c = fiber (F c) (codomFun c) , step1 c _


-- --     helper : (a : A) → transport (λ i → P (push (inl (f a)) i) .fst) (d (inl tt))
-- --                      ≡ d (inr (a , ptC))
-- --     helper a = transport (PathP≡Path (λ i → P (push (inl (f a)) i) .fst) (d (inl tt)) (d (inr (a , ptC))))
-- --                          (transport (λ j → PathP (λ i → P (rUnit (push (inl (f a))) (~ j) i) .fst) (d (inl tt)) (d (inr (a , ptC))))
-- --                          λ i → d (push (inl a) i))


-- --     QptC : Q ptC .fst
-- --     QptC = (λ b → transport (λ i → P (push (inl b) i) .fst) (d (inl tt))) ,
-- --            funExt helper
-- --       where


-- --     Q-constructor : (c : C) → Q c .fst
-- --     Q-constructor c = Iso.inv (elim.isIsoPrecompose (λ _ → ptC) (1 + nc) Q (isHLevelConnectedPoint _ conC ptC)) (λ ( _ : Unit) → QptC) c

-- --     g : (b : B) (c : C) → P (inr (b , c)) .fst
-- --     g b c = Q-constructor c .fst b

-- --     Q-constructor-β : (b : B) → Q-constructor ptC .fst b ≡ transport (λ i → P (push (inl b) i) .fst) (d (inl tt))
-- --     Q-constructor-β b = ((λ i → (Trunc.rec (Q ptC .snd) (λ { (a , p) → subst (fst ∘ Q) p QptC}) (helper3 i)) .fst b)) ∙
-- --                         (λ i → transportRefl (QptC) i .fst b)

-- --       where
-- --       helper3 : (isHLevelConnectedPoint _ conC ptC) ptC .fst ≡ ∣ tt , refl ∣
-- --       helper3 = (isHLevelConnectedPoint _ conC ptC) ptC .snd ∣ tt , refl ∣

-- --     test : (b : B) (c : C) → PathP (λ i → P (push {!!} {!(~ i)!}) .fst) (Q-constructor ptC .fst b) (Q-constructor c .fst ptB)
-- --     test b = {!!}

-- --     Q-constructor-β2 : (c : C) → Q-constructor c .fst ptB ≡ transport (λ i → P (push (inr c) i) .fst) (d (inl tt))
-- --     Q-constructor-β2 c = ((λ i → (Trunc.rec (Q c .snd) (λ { (a , p) → subst (fst ∘ Q) p QptC}) ((isHLevelConnectedPoint _ conC ptC) c .fst)) .fst ptB)) ∙
-- --                           {!isHLevelConnectedPoint _ conC ptC c .fst!}

-- --     gid1 : (a : A) (c : C) → g (f a) c  ≡ d (inr (a , c))
-- --     gid1 a c i = (Q-constructor c .snd) i a

-- --     gid1' : {!!}
-- --     gid1' = {!!}

-- --     gid1Path : (c : C) → PathP (λ i → P (push (inr c) i) .fst) (d (inl tt)) (g ptB c)
-- --     gid1Path c i =
-- --        hcomp (λ k → λ {(i = i0) → {!!} ; (i = i1) → {!!}})
-- --              {!!}

-- --     compPath : (c : C) → PathP _ (d (inl tt)) (g ptB c)
-- --     compPath c = compPathP (λ i → d (push (inr c) i)) (compPathP (sym (gid1 ptA c)) (λ i → g (fpt i) c))


-- --     compPathTransport : (c : C) →  ((λ z → P ((push (inr c) ∙
-- --                                     (λ i → inr (fpt (~ i) , c))) z) .fst) ∙
-- --                                     (λ i → ((λ i₁ → P (inr (f ptA , c)) .fst) ∙ (λ i₁ → P (inr (fpt i₁ , c)) .fst)) i))
-- --                                   ≡ λ i → P (push (inr c) i) .fst
-- --     compPathTransport c = (λ k → ((λ z → P ((push (inr c) ∙
-- --                                     (λ i → inr (fpt (~ i) , c))) z) .fst) ∙
-- --                                     ((lUnit (λ i₁ → P (inr (fpt i₁ , c)) .fst) (~ k) ))))
-- --                            ∙ (λ k →  ((λ z → P ((push (inr c) ∙
-- --                                     (λ i → inr (fpt (~ i ∨ k) , c))) z) .fst) ∙
-- --                                     (λ i₁ → P (inr (fpt (i₁ ∨ k) , c)) .fst) ))
-- --                            ∙ (λ k → ((λ z → P ((push (inr c) ∙ refl) z) .fst) ∙ refl))
-- --                            ∙ (λ k → rUnit ((λ z → P ((rUnit (push (inr c)) (~ k)) z) .fst)) (~ k))

-- --     compPathTransport-ptC : compPathTransport ptC ≡ {!!}
-- --     compPathTransport-ptC = {!!}

-- --     compPathTrue : (c : C) → PathP (λ i → P (push (inr c) i) .fst) (d (inl tt)) (g ptB c)
-- --     compPathTrue c = transport (λ i → PathP (λ j → compPathTransport c i j) (d (inl tt)) (g ptB c)) (compPath c)

-- --     gid1transp : (c : C) → PathP {!!} (g ptB c) (transport (λ i → P (push (inr c) i) .fst) (d (inl tt)))
-- --     gid1transp c = compPathP (λ i → g (fpt (~ i)) c) (compPathP (gid1 ptA c) (compPathP (λ i → d (push (inr c) (~ i))) λ i → transp (λ j → P (push (inr c) (i ∧ j)) .fst) (~ i) (d (inl tt))))


-- --     gid2 : (b : B) → g b ptC ≡ transport (λ i → P (push (inl b) i) .fst) (d (inl tt)) -- (λ i → P (push (inl b) i) .fst) (d (inl tt))
-- --     gid2 b = Q-constructor-β b


-- --     gid1≡gid2 : (c : C) (a : A) → PathP {!gid1transp c !} (gid1 a ptC) (gid2 (f a))
-- --     gid1≡gid2 c a = compPathP {!λ j → (Q-constructor ptC .snd) i a!} (compPathP {!!} {!!})


-- --     gid2Path : (b : B) → PathP (λ i → P (push (inl b) i) .fst) (d (inl tt)) (g b ptC)
-- --     gid2Path b i =
-- --       hcomp (λ k → λ {(i = i0) → (d (inl tt)) ; (i = i1) → gid2 b (~ k)})
-- --             (transp (λ j → P (push (inl b) (j ∧ i)) .fst) (~ i) (d (inl tt)))

-- --     PathP2 : PathP {!!} ((gid2Path ptB)) (compPathTrue ptC)
-- --     PathP2 = compPathP {!gid2Path ptB!} (compPathP {!!} {!compPathTrue ptC!})

-- --     h : (x : (B , ptB) ⋀ (C , ptC)) → P x .fst
-- --     h (inl x) = d (inl tt)
-- --     h (inr (b , c)) = g b c
-- --     h (push (inl b) i) = gid2Path b i
-- --     h (push (inr x) i) = compPathTrue x i
-- --     h (push (push a i₁) i) = {!!}

{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.Tricky where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group renaming (Unit to UnitGr ; Bool to BoolGr)
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.ZAction

open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.LES
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.S2

open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Whitehead

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; map to pMap)

-- We start off with this horrendous but useful lemma for transporting
-- exact sequences
transportExact4 : {ℓ ℓ' ℓ'' ℓ''' : Level}
                  (G G₂ : Group ℓ) (H H₂ : Group ℓ') (L L₂ : Group ℓ'') (R R₂ : Group ℓ''')
               → (G≡G₂ : G ≡ G₂) → (H≡H₂ : H ≡ H₂) (L≡L₂ : L ≡ L₂) (R≡R₂ : R ≡ R₂)
               → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
               → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
               → (L→R : GroupHom L R)
               → Exact4 G H L R G→H H→L L→R
               → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
               → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
               → Σ[ L₂→R₂ ∈ GroupHom L₂ R₂ ]
                   Exact4 G₂ H₂ L₂ R₂ G₂→H₂ H₂→L₂ L₂→R₂
transportExact4 G G₂ H H₂ L L₂ R R₂ =
  J4 (λ G₂ H₂ L₂ R₂ G≡G₂ H≡H₂ L≡L₂ R≡R₂
    → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
               → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
               → (L→R : GroupHom L R)
               → Exact4 G H L R G→H H→L L→R
               → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
               → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
               → Σ[ L₂→R₂ ∈ GroupHom L₂ R₂ ]
                   Exact4 G₂ H₂ L₂ R₂ G₂→H₂ H₂→L₂ L₂→R₂)
     (λ G→H G₂→H₂ H→L H₂→L₂ L→R ex
       → J (λ G₂→H₂ _
          → H→L ≡ H₂→L₂
          → Σ[ L→R ∈ GroupHom L R ]
                   Exact4 G H L R G₂→H₂ H₂→L₂ L→R)
       (J (λ H₂→L₂ _ → Σ[ L→R ∈ GroupHom L R ]
                   Exact4 G H L R G→H H₂→L₂ L→R)
          (L→R , ex)))
     G₂ H₂ L₂ R₂
  where
  abstract
    J4 : ∀ {ℓ ℓ₂ ℓ₃ ℓ₄ ℓ'} {A : Type ℓ}
         {A₂ : Type ℓ₂} {A₃ : Type ℓ₃} {A₄ : Type ℓ₄}
         {x : A} {x₂ : A₂} {x₃ : A₃} {x₄ : A₄}
         (B : (y : A) (z : A₂) (w : A₃) (u : A₄)
         → x ≡ y → x₂ ≡ z → x₃ ≡ w → x₄ ≡ u → Type ℓ')
      → B x x₂ x₃ x₄ refl refl refl refl
      → (y : A) (z : A₂) (w : A₃) (u : A₄)
         (p : x ≡ y) (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u)
      → B y z w u p q r s
    J4 {x = x} {x₂ = x₂} {x₃ = x₃} {x₄ = x₄} B b y z w u =
      J (λ y p → (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u) →
        B y z w u p q r s)
        (J (λ z q → (r : x₃ ≡ w) (s : x₄ ≡ u) → B x z w u refl q r s)
          (J (λ w r → (s : x₄ ≡ u) → B x x₂ w u refl refl r s)
            (J (λ u s → B x x₂ x₃ u refl refl refl s) b)))

-- Move to Base
≃∙→πHom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
        → (A ≃∙ B)
        → (n : ℕ) → GroupEquiv (πGr n A) (πGr n B)
fst (fst (≃∙→πHom e n)) = fst (πHom n (≃∙map e))
snd (fst (≃∙→πHom e n)) =
  isoToIsEquiv (setTruncIso (equivToIso (_ , isEquivΩ^→ (suc n) (≃∙map e) (snd (fst e)))))
snd (≃∙→πHom e n) = snd (πHom n (≃∙map e))

-- Move to connected/loopspace
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
    (help n m (help2 n (suc m)) (isConnectedΩ^→ n (suc m) f conf))
  where
  open import Cubical.Data.Sum
  help2 : (n m : ℕ) → ((suc n ∸ m ≡ suc (n ∸ m))) ⊎ (suc n ∸ suc m ≡ 0)
  help2 n zero = inl refl
  help2 zero (suc m) = inr refl
  help2 (suc n) (suc m) = help2 n m

  help : (n m : ℕ) → ((suc n ∸ (suc m) ≡ suc (n ∸ suc m))) ⊎ (suc n ∸ suc (suc m) ≡ 0)
       → isConnectedFun (suc n ∸ suc m) (fst (Ω^→ (suc m) f))
      → isConnectedFun (suc n ∸ suc (suc m))
          {A = Path ((Ω^ (suc m)) (_ , pt A) .fst)
          refl refl}
          (cong (fst (Ω^→ (suc m) f)))
  help n m (inl x) conf =
    isConnectedCong (n ∸ suc m) (fst (Ω^→ (suc m) f))
      (subst (λ x → isConnectedFun x (fst (Ω^→ (suc m) f))) x conf)
  help n m (inr x) conf =
    subst (λ x → isConnectedFun x (cong {x = refl} {y = refl} (fst (Ω^→ (suc m) f))))
      (sym x)
      λ b → tt* , λ _ → refl

-- check if exists. Move to unit otherwise?
fibreUnitMap : ∀ {ℓ} {A : Type ℓ} → Iso (fiber (λ (a : A) → tt) tt) A
fun fibreUnitMap (x , p) = x
inv fibreUnitMap a = a , refl
rightInv fibreUnitMap _ = refl
leftInv fibreUnitMap _ = refl

W : S₊ 3 → (S₊∙ 2 ⋁ S₊∙ 2)
W = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}
   ∘ Iso.inv (IsoSphereJoin 1 1)

fold∘W : S₊ 3 → S₊ 2
fold∘W = fold⋁ ∘ W

isConnectedS3→S2 : (f : S₊ 3 → S₊ 2) → isConnectedFun 2 f
isConnectedS3→S2 f p =
  trRec (isProp→isOfHLevelSuc 1 isPropIsContr)
    (J (λ p _ → isConnected 2 (fiber f p))
      (∣ north , refl ∣
     , (trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
         (uncurry
           (sphereElim 2
             (λ _ → isOfHLevelΠ 3
               λ _ → isOfHLevelPath 3
                 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
           λ p → trRec (isOfHLevelTrunc 2 _ _)
             (λ r → cong ∣_∣ₕ (ΣPathP (refl , r)))
            (fun (PathIdTruncIso 1)
              (isContr→isProp
                (isConnectedPath 2 (sphereConnected 2)
                  (f north) (f north)) ∣ refl ∣ ∣ p ∣)))))))
    (fun (PathIdTruncIso 2)
      (isContr→isProp (sphereConnected 2) ∣ f north ∣ ∣ p ∣))

module BM-inst =
  BlakersMassey□ (λ _ → tt) fold∘W 3 1
   (λ _ → subst (isConnected 4)
            (isoToPath (invIso fibreUnitMap))
            (sphereConnected 3))
   (isConnectedS3→S2 fold∘W)

open BM-inst

-- The central types
coFib-fold∘W : Type
coFib-fold∘W = Pushout (λ _ → tt) fold∘W

coFib-fold∘W∙ : Pointed₀
coFib-fold∘W∙ = coFib-fold∘W , inl tt

TotalPushoutPath×∙ : Pointed ℓ-zero
fst TotalPushoutPath×∙ = Σ (Unit × S₊ 2) PushoutPath×
snd TotalPushoutPath×∙ = (tt , north) , push north

S³→TotalPushoutPath× : S₊ 3 → Σ (Unit × S₊ 2) PushoutPath×
S³→TotalPushoutPath× = toPullback

private
  inr' : S₊ 2 → coFib-fold∘W
  inr' = inr

  inr∙ : S₊∙ 2 →∙ coFib-fold∘W∙
  fst inr∙ = inr'
  snd inr∙ = sym (push north)

  fibreinr'Iso : Iso (fiber inr' (inl tt)) (Σ (Unit × S₊ 2) PushoutPath×)
  fun fibreinr'Iso (x , p) = (tt , x) , (sym p)
  inv fibreinr'Iso ((tt , x) , p) = x , (sym p)
  rightInv fibreinr'Iso _ = refl
  leftInv fibreinr'Iso _ = refl

  P : Pointed₀
  P = (fiber inr' (inl tt) , north , (sym (push north)))

π'P→π'TotalPath× : (n : ℕ)
  → GroupEquiv (π'Gr n TotalPushoutPath×∙) (π'Gr n P)
fst (fst (π'P→π'TotalPath× n)) =
  π'eqFun n ((invEquiv (isoToEquiv fibreinr'Iso)) , refl)
snd (fst (π'P→π'TotalPath× n)) = π'eqFunIsEquiv n _
snd (π'P→π'TotalPath× n) = π'eqFunIsHom n _

-- Time to invoke the long exact sequence of homotopy groups on
-- inr∙ : S² →∙ coFib-fold∘W∙
module LESinst = πLES {A = S₊∙ 2} {B = coFib-fold∘W∙} inr∙

-- Π₂ is trivial for the fibres
π₂P≅0 : GroupEquiv (πGr 1 P) UnitGr
π₂P≅0 = compGroupEquiv (≃∙→πHom (isoToEquiv fibreinr'Iso , refl) 1)
         (GroupIso→GroupEquiv
           (contrGroupIsoUnit (isOfHLevelRetractFromIso 0 (invIso map23) isContrπ₂S³)))
  where
  mapp : Iso (hLevelTrunc 4 (S₊ 3)) (hLevelTrunc 4 (Σ (Unit × S₊ 2) PushoutPath×))
  mapp = connectedTruncIso 4 S³→TotalPushoutPath× isConnected-toPullback

  map23 : Iso (π 2 (hLevelTrunc∙ 4 (S₊∙ 3))) (π 2 TotalPushoutPath×∙)
  map23 =
    (compIso (setTruncIso
      (equivToIso (_ ,
        (isEquivΩ^→ 2 (fun mapp , refl) (isoToIsEquiv mapp)))))
     (invIso (πTruncIso 2)))

  zz : isContr (π 2 (Unit , tt))
  fst zz = ∣ refl ∣₂
  snd zz = sElim (λ _ → isSetPathImplicit) λ p → refl

  isContrπ₂S³ : isContr (π 2 (hLevelTrunc∙ 4 (S₊∙ 3)))
  isContrπ₂S³ =
    subst (λ x → isContr (π 2 x))
      (λ i → ((sym (isContr→≡Unit (sphereConnected 3))) i)
            , transp (λ j → isContr→≡Unit
              (sphereConnected 3) (~ i ∧ j)) i ∣ north ∣)
      zz

-- We instantiate the sequence
P→S²→Pushout :
  Exact4 (πGr 2 P) (πGr 2 (S₊∙ 2)) (πGr 2 coFib-fold∘W∙) (πGr 1 P)
        (LESinst.fib→A 2)
        (LESinst.A→B 2)
        (LESinst.B→fib 1)
Exact4.ImG→H⊂KerH→L P→S²→Pushout = LESinst.Im-fib→A⊂Ker-A→B 2
Exact4.KerH→L⊂ImG→H P→S²→Pushout = LESinst.Ker-A→B⊂Im-fib→A 2
Exact4.ImH→L⊂KerL→R P→S²→Pushout = LESinst.Im-A→B⊂Ker-B→fib 1
Exact4.KerL→R⊂ImH→L P→S²→Pushout = LESinst.Ker-B→fib⊂Im-A→B 1

ΣP→S²→Pushout' :
  Σ[ F ∈ GroupHom (π'Gr 2 coFib-fold∘W∙) (π'Gr 1 P) ]
  (Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) (π'Gr 1 P)
         (π'∘∙Hom 2 (fst , refl))
         (π'∘∙Hom 2 inr∙)
         F)
ΣP→S²→Pushout' =
  transportExact4 _ _  _ _ _ _ _ _
    (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 P)))))
    (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 (S₊∙ 2))))))
    (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 coFib-fold∘W∙)))))
    (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 1 P)))))
    _ _ _ _ _
    P→S²→Pushout
    (toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (fromPathP λ i → fst (π∘∙fib→A-PathP 2 inr∙ i))))
    ((toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (fromPathP λ i → fst (π∘∙A→B-PathP 2 inr∙ i)))))

abstract
  π₂coFib-fold∘W→π₁P : GroupHom (π'Gr 2 coFib-fold∘W∙) (π'Gr 1 P)
  π₂coFib-fold∘W→π₁P = fst ΣP→S²→Pushout'

  P→S²→Pushout→P' :
    Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) (π'Gr 1 P)
          (π'∘∙Hom 2 (fst , refl))
          (π'∘∙Hom 2 inr∙)
          π₂coFib-fold∘W→π₁P
  P→S²→Pushout→P' = ΣP→S²→Pushout' .snd

compSurj : ∀ {ℓ ℓ' ℓ''} {G : Group ℓ} {H : Group ℓ'} {L : Group ℓ''}
         → (G→H : GroupHom G H) (H→L : GroupHom H L)
         → isSurjective G→H → isSurjective H→L
         → isSurjective (compGroupHom G→H H→L)
compSurj G→H H→L surj1 surj2 l =
  pRec squash
    (λ {(h , p)
      → pMap (λ {(g , q) → g , (cong (fst H→L) q ∙ p)})
        (surj1 h)})
    (surj2 l)

π₃S³→π₃PΩ : GroupHom (πGr 2 (S₊∙ 3)) (πGr 2 TotalPushoutPath×∙)
π₃S³→π₃PΩ = πHom 2 (S³→TotalPushoutPath× , refl)

TotalPushoutPath×∙→P : TotalPushoutPath×∙ →∙ P
fst TotalPushoutPath×∙→P x = (snd (fst x)) , (sym (snd x))
snd TotalPushoutPath×∙→P = refl

isSurjective-π₃S³→π₃PΩ : isSurjective π₃S³→π₃PΩ
isSurjective-π₃S³→π₃PΩ =
  sElim (λ _ → isProp→isSet squash)
    λ p → trRec squash
      (λ s → ∣ ∣ fst s ∣₂ , (cong ∣_∣₂ (snd s)) ∣)
      (((isConnectedΩ^→ 3 3 (S³→TotalPushoutPath× , refl) isConnected-toPullback) p) .fst)


π₃S³→π₃P : GroupHom (π'Gr 2 (S₊∙ 3)) (π'Gr 2 TotalPushoutPath×∙)
π₃S³→π₃P = π'∘∙Hom 2 (S³→TotalPushoutPath× , refl)

transportLem : PathP (λ i → GroupHomπ≅π'PathP (S₊∙ 3) TotalPushoutPath×∙ 2 i)
                     π₃S³→π₃PΩ π₃S³→π₃P
transportLem =
  toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
     (π'∘∙Hom'≡π'∘∙fun {A = S₊∙ 3} {B = TotalPushoutPath×∙} 2 (S³→TotalPushoutPath× , refl)))

isSurjective-π₃S³→π₃P : isSurjective π₃S³→π₃P
isSurjective-π₃S³→π₃P =
  transport (λ i → isSurjective (transportLem i))
    isSurjective-π₃S³→π₃PΩ

π₃S³→π₃S²' : GroupHom (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2))
π₃S³→π₃S²' = compGroupHom π₃S³→π₃P (π'∘∙Hom 2 ((λ x → snd (fst x)) , refl))

test : π₃S³→π₃S²' ≡ π'∘∙Hom 2 (fold∘W , refl)
test = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt (sElim (λ _ → isSetPathImplicit)
          λ f → cong ∣_∣₂ (ΣPathP (refl ,
            (λ j → (λ i → snd (fst ((rUnit (λ k → S³→TotalPushoutPath× (snd f k)) (~ j)) i)))
                  ∙ (λ _ → north))))))

amap : TotalPushoutPath×∙ →∙ P
fst amap ((tt , s), p) = s , (sym p)
snd amap = refl

π₃S³→π₃P' : GroupHom (π'Gr 2 (S₊∙ 3)) (π'Gr 2 P)
π₃S³→π₃P' = compGroupHom π₃S³→π₃P (π'∘∙Hom 2 amap)

isSurjective-π₃S³→π₃P' : isSurjective π₃S³→π₃P'
isSurjective-π₃S³→π₃P' =
  compSurj π₃S³→π₃P (π'∘∙Hom 2 amap)
    isSurjective-π₃S³→π₃P
    (sElim (λ _ → isProp→isSet squash)
      λ {(s , p) → ∣ ∣ (λ x → (tt , s x .fst) , sym (s x .snd))
         , ΣPathP ((ΣPathP (refl , (cong fst p)))
         , (λ i j → snd (p i) (~ j))) ∣₂
         , cong ∣_∣₂ (ΣPathP (refl , sym (rUnit p))) ∣})

-- π₃P → π₃S² → π₃ Pushout → Unit
P→S²→Pushout→Unit :
  Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (π'∘∙Hom 2 (fst , refl))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
P→S²→Pushout→Unit =
  transport (λ i →
    Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
          (GroupPath _ _ .fst
            (compGroupEquiv (GroupIso→GroupEquiv (π'Gr≅πGr 1 P)) π₂P≅0) i)
          (π'∘∙Hom 2 (fst , refl))
          (π'∘∙Hom 2 inr∙)
          (r i))
          P→S²→Pushout→P'
  where
  r : PathP (λ i → GroupHom (π'Gr 2 coFib-fold∘W∙)
                     ((GroupPath _ _ .fst
            (compGroupEquiv (GroupIso→GroupEquiv (π'Gr≅πGr 1 P)) π₂P≅0) i)))
            π₂coFib-fold∘W→π₁P
            (→UnitHom (π'Gr 2 coFib-fold∘W∙))
  r = toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
       (funExt λ _ → refl))
open Exact4

extendExact4Surj : {ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level}
  (G : Group ℓ) (H : Group ℓ') (L : Group ℓ'') (R : Group ℓ''') (S : Group ℓ'''')
  (G→H : GroupHom G H) (H→L : GroupHom H L) (L→R : GroupHom L R) (R→S : GroupHom R S)
  → isSurjective G→H
  → Exact4 H L R S H→L L→R R→S
  → Exact4 G L R S (compGroupHom G→H H→L) L→R R→S
ImG→H⊂KerH→L (extendExact4Surj G H L R S G→H H→L L→R R→S surj ex) x =
  pRec (GroupStr.is-set (snd R) _ _)
    (uncurry λ g → J (λ x _ → isInKer L→R x)
      (ImG→H⊂KerH→L ex (fst H→L (fst G→H g))
        ∣ (fst G→H g) , refl ∣))
KerH→L⊂ImG→H (extendExact4Surj G H L R S G→H H→L L→R R→S surj ex) x ker =
  pRec squash
    (uncurry λ y → J (λ x _ → isInIm (compGroupHom G→H H→L) x)
      (pMap (uncurry
        (λ y → J (λ y _ → Σ[ g ∈ fst G ] fst H→L (fst G→H g) ≡ H→L .fst y)
        (y , refl))) (surj y)))
    (KerH→L⊂ImG→H ex x ker)
ImH→L⊂KerL→R (extendExact4Surj G H L R S G→H H→L L→R R→S surj ex) =
  ImH→L⊂KerL→R ex
KerL→R⊂ImH→L (extendExact4Surj G H L R S G→H H→L L→R R→S surj ex) =
  KerL→R⊂ImH→L ex

P'→S²→Pushout→Unit' :
  Exact4 (π'Gr 2 TotalPushoutPath×∙) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (compGroupHom (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl)))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
P'→S²→Pushout→Unit' =
  extendExact4Surj _ _ _ _ _ _ _ _ _
    (sElim (λ _ → isProp→isSet squash)
      (λ f → ∣ ∣ (λ x → (tt , fst f x .fst) , sym (fst f x .snd))
      , ΣPathP ((ΣPathP (refl , cong fst (snd f))) , λ j i → snd f j  .snd (~ i)) ∣₂
              , cong ∣_∣₂ (ΣPathP (refl , sym (rUnit _))) ∣))
    P→S²→Pushout→Unit


S³→S²→Pushout→Unit'' :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (compGroupHom π₃S³→π₃P
          (compGroupHom (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit'' =
  extendExact4Surj _ _ _ _ _ _ _ _ _
    isSurjective-π₃S³→π₃P P'→S²→Pushout→Unit'

tripleComp≡ :
    (compGroupHom π₃S³→π₃P
     (compGroupHom
      (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
  ≡ π'∘∙Hom 2 (fold∘W , refl)
tripleComp≡ =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (sElim (λ _ → isSetPathImplicit)
     λ f → cong ∣_∣₂ (ΣPathP (refl , (cong (_∙ refl)
     (λ j → cong fst (rUnit (cong (fst TotalPushoutPath×∙→P)
               (rUnit (cong S³→TotalPushoutPath× (snd f)) (~ j))) (~ j))))))))

S³→S²→Pushout→Unit :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (π'∘∙Hom 2 (fold∘W , refl))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit =
  subst
   (λ F → Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
            F (π'∘∙Hom 2 inr∙)
            (→UnitHom (π'Gr 2 coFib-fold∘W∙)))
            tripleComp≡
   S³→S²→Pushout→Unit''

indΠ₃S₂ : ∀ {ℓ} {A : Pointed ℓ} → (f g : A →∙ S₊∙ 2) → fst f ≡ fst g → ∥ f ≡ g ∥
indΠ₃S₂ {A = A} f g p =
  trRec squash
   (λ r → ∣ ΣPathP (p , r) ∣)
    (isConnectedPathP 1 {A = (λ i → p i (snd A) ≡ north)}
      (isConnectedPathSⁿ 1 (fst g (pt A)) north) (snd f) (snd g) .fst )

Fold∘W : fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ idfun∙ (S₊∙ 3) ∣₂
      ≡ ∣ [ idfun∙ (S₊∙ 2) ∣ idfun∙ (S₊∙ 2) ]₂ ∣₂
Fold∘W =
  pRec (squash₂ _ _)
    (cong ∣_∣₂)
    (indΠ₃S₂ _ _
      (funExt (λ x → funExt⁻ (sym (cong fst (id∨→∙id {A = S₊∙ 2}))) (W x))))

-- Todo: generalise this

-- ℤ --f--> ℤ --g--> ℤ ---> 0

open import Cubical.Data.Int renaming (ℤ to Z ; _·_ to _·Z_ ; _+_ to _+Z_)
module Exact4→BoolIso (G : Group₀) (F : GroupHom ℤ ℤ) (H : GroupHom ℤ G) (P : fst F 1 ≡ 2)
         (ex : Exact4 ℤ ℤ G UnitGr F H (→UnitHom G)) where

  strG = snd G
  strH = snd H
  open GroupStr

  Bool→G : Bool → fst G
  Bool→G false = fst H 1
  Bool→G true = 1g strG

  isSurjectiveH : isSurjective H
  isSurjectiveH b = Exact4.KerL→R⊂ImH→L ex b refl

  Bool→GHom : IsGroupHom (snd BoolGr) Bool→G strG
  Bool→GHom =
    makeIsGroupHom
      λ { false false → sym (Exact4.ImG→H⊂KerH→L ex 2 ∣ 1 , P ∣)
                           ∙ IsGroupHom.pres· (snd H) 1 1
        ; false true → sym (rid (snd G) _)
        ; true y → sym (lid (snd G) _)}

  BoolGHom : GroupHom BoolGr G
  fst BoolGHom = Bool→G
  snd BoolGHom = Bool→GHom

  genG : fst G
  genG = fst H 1

  open IsGroupHom

  _·G_ = GroupStr._·_ (snd G)

  isSurjectiveBoolGHomPos : (n : ℕ) → Σ[ b ∈ Bool ] fst H (pos n) ≡ Bool→G b
  isSurjectiveBoolGHomPos zero = true , pres1 strH
  isSurjectiveBoolGHomPos (suc zero) = false , refl
  isSurjectiveBoolGHomPos (suc (suc n)) =
    isSurjectiveBoolGHomPos n .fst
    , (cong (fst H) (+Comm (pos n) 2)
    ∙ (pres· (snd H) 2 (pos n)))
    ∙ cong (_·G (fst H (pos n)))
        (sym (sym (Exact4.ImG→H⊂KerH→L ex 2 ∣ 1 , P ∣)))
    ∙ lid (snd G) _
    ∙ isSurjectiveBoolGHomPos n .snd

  isSurjectiveBoolGHomPre : (x : Z) → Σ[ b ∈ Bool ] fst H x ≡ Bool→G b
  isSurjectiveBoolGHomPre (pos n) = isSurjectiveBoolGHomPos n
  isSurjectiveBoolGHomPre (negsuc n) =
      (isSurjectiveBoolGHomPos (suc n) .fst)
    , cong (fst H) (+Comm (- (pos (suc n))) 0)
    ∙ presinv (snd H) (pos (suc n))
    ∙ cong (inv strG) (isSurjectiveBoolGHomPos (suc n) .snd)
    ∙ sym (presinv Bool→GHom (isSurjectiveBoolGHomPos (suc n) .fst))

  isSurjectiveBoolGHom : isSurjective BoolGHom
  isSurjectiveBoolGHom g =
    pMap (λ {(x , p) → (isSurjectiveBoolGHomPre x .fst)
                      , (sym (isSurjectiveBoolGHomPre x .snd) ∙ p)})
         (isSurjectiveH g)

  isInjectiveBoolGHom : isInjective BoolGHom
  isInjectiveBoolGHom false p =
    ⊥-rec (pRec isProp⊥ (uncurry contr) ∃1≡2)
    where
    H≡0 : isInKer H 1
    H≡0 = p

    H≡ : isInIm F 1
    H≡ = Exact4.KerH→L⊂ImG→H ex 1 p

    F≡pos : (n : ℕ) → fst F (pos n) ≡ 2 ·Z (pos n)
    F≡pos zero = pres1 (snd F)
    F≡pos (suc zero) = P
    F≡pos (suc (suc n)) =
         cong (fst F) (+Comm (pos (suc n)) (pos 1))
      ∙∙ pres· (snd F) (pos 1) (pos (suc n))
      ∙∙ cong₂ _+Z_ P (F≡pos (suc n))
      ∙∙ +Comm 2 (2 ·Z (pos (suc n)))
      ∙∙ (sym (·DistR+ 2 (pos (suc n)) 1))

    F≡ : (x : Z) → fst F x ≡ 2 ·Z x
    F≡ (pos n) = F≡pos n
    F≡ (negsuc n) =
        cong (fst F) (+Comm (negsuc n) 0)
      ∙ presinv (snd F) (pos (suc n))
      ∙ (sym (+Comm (- (fst F (pos (suc n)))) 0)
      ∙ cong -_ (F≡pos (suc n)))
      ∙ sym (ℤ·negsuc 2 n)

    ∃1≡2 : ∃[ x ∈ Z ] 1 ≡ 2 ·Z x
    ∃1≡2 =
      pMap (λ {(x , p) → x , (sym p ∙ F≡ x)}) H≡

    contr : (x : Z) → 1 ≡ 2 ·Z x → ⊥
    contr (pos zero) p = snotz (injPos p)
    contr (pos (suc n)) p = snotz (injPos (sym (cong predℤ p ∙ predSuc _ ∙ help1 n)))
      where
      help1 : (n : ℕ) → pos (suc n) +pos n ≡ pos (suc (n + n))
      help1 zero = refl
      help1 (suc n) = cong sucℤ (sym (sucℤ+ (pos (suc n)) (pos n)))
                    ∙ cong (sucℤ ∘ sucℤ) (help1 n)
                    ∙ cong pos (cong (2 +_) (sym (+-suc n n)))
    contr (negsuc n) p = negsucNotpos (suc (n + n)) 1 (sym (p ∙ negsuclem n))
      where
      negsuclem : (n : ℕ) → (negsuc n +negsuc n) ≡ negsuc (suc (n + n))
      negsuclem zero = refl
      negsuclem (suc n) =
          cong predℤ (+Comm (negsuc (suc n)) (negsuc n)
                     ∙ cong predℤ (negsuclem n))
        ∙ cong (negsuc ∘ (2 +_)) (sym (+-suc n n))
  isInjectiveBoolGHom true p = refl

  BijectionIsoBoolG : BijectionIso BoolGr G
  BijectionIso.fun BijectionIsoBoolG = BoolGHom
  BijectionIso.inj BijectionIsoBoolG = isInjectiveBoolGHom
  BijectionIso.surj BijectionIsoBoolG = isSurjectiveBoolGHom

  Bool≅G : GroupIso BoolGr G
  Bool≅G = BijectionIso→GroupIso BijectionIsoBoolG

open import Cubical.Data.Sum
Exact4→Bool≅G± : (G : Group₀) (F : GroupHom ℤ ℤ) (H : GroupHom ℤ G)
         (P : (fst F 1 ≡ 2) ⊎ (fst F 1 ≡ - 2))
         (ex : Exact4 ℤ ℤ G UnitGr F H (→UnitHom G))
         → GroupIso BoolGr G
Exact4→Bool≅G± G F H (inl x) ex = Exact4→BoolIso.Bool≅G G F H x ex
Exact4→Bool≅G± G F H (inr x) ex =
  Exact4→BoolIso.Bool≅G _ _ _ (cong (fst flip') x) Exact4'
  where
  flip' : GroupHom ℤ ℤ
  fst flip' x = GroupStr.inv (snd ℤ) x
  snd flip' = makeIsGroupHom (λ x y →
      (+Comm (pos 0) (- (x +Z y))
      ∙ -Dist+ x y)
    ∙ λ i → GroupStr.lid (snd ℤ) (- x) (~ i) +Z GroupStr.lid (snd ℤ) (- y) (~ i))

  Exact4' : Exact4 ℤ ℤ G UnitGr (compGroupHom F flip') H (→UnitHom G)
  ImG→H⊂KerH→L Exact4' x inim =
       (cong (fst H) (sym (GroupTheory.invInv ℤ x))
       ∙ (IsGroupHom.presinv (snd H) (fst flip' x)))
    ∙∙ cong (GroupStr.inv (snd G)) (ImG→H⊂KerH→L ex _ (help inim))
    ∙∙ GroupTheory.inv1g  G
    where
    help : isInIm (compGroupHom F flip') x → isInIm F (fst flip' x)
    help =
      pMap λ {(x , p) → x ,
          ((sym (-Involutive (fst F x))
          ∙ +Comm (- (- fst F x)) (pos 0))
         ∙ (λ i → pos 0 - (+Comm (- fst F x) (pos 0)  i)))
         ∙ λ i → pos 0 - p i }
  KerH→L⊂ImG→H Exact4' x inker =
    pMap (λ {(x , p) → (fst flip' x) , (GroupStr.lid (snd ℤ) (- (fst F (pos 0 - x)))
                                     ∙ cong -_ (IsGroupHom.presinv (snd F) x
                                              ∙ GroupStr.lid (snd ℤ) (- (fst F x)))
                                     ∙ -Involutive (fst F x) ∙ p)})
      (KerH→L⊂ImG→H ex x inker)
  ImH→L⊂KerL→R Exact4' = ImH→L⊂KerL→R ex
  KerL→R⊂ImH→L Exact4' = KerL→R⊂ImH→L ex


Exact4→boolIsoGenPre :
  (G H L : Group₀) (Z≅G : GroupEquiv ℤ G) (Z≅H : GroupEquiv ℤ H)
  → (G→H : GroupHom G H) (H→L : GroupHom H L)
  → ((invEq (fst Z≅H) (fst G→H (fst (fst Z≅G) 1)) ≡ 2)
  ⊎ (invEq (fst Z≅H) (fst G→H (fst (fst Z≅G) 1)) ≡ - 2))
  → Exact4 G H L UnitGr G→H H→L (→UnitHom L)
  → GroupIso BoolGr L
Exact4→boolIsoGenPre G H L =
  GroupEquivJ (λ G Z≅G
    → (Z≅H : GroupEquiv ℤ H)
    → (G→H : GroupHom G H) (H→L : GroupHom H L)
    → ((invEq (fst Z≅H) (fst G→H (fst (fst Z≅G) 1)) ≡ 2)
    ⊎ (invEq (fst Z≅H) (fst G→H (fst (fst Z≅G) 1)) ≡ - 2))
    → Exact4 G H L UnitGr G→H H→L (→UnitHom L)
    → GroupIso BoolGr L)
   (GroupEquivJ (λ H Z≅H →
      (G→H : GroupHom ℤ H)
      (H→L : GroupHom H L) →
      (invEq (fst Z≅H) (fst G→H (idfun (typ ℤ) (pos 1))) ≡ pos 2) ⊎
      (invEq (fst Z≅H) (fst G→H (idfun (typ ℤ) (pos 1))) ≡ negsuc 1) →
      Exact4 ℤ H L UnitGr G→H H→L (→UnitHom L) → GroupIso BoolGr L)
      λ Z→Z L P ex → Exact4→Bool≅G± _ _ L P ex)

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.PinSn


-- π₂S³-gen-by-HopfMap

-- abs (HopfInvariant-π' 0 ([ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)) ≡ 2

hopfInvariantEquiv : GroupEquiv (π'Gr 2 (S₊∙ 2)) ℤ
fst (fst hopfInvariantEquiv) = HopfInvariant-π' 0
snd (fst hopfInvariantEquiv) =
  GroupEquivℤ-isEquiv (invGroupEquiv π₃S²≅ℤ) ∣ HopfMap ∣₂
                      π₂S³-gen-by-HopfMap (GroupHom-HopfInvariant-π' 0)
                      (abs→⊎ _ _ HopfInvariant-HopfMap)
snd hopfInvariantEquiv = snd (GroupHom-HopfInvariant-π' 0)

π₃PushoutCharac :
    abs (HopfInvariant-π' 0 [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π') ≡ 2
  → GroupIso BoolGr (π'Gr 2 coFib-fold∘W∙)
π₃PushoutCharac p =
  Exact4→boolIsoGenPre (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
    (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))
    (invGroupEquiv hopfInvariantEquiv)
    (π'∘∙Hom 2 (fold∘W , refl))
    (π'∘∙Hom 2 inr∙)
    (abs→⊎ _ _ (cong abs
      (cong (invEq (fst (invGroupEquiv hopfInvariantEquiv)))
        (cong (fst (π'∘∙Hom 2 (fold∘W , refl)))
          help)
     ∙ cong (HopfInvariant-π' 0)
        (Fold∘W ∙ sym (cong ∣_∣₂ ([]≡[]₂ (idfun∙ (S₊∙ 2)) (idfun∙ (S₊∙ 2)))))) ∙ p))
    S³→S²→Pushout→Unit
  where
  help : inv (fst (πₙ'Sⁿ≅ℤ 2)) 1 ≡ ∣ idfun∙ _ ∣₂
  help = cong (inv (fst (πₙ'Sⁿ≅ℤ 2))) (sym (πₙ'Sⁿ≅ℤ-idfun∙ 2))
       ∙ leftInv (fst (πₙ'Sⁿ≅ℤ 2)) ∣ idfun∙ _ ∣₂

open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso

∣HopfWhitehead∣≡2→π₄S³≅Bool :
  abs (HopfInvariant-π' 0 [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π') ≡ 2
  → GroupEquiv (πGr 3 (S₊∙ 3)) BoolGr
∣HopfWhitehead∣≡2→π₄S³≅Bool p =
  compGroupEquiv
    (compGroupEquiv
      (GroupIso→GroupEquiv
        (compGroupIso π₄S³≅π₃PushS²
          (invGroupIso (π'Gr≅πGr 2 (Pushout⋁↪fold⋁∙ (S₊∙ 2))))))
      (compGroupEquiv (invGroupEquiv (π'Iso 2 lem∙))
        (π'Iso 2 (lem₂ , sym (push north)))))
    (invGroupEquiv (GroupIso→GroupEquiv (π₃PushoutCharac p)))
  where
  lem₂ : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ ≃ fst coFib-fold∘W∙
  lem₂ = compEquiv
          (compEquiv pushoutSwitchEquiv (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
          pushoutSwitchEquiv

  lem₁ : Pushout W (λ _ → tt) ≃ cofibW S¹ S¹ base base
  lem₁ = pushoutEquiv W (λ _ → tt) joinTo⋁ (λ _ → tt)
           (isoToEquiv (invIso (IsoSphereJoin 1 1)))
           (idEquiv _)
           (idEquiv _)
           refl
           refl

  lem : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁
      ≃ fst (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  lem = pushoutEquiv inl _ ⋁↪ fold⋁
          (idEquiv _)
          (compEquiv lem₁ (isoToEquiv (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))))
          (idEquiv _)
          (Susp×Susp→cofibW≡ S¹ S¹ base base)
          refl

  lem∙ : (Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ , inr north)
       ≃∙ (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  fst lem∙ = lem
  snd lem∙ = sym (push (inl north))

{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.FiberOrCofiberSequences.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation renaming (elim to setElim)
open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.LES

open import Cubical.Homotopy.Serre.PointedHITs

open import Cubical.Homotopy.Serre.ConnectedCovers.TruncationLevelFacts
open import Cubical.Homotopy.Serre.Pullback.IsPullback

private
  variable
    ℓ : Level

loop-tt-isUnit : (PathP (λ _ → Unit* {ℓ}) tt* tt*) ≡ Unit*
loop-tt-isUnit = isContr→≡Unit* (isProp→isContrPath isPropUnit* tt* tt*)

transportPathLemmaLeft : {A : Type ℓ} {a b c : A} (p : b ≡ a) (q : b ≡ c)
  → transport (λ i → p i ≡ c) q ≡ (p ⁻¹) ∙ q
transportPathLemmaLeft {b = b} {c = c} =
  J (λ a p → (q : b ≡ c) → transport (λ i → p i ≡ c) q ≡ (p ⁻¹) ∙ q)
    (λ q → fromPathP (lUnit q ∙ cong (_∙ q) symRefl))


fiber∙ : {A B : Pointed ℓ} → (A →∙ B) → Pointed ℓ
fiber∙ {A = A} {B = B} f = fiber (fst f) (pt B) , (pt A) , (snd f)

fiberMap∙ : {A B : Pointed ℓ} (f : A →∙ B) → (fiber∙ f →∙ A)
fiberMap∙ {A = A} {B = B} f = fst , refl

fiberMapCompEq : {A B : Pointed ℓ} (f : A →∙ B)
  → f ∘∙ (fiberMap∙ f) ≡ (const∙ (fiber∙ f) B)
fiberMapCompEq f =
  ΣPathP ((funExt (λ x → snd x))
         , (toPathP (transportPathLemmaLeft (snd f)
                     (cong (fst f) refl ∙ snd f) ∙ cong (snd f ⁻¹ ∙_)
                     (lUnit _ ⁻¹) ∙ lCancel _)))

-- fits better w/ singletons
fiber' : {A B : Type ℓ} → (A → B) → B → Type ℓ
fiber' {A = A} f a = Σ[ x ∈ A ] f x ≡ a

-- these transportPathLemmas should be renamed and moved elsewhere
transportPathLemma' : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c)
  → transp (λ i → p (~ i) ≡ c) i0 q ≡ p ∙ q
transportPathLemma' {c = c} =
  J (λ b' p' → (q : b' ≡ c) → transp (λ i → p' (~ i) ≡ c) i0 q ≡ p' ∙ q)
    λ q → transportRefl q ∙ lUnit q

transportPathLemmaRight : {A : Type ℓ} {a b c : A} (p : b ≡ c) (q : a ≡ b)
  → transport (λ i → a ≡ (p i)) q ≡ q ∙ p
transportPathLemmaRight {a = a} {b = b} =
  J (λ c p → ∀ (q : a ≡ b) → transport (λ i → a ≡ (p i)) q ≡ q ∙ p)
    λ q → fromPathP (rUnit q)

transportFunPathLemma'' : {A : Type ℓ} (a a' : A) (p : a ≡ a')
  → transp (λ i → p (~ i) ≡ a') i0 refl ≡ p
transportFunPathLemma'' a a' =
  J (λ a'' p → transp (λ i → p (~ i) ≡ a'') i0 refl ≡ p)
    (transportRefl refl)

transportFunPathLemma' : {A B : Type ℓ} {a a' : A} {b : B} (f : A → B)
  (q : a ≡ a') (r : f a' ≡ b)
  → transport (λ i → f (q (~ i)) ≡ b) r ≡ cong f q ∙ r
transportFunPathLemma' {b = b} f =
  J ( λ a* q
        → (r : f a* ≡ b)
        → transport (λ i → f (q (~ i)) ≡ b) r ≡ cong f q ∙ r)
    ( λ r → transportRefl r ∙ lUnit r)

transportFunPathLemma : {A B : Type ℓ} (a : A) (b : B) (f g : A → B)
  (p : f ≡ g) (q : f a ≡ b) (r : g a ≡ b)
  → transport (λ i → p i a ≡ b) q ≡ r
  → (λ i → p i a) ⁻¹ ∙ q ≡ r
transportFunPathLemma a b f g =
  J ( λ h p
       → (q : f a ≡ b) (r : h a ≡ b)
       → transport (λ i → p i a ≡ b) q ≡ r
       → (λ i → p i a) ⁻¹ ∙ q ≡ r)
    ( λ q r s → cong (_∙ q) (symRefl ⁻¹)
                 ∙ lUnit q ⁻¹
                 ∙ (s ⁻¹ ∙ transportRefl q) ⁻¹)

movingTransportPathLemma : (A : Type ℓ) (a b : A)
  (p : a ≡ b) (q : a ≡ b) (r : a ≡ a)
  → transport (λ i → p i ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q
movingTransportPathLemma A a b =
  J (λ b' p → ∀ (q : a ≡ b') (r : a ≡ a)
    → transport (λ i → p i ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q)
    λ q r → transportPathLemmaRight q r ∙ lUnit _ ∙ cong (_∙ r ∙ q) symRefl

movFunTransportPathLemma : {A B : Type ℓ} {a : A} {b c : B} (f : B → A)
  (p : b ≡ c) (q : a ≡ a) (r : f b ≡ a)
  → transport (λ i → q i ≡ f (p i)) (r ⁻¹) ≡ q ⁻¹ ∙ (r ⁻¹) ∙ (cong f p)
movFunTransportPathLemma {a = a} {b = b} f =
 J (λ c p → ∀ (q : a ≡ a) (r : f b ≡ a)
          → transport (λ i → q i ≡
                              f (p i)) (r ⁻¹) ≡ q ⁻¹ ∙ (r ⁻¹) ∙ (cong f p))
   λ q r → transportPathLemmaLeft q (r ⁻¹) ∙ rUnit (q ⁻¹ ∙ r ⁻¹)
                                            ∙ (assoc (q ⁻¹) (r ⁻¹) refl) ⁻¹

  --FiberSeq : Pointed ℓ → Pointed ℓ → Pointed ℓ → Type ℓ
  -- likewise

record FiberSeq (A B C : Pointed ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    incl : A →∙ B
    proj : B →∙ C
    eqFib : (A , incl) ≡ (fiber∙ proj , fiberMap∙ proj)

FiberSeq' : (A B C : Pointed ℓ) → Type (ℓ-suc ℓ)
FiberSeq' A B C =
  Σ[ f ∈ (A →∙ B) ] Σ[ g ∈ (B →∙ C) ] (A , f) ≡ (fiber∙ g , fiberMap∙ g)

IsoFiberSeqs : (A B C : Pointed ℓ)
  → Iso (FiberSeq A B C) (FiberSeq' A B C)

Iso.fun (IsoFiberSeqs A B C) F =
  (FiberSeq.incl F) , ((FiberSeq.proj F) , (FiberSeq.eqFib F))
FiberSeq.incl (Iso.inv (IsoFiberSeqs A B C) (incl , proj , eqFib)) =
  incl
FiberSeq.proj (Iso.inv (IsoFiberSeqs A B C) (incl , proj , eqFib)) =
  proj
FiberSeq.eqFib (Iso.inv (IsoFiberSeqs A B C) (incl , proj , eqFib)) = eqFib
Iso.sec (IsoFiberSeqs A B C) F = refl
FiberSeq.incl (Iso.ret (IsoFiberSeqs A B C) F i) = FiberSeq.incl F
FiberSeq.proj (Iso.ret (IsoFiberSeqs A B C) F i) = FiberSeq.proj F
FiberSeq.eqFib (Iso.ret (IsoFiberSeqs A B C) F i) = FiberSeq.eqFib F

EquivFiberSeqs : (A B C : Pointed ℓ)
  → (FiberSeq A B C) ≃ (FiberSeq' A B C)
EquivFiberSeqs A B C = isoToEquiv (IsoFiberSeqs A B C)

IdFiberSeqs : (A B C : Pointed ℓ)
  → (FiberSeq A B C) ≡ (FiberSeq' A B C)
IdFiberSeqs A B C = ua (EquivFiberSeqs A B C)

--projections from a fiber sequence (projections from a cofiber sequence will
--also need to be defined
FiberSeqBase : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqBase {C = C} F = C

FiberSeqTotal : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqTotal {B = B} F = B

FiberSeqFiber : {A B C : Pointed ℓ} → FiberSeq A B C → Pointed ℓ
FiberSeqFiber {A = A} F = A

module _ {A B : Pointed ℓ} (f : A →∙ B) where
  open isPullback (fst f) (fst (const∙ Unit*∙ B)) {P = typ (fiber∙ f)}
                  fst (fst (const∙ (fiber∙ f) Unit*∙))
                  (funExt (λ x → snd x))

  isoUnivProperty : (E : Type ℓ) → isIso (pullbackComparison E)
  fst (isoUnivProperty E) (g , (h , H)) e = (g e) , (funExt⁻ H e)
  fst (snd (isoUnivProperty E)) (g , (h , H)) =
    ΣPathP (refl , (ΣPathP ((funExt (λ _ → refl)) , refl)))
  snd (snd (isoUnivProperty E)) f = refl

FiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
  → FiberSeq (fiber∙ f) A B
FiberSeq.incl (FiberFiberSeq f) = fst , refl
FiberSeq.proj (FiberFiberSeq f) = f
FiberSeq.eqFib (FiberFiberSeq f) = refl

FiberSeqIncl : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (FiberSeqFiber F →∙ FiberSeqTotal F)
FiberSeqIncl F = FiberSeq.incl F


FiberSeqProj : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → (FiberSeqTotal F →∙ FiberSeqBase F)
FiberSeqProj = FiberSeq.proj

{-
  idkhope : Iso (Σ[ B ∈ Pointed ℓ ] Σ[ C ∈ Pointed ℓ ] Σ[ A ∈ Pointed ℓ ]
                 (FiberSeq' A B C))
                (Σ[ B ∈ Pointed ℓ ] Σ[ C ∈ Pointed ℓ ] (B →∙ C))

  EqOfEqFiberSeqProj'' : {A A' B C D E : Pointed ℓ} (F : FiberSeq A B C)
    → (G : FiberSeq A' D E)
    → (p : (B , C , FiberSeqProj F) ≡ (D , E , FiberSeqProj G))
    → A ≡ A'

  EqOfEqFiberSeqProj' : {A A' B C D E : Pointed ℓ} (F : FiberSeq A B C)
    → (G : FiberSeq A' D E)
    → (p : (B , C , FiberSeqProj F) ≡ (D , E , FiberSeqProj G))
    → transport (λ i → FiberSeq (EqOfEqFiberSeqProj'' F G p i) (fst (p i)) (fst (snd (p i)))) F
     ≡ G-}
--EqOfEqFiberSeqProj' F G = {!!}

FiberSeqCompEq* : {B C : Pointed ℓ} (f : B →∙ C)
    → (f ∘∙ fiberMap∙ f) ≡ const∙ _ _
FiberSeqCompEq* f =
  ΣPathP ((funExt (λ x → snd x))
         , toPathP (transportPathLemmaLeft (snd f) (cong (fst f) refl ∙ snd f)
                    ∙ cong (snd f ⁻¹ ∙_) (lUnit (snd f) ⁻¹)
                    ∙ lCancel (snd f)))

FiberSeqCompEq : {A B C : Pointed ℓ} (F : FiberSeq A B C)
    → (FiberSeqProj F ∘∙ FiberSeqIncl F) ≡ const∙ _ _
FiberSeqCompEq F =
  J (λ y p → (FiberSeqProj F ∘∙ (snd y)) ≡ const∙ _ _)
    (FiberSeqCompEq* (FiberSeqProj F))
    (FiberSeq.eqFib F ⁻¹)

Cone : {A B : Pointed ℓ} (f : A →∙ B) → Pointed ℓ → Type ℓ
Cone {A = A} {B = B} f A' = Σ[ h ∈ A' →∙ A ] f ∘∙ h ≡ const∙ A' B

Fun→Cone→Cone : {A B : Pointed ℓ} (f : A →∙ B) (A' B' : Pointed ℓ)
  → Cone f B' → (A' →∙ B') → Cone f A'
Fun→Cone→Cone f A' B' (h , p) g =
  (h ∘∙ g) , (∘∙-assoc f h g) ⁻¹ ∙ cong (_∘∙ g) p ∙ ΣPathP (refl , (lUnit _ ⁻¹))

FiberSeqCone : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Cone (FiberSeqProj F) A
FiberSeqCone F = FiberSeqIncl F , FiberSeqCompEq F

FiberSeqCompEq' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     PathP (λ i → p i (snd (FiberSeqFiber F)) ≡ snd (FiberSeqBase F))
           (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F))
            ∙ snd (FiberSeqProj F)) refl
FiberSeqCompEq' F = PathPΣ (FiberSeqCompEq F)

FiberSeqCompEq'' : {A B C  : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     transport (λ i → p i (snd (FiberSeqFiber F)) ≡ snd (FiberSeqBase F))
     (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F))
      ∙ snd (FiberSeqProj F)) ≡ refl
FiberSeqCompEq'' F = (fst (FiberSeqCompEq' F)) , (fromPathP (snd (FiberSeqCompEq' F)))

FiberSeqCompEq''' : {A B C : Pointed ℓ} (F : FiberSeq A B C)
  → Σ[ p ∈ fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F) ≡ (λ _ → snd C) ]
     (λ i → p i (snd A)) ⁻¹
     ∙ (cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F)))
     ∙ (snd (FiberSeqProj F))
     ≡ refl
FiberSeqCompEq''' F = (fst (FiberSeqCompEq' F)) ,
  transportFunPathLemma (snd (FiberSeqFiber F)) (snd (FiberSeqBase F))
  (fst (FiberSeqProj F) ∘ fst (FiberSeqIncl F))
  (λ _ → snd (FiberSeqBase F))
  (fst (FiberSeqCompEq' F))
  ((cong (fst (FiberSeqProj F)) (snd (FiberSeqIncl F)))
  ∙ (snd (FiberSeqProj F)))
  refl
  (snd (FiberSeqCompEq'' F))


congFunPathLemma : {A B : Type ℓ} {a a' : A} (p : a ≡ a') (f g : A → B)
  (q : f ≡ g) → (λ i → q i a) ∙ cong g p ∙ (sym (λ i → q i a')) ≡ cong f p
congFunPathLemma {a = a} {a' = a'} p f g =
  J (λ h q → (λ i → q i a) ∙ cong h p ∙ (sym (λ i → q i a')) ≡ cong f p)
  (lUnit _ ⁻¹ ∙ cong ((cong f p) ∙_) (symRefl ⁻¹) ∙ rUnit _ ⁻¹)

congConstIsRefl : {A B : Type ℓ} {a a' : A} {b : B} (p : a ≡ a')
  → cong (λ _ → b) p ≡ refl
congConstIsRefl p = refl

FibsEqOfFibSeq : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
    (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
    → (A , FiberSeqIncl F) ≡ (A' , FiberSeqIncl G)
FibsEqOfFibSeq F G p = FiberSeq.eqFib F ∙ cong (λ f → (fiber∙ f , fiberMap∙ f)) p ∙ FiberSeq.eqFib G ⁻¹

FibsIsoOfFibSeq : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
    (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
    → Σ[ pr ∈ Σ[ H ∈ Iso (typ A) (typ A') ] Iso.fun H (pt A) ≡ pt A' ]
       (FiberSeqIncl F
       ∘∙ ((Iso.inv (fst pr)) , cong (Iso.inv (fst pr)) (sym (snd pr))
                                ∙ Iso.ret (fst pr) _))
     ≡ FiberSeqIncl G
FibsIsoOfFibSeq {A = A} F G p =
  J (λ y q
    →  Σ[ pr ∈ Σ[ H ∈ Iso (typ A) (typ (fst y)) ]
              Iso.fun H (pt A) ≡ pt (fst y) ]
   (FiberSeqIncl F
       ∘∙ ((Iso.inv (fst pr))
          , cong (Iso.inv (fst pr)) (sym (snd pr))
            ∙ Iso.ret (fst pr) _))
    ≡ (snd y))
    ((idIso , refl)
    , ΣPathP (refl , (cong (_∙ (snd (FiberSeqIncl F)))
                           (cong (cong (fst (FiberSeqIncl F)))
                                       (lUnit _ ⁻¹))
                     ∙ lUnit _ ⁻¹)))
    (FibsEqOfFibSeq F G p)



ProjOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → FiberSeqProj (FiberFiberSeq f) ≡ f
ProjOfFiberFiberSeq f = refl

inclOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
  → ((fiber∙ f) →∙ A)
inclOfFiberFiberSeq f = fst , refl

InclOfFiberFiberSeq : {A B : Pointed ℓ} (f : A →∙ B)
    → FiberSeqIncl (FiberFiberSeq f) ≡ (fst , refl {x = snd A})
InclOfFiberFiberSeq f = refl


FibsEqOfFibSeq' : {A A' B C : Pointed ℓ} (F : FiberSeq A B C)
  (G : FiberSeq A' B C) → (FiberSeqProj F) ≡ (FiberSeqProj G)
  →
  Σ[ p ∈ A ≡ A' ] PathP (λ i → (p i) →∙ B) (FiberSeqIncl F) (FiberSeqIncl G)
FibsEqOfFibSeq' F G q = PathPΣ (FibsEqOfFibSeq F G q)

FibsEqFiberFiberSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) →
  Σ[ p ∈ A ≡ fiber∙ (FiberSeqProj F) ]
   PathP (λ i → (p i) →∙ B) (FiberSeqIncl F) (fst , refl)
FibsEqFiberFiberSeq {A = A} {B = B} {C = C} F =
  transport
  ( λ i → Σ[ p ∈ A ≡ fiber∙ (FiberSeqProj F) ]
            PathP
            ( λ i → (p i) →∙ B)
            ( FiberSeqIncl F)
            ( InclOfFiberFiberSeq (FiberSeqProj F) i))
  ( FibsEqOfFibSeq' F (FiberFiberSeq (FiberSeqProj F))
  ( ProjOfFiberFiberSeq (FiberSeqProj F) ⁻¹))

FibsIsoFiberFiberSeq : {A B C : Pointed ℓ} (F : FiberSeq A B C) →
  Σ[ H ∈ Iso (typ (fiber∙ (FiberSeqProj F))) (typ A) ]
  Iso.fun H (pt (fiber∙ (FiberSeqProj F))) ≡ (pt A)
FibsIsoFiberFiberSeq F =
  fst (FibsIsoOfFibSeq
       ( FiberFiberSeq
         ( FiberSeqProj F))
       ( F)
       ( ProjOfFiberFiberSeq _))


BaseEqFiberSeq : {A B C C' : Pointed ℓ} → C ≡ C' → FiberSeq A B C
    → FiberSeq A B C'
BaseEqFiberSeq {A = A} {B = B} p F = transport (λ i → FiberSeq A B (p i)) F

BaseEquivFiberSeq : {A B C C' : Pointed ℓ} → C ≃∙ C' → FiberSeq A B C
    → FiberSeq A B C'
BaseEquivFiberSeq e F = BaseEqFiberSeq (ua∙ (fst e) (snd e)) F

BaseIsoFiberSeq : {A B C C' : Pointed ℓ} (H : Iso (typ C) (typ C'))
    → Iso.fun H (pt C) ≡ pt C' → FiberSeq A B C → FiberSeq A B C'
BaseIsoFiberSeq H p =
  BaseEquivFiberSeq ((isoToEquiv H) , p)


TotalEqFiberSeq : {A B B' C : Pointed ℓ} → B ≡ B' → FiberSeq A B C
  → FiberSeq A B' C
TotalEqFiberSeq {A = A} {C = C} p F =
  transport (λ i → FiberSeq A (p i) C) F

TotalEquivFiberSeq : {A B B' C : Pointed ℓ} → B ≃∙ B' → FiberSeq A B C
  → FiberSeq A B' C
TotalEquivFiberSeq e F = TotalEqFiberSeq (ua∙ (fst e) (snd e)) F

TotalIsoFiberSeq : {A B B' C : Pointed ℓ} (H : Iso (typ B) (typ B'))
  → Iso.fun H (pt B) ≡ pt B' → FiberSeq A B C → FiberSeq A B' C
TotalIsoFiberSeq H h F = TotalEquivFiberSeq ((isoToEquiv H) , h) F

FiberEqFiberSeq : {A A' B C : Pointed ℓ} → A ≡ A' → FiberSeq A B C
  → FiberSeq A' B C
FiberEqFiberSeq {B = B} {C = C} p F =
  transport (λ i → FiberSeq (p i) B C) F

FiberEquivFiberSeq : {A A' B C : Pointed ℓ} → A ≃∙ A' → FiberSeq A B C
    → FiberSeq A' B C
FiberEquivFiberSeq e F = FiberEqFiberSeq (ua∙ (fst e) (snd e)) F

FiberIsoFiberSeq : {A A' B C : Pointed ℓ} (H : Iso (typ A) (typ A'))
    → Iso.fun H (pt A) ≡ pt A' → FiberSeq A B C → FiberSeq A' B C
FiberIsoFiberSeq H h F = FiberEquivFiberSeq ((isoToEquiv H) , h) F

ContrBase→TotalEqFib-fib∙ : {B : Pointed ℓ}
    → (fiber∙ {A = B} ((λ (_ : typ B) → tt*) , refl)) ≡ B
ContrBase→TotalEqFib-fib∙ {B = B} = ua∙ γ refl
  where
   γ : (fst (fiber∙ {A = B} ((λ (_ : typ B) → tt*) , refl))) ≃ (fst B)
   γ = Σ-contractSnd (λ _ → isProp→isContrPath isPropUnit* tt* tt*)

ContrBase→TotalEqFib-fib∙' : {B : Pointed ℓ} (f : B →∙ (Unit* , tt*))
  → (fiber∙ {A = B} f) ≡ B
ContrBase→TotalEqFib-fib∙' {B = B} f =
  transport (λ i → fiber∙ {A = B} (ρ (~ i)) ≡ B) ContrBase→TotalEqFib-fib∙
  where
    ρ : f ≡ ((λ (_ : typ B) → tt*) , refl)
    ρ = ΣPathP ((funExt (λ _ → refl))
               , (isContr→isProp
                  (isProp→isContrPath isPropUnit* tt* tt*) (snd f) refl))

ContrBase→TotalEqFib : {A B C : Pointed ℓ} → isContr (typ C)
      → FiberSeq A B C → A ≡ B
ContrBase→TotalEqFib {ℓ} {B = B} {C = C} hC F =
  fst (PathPΣ (FiberSeq.eqFib F))
  ∙ (transport (λ i → (f : B →∙ γ (~ i))
                    → fiber∙ {A = B} f ≡ B) (ContrBase→TotalEqFib-fib∙')) (FiberSeqProj F)
  where
    γ : C ≡ (Unit* {ℓ} , tt*)
    γ = ΣPathP ((isContr→≡Unit* hC) , toPathP (isPropUnit* _ tt*))
--ContrBase→TotalEqFib hC F = {!!}

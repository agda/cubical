{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}

module Cubical.ZCohomology.EilenbergSteenrodZ where

open import Cubical.Core.Everything

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.Data.Nat
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.HITs.SetTruncation renaming (map to sMap ; rec to sRec ; elim to sElim)
open import Cubical.HITs.PropositionalTruncation renaming (map to pMap ; rec to pRec ; elim to pElim ; elim2 to pElim2)
open import Cubical.HITs.Truncation renaming (rec to trRec ; map to trMap ; elim to trEilim ; elim2 to trElim2)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

open import Cubical.HITs.Pushout
open import Cubical.Algebra.Group
open import Cubical.HITs.Susp

open IsGroup
open GroupStr
open GroupIso
open import Cubical.Data.Bool

open import Cubical.HITs.Wedge

open GroupHom

open import Cubical.HITs.Sn

contravar-coHomGr : (n : ℕ) → contravar (coHomGr n)
fun (contravar-coHomGr n f) = coHomFun n f
isHom (contravar-coHomGr zero f) = elim2 {! !} {!!}
isHom (contravar-coHomGr (suc n) f) = {!!}

test : {!!}
test = {!!}

pointerElimFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f : Pointer A → coHomK (suc n)) → (f pt₀ ≡ 0ₖ _) → Pointer A → coHomK (suc n)
pointerElimFun n f p pt₀ = 0ₖ _
pointerElimFun n f p ⌊ x ⌋ = f ⌊ x ⌋
pointerElimFun n f p (id i) = (cong f id ∙ p) i

pointerElim : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointer A → Type ℓ'}
              → ((x : typ A) → B ⌊ x ⌋)
              → (x : _) → B x
pointerElim {A = A} {B = B} ind pt₀ = subst B id (ind (pt A))
pointerElim ind ⌊ x ⌋ = ind x
pointerElim {B = B} ind (id i) = transp (λ j → B (id (i ∧ j))) (~ i) (ind (pt _))

≡PointerFun : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _) → pointerElimFun n f p ≡ f 
≡PointerFun n f p i pt₀ = p (~ i)
≡PointerFun n f p i ⌊ x ⌋ = f ⌊ x ⌋ 
≡PointerFun n f p i (id j) = compPath-filler (cong f id) p (~ i) j

coHomPointerElim : ∀ {ℓ ℓ'} {A : Pointed ℓ} (n : ℕ) {B : coHom (suc n) (Pointer A) → Type ℓ'}
                 → ((x : coHom (suc n) (Pointer A)) → isProp (B x))
                 → ((f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _) → B ∣ pointerElimFun n f p ∣₂)
                 → (x : coHom (suc n) (Pointer A)) → B x
coHomPointerElim {A = A} n {B = B} isprop =
  transport (λ i → ((f : Pointer A → coHomK (suc n)) (p : f pt₀ ≡ 0ₖ _)
                   → B ∣ ≡PointerFun n f p (~ i) ∣₂)
                   → (x : coHom (suc n) (Pointer A)) → B x)
            (coHomPointedElim _ _ isprop)

suspΩFun' : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → Path _ (0ₖ _) (0ₖ _)) → Susp A → coHomK (suc n)
suspΩFun' n f north = 0ₖ _
suspΩFun' n f south = 0ₖ _
suspΩFun' n f (merid a i) = f a i

suspΩFun : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (f : A → coHomK n) → Susp A → coHomK (suc n)
suspΩFun n f = suspΩFun' n λ a → Kn→ΩKn+1 n (f a)

≡suspΩFun : (n : ℕ) (A : Pointed₀) (f : Susp (typ A) → coHomK (suc n)) (p : f north ≡ 0ₖ _) → f ≡ suspΩFun' n λ a → sym p ∙∙ (cong f (merid a)) ∙∙ (cong f (sym (merid (pt A))) ∙ p)
≡suspΩFun n s f p i north = p i
≡suspΩFun n s f p i south = (cong f (sym (merid (pt s))) ∙ p) i
≡suspΩFun n s f p i (merid a j) =
  doubleCompPath-filler (sym p) (cong f (merid a)) (cong f (sym (merid (pt s))) ∙ p) i j

SuspCohomElim : ∀ {ℓ} {A : Pointed ℓ-zero} (n : ℕ) {B : coHom (suc n) (Susp (typ A)) → Type ℓ}
             → ((x : coHom (suc n) (Susp (typ A))) → isProp (B x))
             → ((f : typ A → Path _ (0ₖ _) (0ₖ _)) → f (pt A) ≡ refl → B ∣ suspΩFun' n f ∣₂)
             → (x : _) → B x
SuspCohomElim {A = A} n {B = B} isprop f =
  coHomPointedElim _ north isprop λ g gid
    → subst (B ∘ ∣_∣₂) (sym (≡suspΩFun n A g gid))
                       (f _ ((λ i → (sym gid ∙∙ (λ j → g (merid (pt A) (~ i ∧ j))) ∙∙ ((λ j → g (merid (pt A) (~ i ∧ ~ j))) ∙ gid)))
                                  ∙∙ (λ i → (λ j → gid (i ∨ ~ j)) ∙∙ refl ∙∙ lUnit (λ j → gid (i ∨ j)) (~ i))
                                  ∙∙ sym (rUnit refl)))

open import Cubical.HITs.S1
open isCohomTheory
isCohomTheoryZ : isCohomTheory coHomGr (λ n → coHomMorph n)
Suspension isCohomTheoryZ =
  transport (λ i → Σ[ F ∈ ((n : ℕ) {A : Pointed ℓ-zero}
                          → GroupIso (coHomGr (suc n) (Susp (isoToPath (IsoPointedPointer {A = A}) (~ i))))
                                      (coHomGr n (isoToPath (IsoPointedPointer {A = A}) (~ i)))) ]
                    ({A B : Pointed ℓ-zero} (f : isoToPath (IsoPointedPointer {A = A}) (~ i) → isoToPath (IsoPointedPointer {A = B}) (~ i)) (n : ℕ) →
                     coHomFun (suc n) (suspFun f) ∘ inv (F n) ≡
                     inv (F n) ∘ coHomFun n f))
            (pointerIso)
  where
  hom : (n : ℕ) → {A : Pointed ℓ-zero} → coHom (suc n) (Susp (Pointer A)) → coHom n (Pointer A)
  hom n = sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid pt₀)) ∙∙ rCancelₖ (suc n) (f north))

  hom⁻ : (n : ℕ) {A : Pointed ℓ-zero} → coHom n (Pointer A) → coHom (suc n) (Susp (Pointer A))
  hom⁻ n = sMap (suspΩFun n)

  ishom⁻ : (n : ℕ) {A : Pointed ℓ-zero}
        → isGroupHom (coHomGr n (Pointer A)) (coHomGr (suc n) (Susp (Pointer A))) (hom⁻ n)
  ishom⁻ zero {A = A} =
    elim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      λ f g → cong ∣_∣₂ (funExt λ {north → refl
                                ; south → refl
                                ; (merid a i) j → (Kn→ΩKn+1-hom 0 (f a) (g a)
                                                 ∙ ∙≡+₁ (Kn→ΩKn+1 0 (f a)) (Kn→ΩKn+1 0 (g a))) j i})
  ishom⁻ (suc n) {A = A} = elim2 (λ _ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      λ f g → cong ∣_∣₂ (funExt λ {north → refl
                                ; south → refl
                                ; (merid a i) j → (Kn→ΩKn+1-hom (suc n) (f a) (g a)
                                                 ∙ ∙≡+₂ n (Kn→ΩKn+1 (suc n) (f a)) (Kn→ΩKn+1 (suc n) (g a))) j i})

  pointerIso : Σ _ _
  fst pointerIso n {A = A} = invGroupIso theIso
    where
    theIso : GroupIso (coHomGr n (Pointer A)) (coHomGr (suc n) (Susp (Pointer A)))
    fun (map theIso) = hom⁻ n
    isHom (map theIso) = ishom⁻ n
    inv theIso = hom n
    rightInv theIso =
      SuspCohomElim {A = Pointer A , pt₀} _ (λ _ → setTruncIsSet _ _)
                    λ f fId → cong ∣_∣₂ (funExt λ {north → refl
                                             ; south → refl
                                             ; (merid a i) j → helper n a f fId j i})
      where
      helper : (n : ℕ) (a : Pointer A) (f : (Pointer A) →  Path (coHomK (suc n)) (0ₖ (suc n)) (0ₖ (suc n))) → f pt₀ ≡ refl →
                              cong (suspΩFun n
         (λ x →
            ΩKn+1→Kn n
            ((λ i₁ → rCancelₖ (suc n) (0ₖ _) (~ i₁)) ∙∙
             (λ i₁ →
                suspΩFun' n f ((merid x ∙ (λ i₂ → merid pt₀ (~ i₂))) i₁) -ₖ
                suspΩFun' n f north)
             ∙∙ rCancelₖ (suc n) (suspΩFun' n f north))))
         (merid a) ≡ f a
      helper zero a f fId =
          (λ i → Iso.rightInv (Iso-Kn-ΩKn+1 0)
                   (transportRefl refl i
                 ∙∙ cong (λ x → suspΩFun' 0 f x +ₖ 0ₖ _) (merid a ∙ sym (merid pt₀))
                 ∙∙ transportRefl refl i) i)
       ∙∙ sym (rUnit _)
       ∙∙ (λ i → cong (λ x → rUnitₖ _ (suspΩFun' 0 f x) i) (merid a ∙ sym (merid pt₀)))
       ∙∙ congFunct (suspΩFun' 0 f) (merid a) (sym (merid pt₀)) -- (λ i → cong {!!} {!merid a!} ∙ {!!})
       ∙∙ (cong (f a ∙_) (cong sym fId)
        ∙ sym (rUnit (f a)))
      helper (suc n) a f fId = 
        (λ i → Iso.rightInv (Iso-Kn-ΩKn+1 (suc n))
                   (transportRefl refl i
                 ∙∙ cong (λ x → suspΩFun' (suc n) f x +ₖ 0ₖ _) (merid a ∙ sym (merid pt₀))
                 ∙∙ transportRefl refl i) i)
       ∙∙ sym (rUnit _)
       ∙∙ (λ i → cong (λ x → rUnitₖ _ (suspΩFun' (suc n) f x) i) (merid a ∙ sym (merid pt₀)))
       ∙∙ congFunct (suspΩFun' (suc n) f) (merid a) (sym (merid pt₀))
       ∙∙ (cong (f a ∙_) (cong sym fId)
        ∙ sym (rUnit (f a)))
    leftInv theIso = helper n
      where
      helper : (n : ℕ) → retract (hom⁻ n) (hom n)
      helper zero = {!!}
      helper (suc n) =
        coHomPointerElim n (λ _ → setTruncIsSet _ _)
          λ f fId →
            cong ∣_∣₂ (funExt
                       (pointerElim λ x →
                         cong (ΩKn+1→Kn (suc n))
                              (λ i → transportRefl refl i ∙∙ (λ i →
                                     suspΩFun (suc n) (pointerElimFun n f fId)
                                     ((merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁))) i)
                                     -ₖ suspΩFun (suc n) (pointerElimFun n f fId) north)
                                   ∙∙ transportRefl refl i)
                     ∙∙ cong (ΩKn+1→Kn (suc n)) (sym (rUnit ((λ i →
                                     suspΩFun (suc n) (pointerElimFun n f fId)
                                     ((merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁))) i)
                                     -ₖ suspΩFun (suc n) (pointerElimFun n f fId) north))))
                     ∙∙ cong (ΩKn+1→Kn (suc n)) (λ i → cong (λ x → rUnitₖ _ x i)
                                                 (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋ ∙ (λ i₁ → merid pt₀ (~ i₁)))))
                     ∙∙ (λ i → ΩKn+1→Kn (suc n) (congFunct (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋) (sym (merid pt₀)) i))
                     ∙∙ ΩKn+1→Kn-hom (suc n) (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (merid ⌊ x ⌋))
                                              (cong (suspΩFun (suc n) (pointerElimFun n f fId)) (sym (merid pt₀)))
                     ∙∙ cong₂ _+ₖ_ (Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) (f ⌊ x ⌋))
                                   (cong (ΩKn+1→Kn (suc n)) (cong (cong ∣_∣) (cong sym (rCancel (merid (ptSn (suc n)))))))
                     ∙∙ (cong (f ⌊ x ⌋ +ₖ_) (transportRefl (0ₖ _))
                      ∙ rUnitₖ _ (f ⌊ x ⌋))))
  snd pointerIso f zero = {!!}
  snd pointerIso f (suc n) =
    funExt
      (coHomPointerElim _ (λ _ → setTruncIsSet _ _)
        λ f fId → cong ∣_∣₂ (funExt λ {north → refl
                                     ; south → refl
                                     ; (merid a i) → refl}))
  {-
  where
  grIso : GroupIso _ _
  fun (map grIso) = sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid pt₀)) ∙∙ rCancelₖ (suc n) (f north))
  isHom (map grIso) = {!!}
  inv grIso = {!!}
  rightInv grIso = {!!}
  leftInv grIso = {!!} -}
{- fun (map (Suspension₁ isCohomTheoryZ n {A = (A , a)})) =
  sMap λ f x → ΩKn+1→Kn n (sym (rCancelₖ (suc n) (f north)) ∙∙ cong (λ x → f x -ₖ f north) (merid x ∙ sym (merid a)) ∙∙ rCancelₖ (suc n) (f north))
isHom (map (Suspension₁ isCohomTheoryZ zero)) =
  coHomPointedElim2 _ north (λ _ _ → setTruncIsSet _ _)
    {!!}
isHom (map (Suspension₁ isCohomTheoryZ (suc n))) = {!!}
inv (Suspension₁ isCohomTheoryZ n) = {!!}
rightInv (Suspension₁ isCohomTheoryZ n) = {!!}
leftInv (Suspension₁ isCohomTheoryZ n) = {!!} -}
fst (Exactness isCohomTheoryZ f zero) = {!!}
fst (Exactness isCohomTheoryZ {A = A} {B = B} f (suc n)) =
  coHomPointedElim _ (pt B)
    (λ _ → isPropΠ λ _ → propTruncIsProp)
    λ g gId inker
      → pRec propTruncIsProp
              (λ gIdTot → ∣ ∣ (λ {(inl tt) → 0ₖ _ ; (inr b) → g b ; (push a i) → funExt⁻ gIdTot a (~ i)}) ∣₂
                            , cong ∣_∣₂ (funExt λ b → refl) ∣)
              (Iso.fun PathIdTrunc₀Iso inker)
snd (Exactness isCohomTheoryZ {A = A} {B = B} f n) =
  sElim {!snd (Exactness isCohomTheoryZ {A = A} {B = B} f n)!}
        λ g → pRec {!!}
                    (uncurry
                      (sElim {!!}
                             λ cg p → pRec (setTruncIsSet _ _)
                                            (λ gId → cong ∣_∣₂ (funExt λ x → {!g!} ∙∙ {!cg (cfcod (fst f) (fst f x)) ≡ g (fst f x)!} ∙∙ {!cg!}))
                                            (Iso.fun PathIdTrunc₀Iso p)))
  where
  helper : (n : ℕ) → (cg : _) → coHomFun n (fst f) (coHomFun n (cfcod (fst f)) cg) ≡ 0ₕ _
  helper zero =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
          λ g → cong ∣_∣₂ (funExt λ a → cong g (sym (push a) ∙ push (pt A))
                                     ∙∙ {!!}
                                     ∙∙ {!g!})
    where
    help : {!!}
    help = {!!}
  helper (suc n) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
           λ cg → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                         (λ p → (cong ∣_∣₂ (funExt λ x → cong cg (sym (push x))
                                                       ∙ p)))
                         (isConnectedPathKn _ (cg (inl tt)) (0ₖ (suc n)) .fst)
{-
snd (Exactness isCohomTheoryZ {A = A} {B = B} f (suc n)) =
  coHomPointedElim _ (pt B) (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
    λ g gId → pRec (setTruncIsSet _ _)
                    (uncurry λ cg p
                      → subst (isInKer (coHomGr (suc n) (typ B)) (coHomGr (suc n) (typ A))
                                        (coHomMorph (suc n) (fst f)))
                                p
                                (helper cg))
  where
  helper : (cg : _) → coHomFun (suc n) (fst f) (coHomFun (suc n) (cfcod (fst f)) cg) ≡ 0ₕ _
  helper = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                 λ cg → trRec (isProp→isOfHLevelSuc n (setTruncIsSet _ _))
                               (λ p → (cong ∣_∣₂ (funExt λ x → cong cg (sym (push x))
                                                             ∙ p)))
                               (isConnectedPathKn _ (cg (inl tt)) (0ₖ (suc n)) .fst) -}
Dimension isCohomTheoryZ zero =
  (0ₕ _) , sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                 λ f → {!pRec ? ?!}
Dimension isCohomTheoryZ (suc n) = {!!}
BinaryWedge isCohomTheoryZ n = Hⁿ-⋁ _ _ n

{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.K2 where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin

open import Cubical.HITs.EilenbergMacLane1 renaming (elimSet to elimSetEM ; elimProp to elimPropEM)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)

private
  variable
    ℓ : Level

-- ⊕HIT-AbGr

ℤ/2 : AbGroup ℓ-zero
ℤ/2 = Group→AbGroup (ℤGroup/ 2) +ₘ-comm

K₁ = EM₁ (AbGroup→Group ℤ/2)
ΩK₁ = Path K₁ embase embase

K₂ = EM ℤ/2 2





open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma



H¹→Prop : ∀ {ℓ} {A : (KleinBottle → K₁) → Type ℓ} → ((x : _) → isProp (A x))
  → ((l1 l2 : ΩK₁) (sq : Square l2 l2 (sym l1) l1) → A (KleinFun embase l1 l2 sq))
  → (x : _) → A x
H¹→Prop {A = A} pr ind f =
  PT.rec (pr f) (λ {(l1 , l2 , sq , id) → subst A (sym id) (ind _ _ _)}) (H¹→Prop' f)
  where
  characKleinFun : (f : KleinBottle → K₁) → Σ[ x ∈ K₁ ] Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ]
                                      Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq
  characKleinFun f = (f point) , ((cong f line1) , ((cong f line2) , (λ i j → f (square i j) )
             , funExt λ { point → refl ; (line1 i) → refl ; (line2 i) → refl ; (square i i₁) → refl}))

  characKleinFun^ : (f : KleinBottle → K₁) (x y : K₁) (p : x ≡ y)
    → Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ] Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq
    → Σ[ l1 ∈ y ≡ y ] Σ[ l2 ∈ y ≡ y ] Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun y l1 l2 sq
  characKleinFun^ f x = J> λ x → x

  H¹→Prop' : (f : KleinBottle → K₁) → ∃[ l1 ∈ embase ≡ embase ] Σ[ l2 ∈ embase ≡ embase ]
                                        Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f
                                        ≡ KleinFun embase l1 l2 sq
  H¹→Prop' f =
    TR.rec squash₁ (λ r → ∣ characKleinFun^ f (f point) embase (sym r) (characKleinFun f .snd) ∣₁)
      (Iso.fun (PathIdTruncIso 1) (isConnectedEM 1 .snd (∣ f point ∣)))

open import Cubical.HITs.Susp
open import Cubical.Homotopy.Loopspace


H²→Prop : ∀ {ℓ} {A : (KleinBottle → K₂) → Type ℓ} → ((x : _) → isProp (A x))
  → ((sq : (Ω^ 2) (EM∙ ℤ/2 2) .fst) → A (KleinFun ∣ north ∣ refl refl sq))
  → (x : _) → A x
H²→Prop {A = A} pr ind f = PT.rec (pr f) (λ {(sq , fid) → subst A (sym fid) (ind sq)}) (H²→Prop' f)
  where
  characKleinFun^ : (f : KleinBottle → K₂) (x y : K₂)
       (p : x ≡ y) (l1 : x ≡ x) (l1' : y ≡ y)
    → PathP (λ i → p i ≡ p i) l1 l1'
    → (l2 : x ≡ x) (l2' : y ≡ y)
    → PathP (λ i → p i ≡ p i) l2 l2'
    → (Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ KleinFun x l1 l2 sq)
    → Σ[ sq ∈ Square l2' l2' (sym l1') l1' ] f ≡ KleinFun y l1' l2' sq
  characKleinFun^ f x = J> λ l1 → J> λ l2 → J> λ r → r

  H²→Prop' : (f : KleinBottle → K₂)
    → ∃[ sq ∈ (Ω^ 2) (EM∙ ℤ/2 2) .fst ] f ≡ KleinFun ∣ north ∣ refl refl sq
  H²→Prop' f =
    TR.rec (isProp→isSet squash₁)
      (λ p → TR.rec squash₁
            (λ pl → TR.rec squash₁
              (λ pr → ∣ characKleinFun^ f _ _ (sym p) (cong f line1) refl pl (cong f line2) refl pr
                         ((λ i j → f (square i j))
                         , (funExt (λ { point → refl
                                  ; (line1 i) → refl
                                  ; (line2 i) → refl
                                  ; (square i i₁) → refl}))) ∣₁)
              (isConnectedPathP 1 {A = λ i → p (~ i) ≡ p (~ i)}
         (isConnectedPath 2 (isConnectedEM 2) _ _) (cong f line2) refl .fst))
        (isConnectedPathP 1 {A = λ i → p (~ i) ≡ p (~ i)}
         (isConnectedPath 2 (isConnectedEM 2) _ _) (cong f line1) refl .fst))
      (Iso.fun (PathIdTruncIso 2) (isConnectedEM 2 .snd ∣ f point ∣))





open IsAbGroup
open AbGroupStr

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

-const : (x : fst ℤ/2) → -_ (snd ℤ/2) x ≡ x
-const = ℤ/2-elim refl refl

-ₖconst₁ : (x : EM ℤ/2 (suc zero)) → -[ 1 ]ₖ x ≡ x
-ₖconst₁ = elimSetEM _ (λ _ → emsquash _ _)
      refl
      λ g → flipSquare (sym (emloop-sym (AbGroup→Group ℤ/2) g) ∙ cong emloop (-const g))

-ₖconst : (n : ℕ) → (x : EM ℤ/2 (suc n)) → -ₖ x ≡ x
-ₖconst =
  elim+2 -ₖconst₁
    (TR.elim (λ _ → isOfHLevelPath (suc (suc (suc (suc zero)))) (hLevelEM _ (suc (suc zero))) _ _)
    λ { north → refl
      ; south i → ∣ merid embase i ∣
      ; (merid a i) j →
        hcomp (λ r → λ {(i = i0) → ∣ north ∣
                        ; (i = i1) → ∣ merid embase (j ∧ r) ∣
                        ; (j = i0) → EM→ΩEM+1-sym (suc zero) a r i
                        ; (j = i1) → ∣ compPath-filler (merid a) (sym (merid embase)) (~ r) i ∣})
               (EM→ΩEM+1 (suc zero) (-ₖconst₁ a j) i)})
    λ n ind → TR.elim (λ _ → isOfHLevelPath (suc (suc (suc (suc (suc n)))))
                       (hLevelEM _ (suc (suc (suc n)))) _ _)
    λ { north → refl
      ; south i → ∣ merid north i ∣
      ; (merid a i) j →
         hcomp (λ r → λ {(i = i0) → ∣ north ∣
                        ; (i = i1) → ∣ merid north (j ∧ r) ∣
                        ; (j = i0) → EM→ΩEM+1-sym (suc (suc n)) ∣ a ∣ₕ r i
                        ; (j = i1) → ∣ compPath-filler (merid a) (sym (merid north)) (~ r) i ∣})
               (EM→ΩEM+1 (suc (suc n)) (ind ∣ a ∣ j) i)}

H¹K²→G+G : coHom 1 ℤ/2 KleinBottle → fst (dirProdAb ℤ/2 ℤ/2)
H¹K²→G+G = ST.rec (is-set (snd (dirProdAb ℤ/2 ℤ/2)))
                   λ f → ΩEM+1→EM-gen _ _ (cong f line1)
                       , ΩEM+1→EM-gen _ _ (cong f line2)

G+G→H¹K² : fst (dirProdAb ℤ/2 ℤ/2) → coHom 1 ℤ/2 KleinBottle
G+G→H¹K² (g₁ , g₂) =
  ∣ (λ { point → 0ₖ _
      ; (line1 i) → emloop g₁ i
      ; (line2 i) → emloop g₂ i
      ; (square i j) → help j i}) ∣₂
  where
  sideSq : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → Square p p p p
  sideSq p i j =
    hcomp (λ k → λ {(i = i0) → p (j ∨ ~ k)
                   ; (i = i1) → p (j ∧ k)
                   ; (j = i0) → p (i ∨ ~ k)
                   ; (j = i1) → p (i ∧ k)})
          (p i0)

  open import Cubical.Foundations.Path

  main : (g₁ g₂ : _) → PathP (λ i → Path (EM₁ (AbGroup→Group ℤ/2)) (emloop g₂ i) (emloop g₂ i)) (emloop g₁) (emloop g₁)
  main  =
    ℤ/2-elim
      (ℤ/2-elim (sideSq _) (emloop-1g _ ◁ ((λ i j → emloop 1 i) ▷ sym (emloop-1g _))))
      (ℤ/2-elim (flipSquare (emloop-1g _ ◁ ((λ i j → emloop 1 i) ▷ sym (emloop-1g _)))) (sideSq _))

  help : Square {A = EM₁ (AbGroup→Group ℤ/2)}
                 (sym (emloop g₁)) (emloop g₁)
                 (emloop g₂) (emloop g₂)
  help = (sym (emloop-inv (AbGroup→Group ℤ/2) g₁) ∙ cong emloop (-const g₁))
       ◁ main g₁ g₂

G+G→H¹K²→G+G : (x : fst (dirProdAb ℤ/2 ℤ/2)) → H¹K²→G+G (G+G→H¹K² x) ≡ x
G+G→H¹K²→G+G (g₁ , g₂) =
  ΣPathP ((Iso.leftInv (Iso-EM-ΩEM+1 0) g₁)
        , Iso.leftInv (Iso-EM-ΩEM+1 0) g₂)

H¹K²→G+G→H¹K² : (x : _) → G+G→H¹K² (H¹K²→G+G x) ≡ x
H¹K²→G+G→H¹K² =
  ST.elim (λ _ → isSetPathImplicit) (H¹→Prop (λ _ → squash₂ _ _)
    λ l1 l2 sq → cong ∣_∣₂ (funExt (elimSet (λ _ → hLevelEM _ 1 _ _) refl
      (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l1))
      (flipSquare (Iso.rightInv (Iso-EM-ΩEM+1 0) l2)))))

ℤ/2⊕ℤ/2≅H¹[K²,ℤ/2] : AbGroupEquiv (dirProdAb ℤ/2 ℤ/2) (coHomGr 1 ℤ/2 KleinBottle)
fst ℤ/2⊕ℤ/2≅H¹[K²,ℤ/2] = isoToEquiv is
  where
  is : Iso _ _
  Iso.fun is = G+G→H¹K²
  Iso.inv is = H¹K²→G+G
  Iso.rightInv is = H¹K²→G+G→H¹K²
  Iso.leftInv is = G+G→H¹K²→G+G
snd ℤ/2⊕ℤ/2≅H¹[K²,ℤ/2] =
  makeIsGroupHom λ x y → cong ∣_∣₂
    (funExt (elimSet (λ _ → hLevelEM _ 1 _ _) refl
      (flipSquare ((EM→ΩEM+1-hom 0 (fst x) (fst y)
                 ∙ sym (cong₂+₁ (emloop (fst x)) (emloop (fst y))))))
      (flipSquare ((EM→ΩEM+1-hom 0 (snd x) (snd y)
                 ∙ sym (cong₂+₁ (emloop (snd x)) (emloop (snd y))))))))

H¹[K²,ℤ/2]≅ℤ/2⊕ℤ/2 : AbGroupEquiv (coHomGr 1 ℤ/2 KleinBottle) (dirProdAb ℤ/2 ℤ/2)
H¹[K²,ℤ/2]≅ℤ/2⊕ℤ/2 = invGroupEquiv ℤ/2⊕ℤ/2≅H¹[K²,ℤ/2]

open import Cubical.Foundations.GroupoidLaws
transferCube : ∀ {ℓ} {A : Type ℓ} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z}
  → Square r q p s → p ∙ q ≡ r ∙ s
transferCube {p = p} {q = q} {r = r} {s = s} sq i j =
  hcomp (λ k → λ {(i = i0) → compPath-filler p q k j
                 ; (i = i1) → compPath-filler' r s k j
                 ; (j = i0) → r (~ k ∧ i)
                 ; (j = i1) → q (k ∨ i)})
        (sq j i)

transferCube' : ∀ {ℓ} {A : Type ℓ} {x : A} (sq : Square (λ _ → x) refl refl refl)
             → transferCube sq ≡ cong (_∙ refl) (flipSquare sq)
transferCube' {x = x} sq k i j =
  hcomp (λ r → λ {(i = i0) → rUnit (λ _ → x) r j
                 ; (i = i1) → rUnit (λ _ → x) r j
                 ; (j = i0) → x
                 ; (j = i1) → x
                 ; (k = i1) → cong (λ x → rUnit x r) (flipSquare sq) i j})
        (sq j i)

open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

symΩEM : (x : K₂) → ∣ north ∣ ≡ x → TypeOfHLevel ℓ-zero 3
symΩEM = TR.elim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelTypeOfHLevel 3)
  λ { north → λ p → (p ≡ sym p) , isOfHLevelPath 3 (hLevelEM _ 2 _ _) _ _
    ; south → λ p → (p ∙ cong ∣_∣ₕ (sym (merid embase)) ≡ cong ∣_∣ₕ (merid embase) ∙ sym p) , isOfHLevelPath 3 (hLevelEM _ 2 _ _) _ _
    ; (merid a i) → h a i}
  where
  h : (a : _) → PathP (λ i → Path K₂ ∣ north ∣ ∣ merid a i ∣ → TypeOfHLevel ℓ-zero 3)
                       (λ p → (p ≡ sym p) , isOfHLevelPath 3 (hLevelEM _ 2 _ _) _ _)
                       λ p → (p ∙ cong ∣_∣ₕ (sym (merid embase)) ≡ cong ∣_∣ₕ (merid embase) ∙ sym p)
                                           , isOfHLevelPath 3 (hLevelEM _ 2 _ _) _ _
  h a = toPathP (flipTransport {A = λ i → Path K₂ ∣ north ∣ ∣ merid a i ∣ → TypeOfHLevel ℓ-zero 3}
                (funExt (λ p → Σ≡Prop (λ _ → isPropIsOfHLevel 3)
                  (((s2 p
                   ∙ λ i → k p i ≡ pr p (~ i))
                  ∙ λ i → l p (~ i) ∙ sym s ≡ s ∙ sym (l p (~ i)) )
                 ∙ sym (transportRefl _)))))
    where
    s : Path K₂ ∣ north ∣ ∣ south ∣
    s i = ∣ merid embase i ∣

    ap : Path K₂ ∣ north ∣ ∣ south ∣
    ap i = ∣ merid a i ∣

    l : (p : _) → transport (λ i → Path K₂ ∣ north ∣ ∣ merid a i ∣) p ≡ p ∙ cong ∣_∣ₕ (merid a)
    l p i = transp (λ j → Path K₂ ∣ north ∣ ∣ merid a (j ∨ i) ∣) i
                   (compPath-filler p (cong ∣_∣ₕ (merid a)) i)

    k : (p : Path K₂ ∣ north ∣ ∣ north ∣) → p ∙ EM→ΩEM+1 1 a ≡ (p ∙ ap) ∙ sym s
    k p = (λ i → p ∙ (cong-∙ ∣_∣ₕ (merid a) (sym (merid embase))) i) ∙ assoc p ap (sym s)

    pr : (p : _) → s ∙ sym (p ∙ ap) ≡ sym (sym (EM→ΩEM+1 1 a) ∙ p)
    pr p =
        (((λ i → s ∙ (symDistr p ap i))
        ∙ assoc _ _ _
        ∙ (λ i → symDistr ap (sym s) (~ i) ∙ sym p)
        ∙ λ i → sym (cong-∙ ∣_∣ₕ (merid a) (sym (merid embase)) (~ i)) ∙ sym p)
        ∙ (isCommΩEM _ _ _))
      ∙ sym (symDistr (EM→ΩEM+1 1 a) p)
      ∙ cong sym (cong (_∙ p) (cong (EM→ΩEM+1 1) (sym (-ₖconst 0 a)) ∙ EM→ΩEM+1-sym 1 a))

    gr : (p : Path K₂ ∣ north ∣ ∣ north ∣) → PathP (λ i → ∣ north ∣ ≡ EM→ΩEM+1 1 a i) p (p ∙ EM→ΩEM+1 1 a)
    gr p = compPath-filler p (EM→ΩEM+1 1 a)

    gr' : (p : Path K₂ ∣ north ∣ ∣ north ∣) → PathP (λ i → ∣ north ∣ ≡ EM→ΩEM+1 1 a i) (sym p) (sym (sym (EM→ΩEM+1 1 a) ∙ p))
    gr' p i = sym (compPath-filler' (sym (EM→ΩEM+1 1 a)) p i)

    s2 : (p : _) → (p ≡ sym p) ≡ (p ∙ EM→ΩEM+1 1 a ≡ sym (sym (EM→ΩEM+1 1 a) ∙ p))
    s2 p i = gr p i ≡ gr' p i

symr : (x : K₂) (p : ∣ north ∣ ≡ x) → symΩEM x p .fst
symr = J> refl

br : (x : K₂) (p : x ≡ x) → p ≡ sym p
br = EM.EM-raw'-elim ℤ/2 2 (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPath 3 (hLevelEM ℤ/2 2 _ _) _ _)
      (EM-raw'-trivElim ℤ/2 1 (λ _ → isSetΠ λ _ → hLevelEM ℤ/2 2 _ _ _ _)
        (symr ∣ north ∣))

br-refl : br (0ₖ 2) refl ≡ refl
br-refl = transportRefl refl

fun1 : (f : KleinBottle → K₂) → (λ j → f (line2 j)) ∙ (λ i → f (line1 i)) ≡ (λ j → f (line2 j)) ∙ (λ i → f (line1 i))
fun1 f = (λ i → (λ j → f (line2 j)) ∙ br _ (λ i → f (line1 i)) i) ∙ isCommΩEM-base 1 _ _ _ ∙ transferCube (λ i j → f (square i j))

fun'2 : (x : K₂) (p : refl {x = x} ≡ refl) → fst ℤ/2
fun'2 x p = ΩEM+1→EM-gen 0 (ΩEM+1→EM-gen 1 x refl) (cong (ΩEM+1→EM-gen 1 x) p)

fun2 : {x : K₂} {p : x ≡ x} (q : p ≡ p) → fst ℤ/2
fun2 {x = x} {p = p} q = fun'2 x ((sym (rCancel p) ∙∙ cong (_∙ sym p) q ∙∙ rCancel p))

l : isCommΩEM-base {G = ℤ/2} 1 ∣ north ∣ refl refl ≡ refl
l = ∙∙lCancel _

fun1-nice : (p : Square {A = K₂} refl refl (sym refl) refl)
  → fun1 (KleinFun (0ₖ 2) refl refl p)
  ≡ λ i → p (~ i) ∙ refl
fun1-nice p =
     cong₂ _∙_ (cong (cong (λ x → (λ _ → ∣ north ∣) ∙ x)) br-refl)
               (cong₂ _∙_ l (transferCube' p))
  ∙∙ sym (lUnit _)
  ∙∙ (sym (lUnit _)
    ∙ cong (cong (λ x → x ∙ refl)) (sym (sym≡flipSquare p)))


fff : (p : Square {A = K₂} refl refl (sym refl) refl)
  → fun2 (fun1 (KleinFun (0ₖ 2) refl refl p))
  ≡ ΩEM+1→EM 0 (cong (ΩEM+1→EM 1) p)
fff p = cong fun2 (fun1-nice p)
      ∙ (λ j → fun2 (λ i → rUnit (p (~ i)) (~ j)))
      ∙ cong (fun'2 _) help
      ∙ ΩEM+1→EM-sym 0 (cong (ΩEM+1→EM 1) p)
      ∙ -const _
  where
  help : sym (rCancel refl) ∙∙ (λ i → p (~ i) ∙ refl) ∙∙ rCancel refl
       ≡ λ i j → p (~ i) j
  help k i = hcomp (λ r → λ {(k = i1) → p (~ i)
                            ; (i = i0) → rUnit (refl {x = 0ₖ 2}) (~ r ∧ ~ k)
                            ; (i = i1) → rUnit (refl {x = 0ₖ 2}) (~ r ∧ ~ k)})
                   (rUnit (p (~ i)) (~ k))

H²K²→G : coHom 2 ℤ/2 KleinBottle → fst ℤ/2
H²K²→G =
  ST.rec isSetFin
    λ f → fun2 (fun1 f)

open import Cubical.Foundations.Equiv.HalfAdjoint

Iso-Ω²K²-G : Iso (fst ((Ω^ 2) (EM∙ ℤ/2 2))) (fst ℤ/2)
Iso-Ω²K²-G = compIso (congIso (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 1))) (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 0))

G→Ω²K² : fst ℤ/2 → fst ((Ω^ 2) (EM∙ ℤ/2 2))
G→Ω²K² g = Iso.inv Iso-Ω²K²-G g

G→H²K² : fst ℤ/2 → coHom 2 ℤ/2 KleinBottle
G→H²K² g = ∣ KleinFun (0ₖ 2) refl refl (G→Ω²K² g) ∣₂

H²K²→G→H²K² : (f : coHom 2 ℤ/2 KleinBottle) → G→H²K² (H²K²→G f) ≡ f
H²K²→G→H²K² =
  ST.elim (λ _ → isSetPathImplicit)
    (H²→Prop (λ _ → squash₂ _ _)
      λ sq → cong G→H²K² (fff sq)
            ∙ cong ∣_∣₂ (funExt λ { point → refl
                                ; (line1 i) → refl
                                ; (line2 i) → refl
                                ; (square i j) k → Iso.leftInv Iso-Ω²K²-G sq k i j}))

G→H²K²→G : (g : fst ℤ/2) → H²K²→G (G→H²K² g) ≡ g
G→H²K²→G g = fff (G→Ω²K² g) ∙ (Iso.rightInv Iso-Ω²K²-G g)

0ₕ≡ : Path (coHom 2 ℤ/2 KleinBottle) (0ₕ 2) (∣ (KleinFun ∣ north ∣ refl refl (λ _ _ → ∣ north ∣)) ∣₂)
0ₕ≡ = cong ∣_∣₂ (funExt λ { point → refl ; (line1 i) → refl ; (line2 i) → refl ; (square i i₁) → refl}) --

pres0' : H²K²→G (0ₕ _) ≡ 0
pres0' = cong H²K²→G 0ₕ≡
       ∙ fff (λ _ _ → ∣ north ∣ₕ)
       ∙ refl

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
-- isAbGroup

Isoℤ/2-morph' : {A : Type} (f : A ≃ fst ℤ/2) (0A : A) → 0 ≡ fst f 0A → (_+'_ : A → A → A) (-m : A → A)
  → (λ x → x) ≡ -m
  → (e : IsAbGroup 0A _+'_ -m)
  → IsGroupHom  (AbGroup→Group (A , abgroupstr 0A _+'_ (λ x → -m x) e) .snd) (fst f) (AbGroup→Group ℤ/2 .snd)
Isoℤ/2-morph' =
  EquivJ (λ A f → (0A : A) → 0 ≡ fst f 0A → (_+'_ : A → A → A) (-m : A → A)
  → (λ x → x) ≡ -m
  → (e : IsAbGroup 0A _+'_ -m)
  → IsGroupHom  (AbGroup→Group (A , abgroupstr 0A _+'_ (λ x → -m x) e) .snd) (fst f) (AbGroup→Group ℤ/2 .snd))
  (J> λ _+'_ → J>
    λ e → makeIsGroupHom (ℤ/2-elim (ℤ/2-elim (IsAbGroup.+IdR e fzero)
      (IsAbGroup.+IdL e 1))
      (ℤ/2-elim (IsAbGroup.+IdR e 1)
        (IsAbGroup.+InvR e 1))))


private
  is : Iso _ _
  Iso.fun is = H²K²→G
  Iso.inv is = G→H²K²
  Iso.rightInv is = G→H²K²→G
  Iso.leftInv is = H²K²→G→H²K²

H²[K²,ℤ/2]≅ℤ/2 : AbGroupEquiv (coHomGr 2 ℤ/2 KleinBottle) ℤ/2
fst H²[K²,ℤ/2]≅ℤ/2 = isoToEquiv is
snd H²[K²,ℤ/2]≅ℤ/2 =
  Isoℤ/2-morph' (isoToEquiv is) (0ₕ 2) (sym pres0') _+ₕ_ (-ₕ_)
    (funExt (ST.elim (λ _ → isSetPathImplicit)
      (λ f → cong ∣_∣₂ (funExt λ x → sym (-ₖconst 1 (f x))))))
    (AbGroupStr.isAbGroup (coHomGr 2 ℤ/2 KleinBottle .snd))


open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin

open import Cubical.HITs.EilenbergMacLane1 renaming (elimSet to elimSetEM ; elimProp to elimPropEM)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.Truncation as TR
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.Susp

{-
private
  variable
    ℓ : Level
-}
open import Cubical.HITs.Susp
open import Cubical.Homotopy.Loopspace

open IsAbGroup
open AbGroupStr

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

α-raw : KleinBottle → EM ℤ/2 1
α-raw = KleinFun embase (emloop 1) refl (flipSquare (sym (emloop-inv (AbGroup→Group ℤ/2) 1)))

β-raw : KleinBottle → EM ℤ/2 1
β-raw = KleinFun embase refl (emloop 1) (λ _ i → emloop 1 i)

α : coHom 1 ℤ/2 KleinBottle
α = ∣ KleinFun embase (emloop 1) refl (flipSquare (sym (emloop-inv (AbGroup→Group ℤ/2) 1))) ∣₂

β : coHom 1 ℤ/2 KleinBottle
β = ∣ KleinFun embase refl (emloop 1) (λ _ i → emloop 1 i) ∣₂

open import Cubical.Algebra.Ring



open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)

emloop' : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong₂ (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
        ≡ refl
emloop' p = cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
          ∙∙ (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                  ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)
          ∙∙ sym (rUnit refl)


FF = (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})

R : ∀ {ℓ} {A B : Type ℓ} {x y : A} (f : A → A → B)
  → (p : x ≡ y) → sym (cong (λ x₁ → f x₁ y) (sym p) ∙ cong (f x) (sym p)) ≡
      cong (λ x₁ → f x₁ x) p ∙ cong (f y) p
R {x = x} {y = y} f p i j =
  hcomp (λ k → λ {(i = i0) → compPath-filler (cong (λ x₁ → f x₁ y) (sym p)) (cong (f x) (sym p)) k (~ j)
                 ; (i = i1) → compPath-filler (cong (λ x₁ → f x₁ x) p) (cong (f y) p) k j
                 ; (j = i0) → f x (p (~ k ∧ ~ i))
                 ; (j = i1) → f y (p (k ∨ ~ i))})
        (f (p j) (p (~ i)))

myF : (p : Path (EM ℤ/2 1) embase embase)
  → sym
      (cong (λ x₁ → FF x₁ embase) (sym p) ∙ cong (FF embase) (sym p))
      ≡ cong (λ x₁ → FF x₁ embase) p ∙ cong (FF embase) p
myF = λ p → (cong sym (sym (rUnit (cong (λ x₁ → FF x₁ embase) (sym p)))) ∙∙ (λ i j → FF (p j) (p (~ i))) ∙∙ rUnit _)

R' : (p : Path (EM ℤ/2 1) embase embase)
  → R FF p ≡ myF p
R' p k i j =
  hcomp (λ r → λ {(i = i0) → compPath-filler (cong (λ x₁ → FF x₁ embase) (sym p)) (cong (FF embase) (sym p)) r (~ j)
                 ; (i = i1) → compPath-filler (cong (λ x₁ → FF x₁ embase) (sym p)) (cong (FF embase) (sym p)) r (~ j)
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣})
        (FF (p j) (p (~ i)))

R-refl : ∀ {ℓ} {A B : Type ℓ} {x : A} (f : A → A → B)
      → R {x = x} f refl ≡ refl
R-refl {x = x} f k i j =
  hcomp (λ r → λ {(i = i0) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)
                 ; (i = i1) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)
                 ; (j = i0) → f x x
                 ; (j = i1) → f x x
                 ; (k = i1) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)})
        (f x x)

cong₂Funct-cong-sym : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → A → B)
  → cong₂Funct f p p ∙ sym (R f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p))
cong₂Funct-cong-sym {A = A} {B = B} =
  J (λ y p → (f : A → A → B) → cong₂Funct f p p ∙ sym (R f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p)))
        λ f → (λ i → cong₂Funct f refl refl ∙ sym (R-refl f i))
              ∙ sym (rUnit _) -- λ f → rUnit _ ∙ λ i → cong sym (cong₂Funct f refl refl) ∙ R-refl f (~ i)

emloop''2 : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong sym (emloop' (sym p))
  ≡ (((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p) ∙ sym (myF p))
  ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
  ∙∙ sym (rUnit refl))
emloop''2 p i = (cong₂Funct-cong-sym p FF (~ i)
  ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
  ∙∙ sym (rUnit refl))

gr : ∀ {ℓ} {A : Type ℓ} {x y z w t : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ t)
  → ((p ∙ q) ∙∙ r ∙∙ s) ≡ (p ∙∙ (q ∙ r) ∙∙ s)
gr p q r s i = compPath-filler p q (~ i) ∙∙ compPath-filler' q r i ∙∙ s

emloop''' : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong sym (emloop' (sym p))
  ≡ (((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p))
  ∙∙ (sym (myF p) ∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)))
  ∙∙ sym (rUnit refl))
emloop''' p = emloop''2 p ∙ gr (cong₂Funct FF p p) (sym (myF p)) (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i) ∙ (λ j → embase ⌣ₖ⊗ p j)) (sym (rUnit refl))


KleinFunβ : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (β-raw x) (β-raw x)) ≡ ∣ north ∣ₕ
KleinFunβ point = refl
KleinFunβ (line1 i) = refl
KleinFunβ (line2 i) j = emloop' (emloop 1) j i
KleinFunβ (square i j) k = emloop' (emloop 1) k j

ℤ/ℤ⨂→ : (x y : fst ℤ/2) → fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))
ℤ/ℤ⨂→ x y = sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (x ⊗ y)) ∙∙ EM→ΩEM+1-0ₖ 1

ℤ/2→ : fst ℤ/2 → fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))
ℤ/2→ g = ℤ/ℤ⨂→ g g

ℤ/2→' : fst ℤ/2 → fst ((Ω^ 2) (EM∙ ℤ/2 2))
ℤ/2→' g = (sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 g) ∙∙ EM→ΩEM+1-0ₖ 1)

ℤ/2→Flip''-gen : (x y : fst ℤ/2) → (ℤ/ℤ⨂→ x y) ≡ sym (ℤ/ℤ⨂→ y x)
ℤ/2→Flip''-gen x y i j =
  hcomp (λ k → λ {(j = i0) → EM→ΩEM+1-0ₖ 1 k
                 ; (j = i1) → EM→ΩEM+1-0ₖ 1 k})
         (braa i j)
  where
  lem3 : (x y : _) → Path (ℤ/2 ⨂₁ ℤ/2) (x ⊗ y) (y ⊗ x)
  lem3 = ℤ/2-elim (ℤ/2-elim refl (⊗AnnihilL 1 ∙ sym (⊗AnnihilR 1)))
            (ℤ/2-elim (⊗AnnihilR 1 ∙ sym (⊗AnnihilL 1)) refl)

  lem2 : (x y : _) → GroupStr.inv (snd (AbGroup→Group (ℤ/2 ⨂ ℤ/2))) (y ⊗ x) ≡ x ⊗ y
  lem2 x y = cong (_⊗ x) (-const y) ∙ lem3 y x

  braa : cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (emloop (x ⊗ y))
       ≡ cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (sym (emloop (y ⊗ x)))
  braa = cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1)) (cong emloop (sym (lem2 x y)))
       ∙ cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1))
          (emloop-inv (AbGroup→Group (ℤ/2 ⨂ ℤ/2)) (y ⊗ x))


ℤ/2→Flip'' : ℤ/2→ (fsuc fzero) ≡ sym (ℤ/2→ (fsuc fzero))
ℤ/2→Flip'' = ℤ/2→Flip''-gen 1 1

ℤ/2→Flip : ℤ/2→ (fsuc fzero) ≡ λ k i → ℤ/2→ (fsuc fzero) k (~ i)
ℤ/2→Flip = ℤ/2→Flip'' ∙ sym≡cong-sym (ℤ/2→ (fsuc fzero))

ℤ/2→Flip' : ℤ/2→ (fsuc fzero) ≡ flipSquare (ℤ/2→ (fsuc fzero))
ℤ/2→Flip' = ℤ/2→Flip ∙∙ sym (sym≡cong-sym (ℤ/2→ (fsuc fzero))) ∙∙ sym≡flipSquare (ℤ/2→ (fsuc fzero))


Cube1 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube1 i k r =
  hcomp (λ j →
    λ {(i = i0) → ∣ north ∣
     ; (i = i1) → ∣ north ∣
     ; (k = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
     ; (k = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
     ; (r = i0) → ℤ/2→ (fsuc fzero) k i
     ; (r = i1) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                         (λ i j → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) j)
                                         (EM→ΩEM+1-0ₖ 1) (~ j) k (~ i) })
         (ℤ/2→Flip r k i)

Cube2 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube2 i k r =
  hcomp (λ j →
      λ {(i = i0) → ∣ north ∣
       ; (i = i1) → ∣ north ∣
       ; (k = i0) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)
       ; (k = i1) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)})
   (Cube1 i k r)

Cube3 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube3 i k r =
  hcomp (λ j →
     λ {(i = i0) →  ∣ north ∣
      ; (i = i1) →  ∣ north ∣
      ; (k = i0) → ((λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r))
                   ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) (~ r)) (~ i)
      ; (k = i1) → ((λ k → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j))
                    ∙ λ k → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j)) (~ i)
      ; (r = i0) → (sym (rUnit refl) ∙∙ ℤ/2→ (fsuc fzero) ∙∙ rUnit refl) k i
      ; (r = i1) → compPath-filler (sym (myF (emloop 1)))
                     (((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                                                  ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i)))
                     j k (~ i)})
  (Cube2 i k r)

Cube4 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube4 i k r =
  hcomp (λ j →
   λ {(i = i0) → ∣ north ∣
    ; (i = i1) → ∣ north ∣
    ; (k = i1) → rUnit (λ _ → FF embase embase) (~ j) i
    ; (r = i0) → doubleCompPath-filler (sym (rUnit (λ _ → FF embase embase))) (ℤ/2→ (fsuc fzero)) (rUnit (λ _ → FF embase embase)) (~ j) k i
    ; (r = i1) → doubleCompPath-filler (((cong₂Funct FF (emloop 1) (emloop 1))))
                     (sym (myF (emloop 1)) ∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i)))
                    (sym (rUnit refl)) j k (~ i)})
   (Cube3 i k r)

Cube5 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube5 i j k = hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (emloop 1) (~ r ∨ k) (~ i)
                 ; (j = i1) → Cube4 i k r
                 ; (k = i0) → emloop' (emloop 1) (~ r) (~ i)
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
                 (ℤ/2→ (fsuc fzero) (j ∧ k) i)

Cube6 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube6 i j k =
  hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
                 ; (j = i1) → emloop''' (emloop 1) (~ r) k (~ i)
                 ; (k = i0) → FF (emloop 1 (~ i)) (emloop 1 (~ i))
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
                 (Cube5 i j k)

Cube7 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube7 i j k =
  hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
                 ; (j = i1) → emloop' (λ i₁ → α-raw (square i₁ r)) k i
                 ; (k = i0) → FF (α-raw (square i (j ∧ r))) (α-raw (square i (j ∧ r)))
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
           (Cube6 i j k)

KleinFunβα : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (β-raw x) (α-raw x))
                                  ≡ KleinFun (0ₖ 2) refl refl (ℤ/2→ 1) x
KleinFunβα point = refl
KleinFunβα (line1 i) k = ∣ north ∣
KleinFunβα (line2 i) = ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 i)
KleinFunβα (square i j) k =
  hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → FF (emloop 1 j) (α-raw (square i (j ∧ r)))
                 ; (k = i1) → (ℤ/2→ (fsuc fzero)) i j})
    (hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1)) (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1) )) (EM→ΩEM+1-0ₖ 1) (~ r) (~ i) j
                 ; (k = i1) → (ℤ/2→ (fsuc fzero)) i j})
        (ℤ/2→Flip'' (~ k) i j))

KleinFunα⊗ : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2} {n = 1} {m = 1} (α-raw x) (α-raw x))
                                    ≡ KleinFun (0ₖ 2) refl refl (ℤ/2→ 1) x
KleinFunα⊗ x = KleinFunα' x ∙ λ i → KleinFun (0ₖ 2) refl refl (ℤ/2→Flip' (~ i)) x
  where
  KleinFunα' : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (α-raw x) (α-raw x))
                                    ≡ KleinFun (0ₖ 2) refl refl (flipSquare (ℤ/2→ 1)) x
  KleinFunα' point = refl
  KleinFunα' (line1 i) k = emloop' (cong α-raw line1) k i
  KleinFunα' (line2 i) = refl
  KleinFunα' (square i j) k = Cube7 i j k

Klein' : (x : KleinBottle)
  → (KleinFun (0ₖ 2) refl refl (ℤ/2→ 1) x)
   ≡ KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x
Klein' point = refl
Klein' (line1 i) = refl
Klein' (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
Klein' (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k)

Klein'' : (x : KleinBottle)
  → (KleinFun (0ₖ 2) refl refl (ℤ/2→' 1) x)
   ≡ KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x
Klein'' point = refl
Klein'' (line1 i) = refl
Klein'' (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
Klein'' (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop 1 i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop 1 i) k)

KleinFunα⊗'' : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 (KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x)
                          ≡ (KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x)
KleinFunα⊗'' point = refl
KleinFunα⊗'' (line1 i) = refl
KleinFunα⊗'' (line2 i) k = ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2) (merid embase) (sym (merid embase)) k i ∣ₕ
KleinFunα⊗'' (square i j) k = ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2) (merid (emloop (1 ⊗ 1) i)) (sym (merid embase)) k j ∣ₕ

KleinFunβ⊗'' : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 ∣ north ∣
                          ≡ (KleinFun (0ₖ 2) refl refl refl x)
KleinFunβ⊗'' point = refl
KleinFunβ⊗'' (line1 i) = refl
KleinFunβ⊗'' (line2 i) = refl
KleinFunβ⊗'' (square i j) = refl


lem2 : G→Ω²K² 1 ≡ ℤ/2→' 1
lem2 k i j = hcomp (λ r → λ {(i = i0) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                            ; (i = i1) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                            ; (j = i0) → ∣ north ∣
                            ; (j = i1) → ∣ north ∣ })
                   (EM→ΩEM+1 1 (EM→ΩEM+1 0 1 i) j)


open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
FF-comm : (x : EM ℤ/2 1)
  → cup∙ {G' = ℤ/2} {H' = ℤ/2} 1 1 x ≡ ((λ y → FF y x) , (0ₖ-⌣ₖ⊗ 1 1 x))
FF-comm =
  EM-raw'-elim ℤ/2 1 (λ _ → isOfHLevel↑∙ 1 0 _ _)
    λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y → funExt⁻ (cong fst (Rs' y)) x)
  where -- isOfHLevel↑∙'
  Rs' : (y : EM ℤ/2 1) → Path (EM-raw'∙ ℤ/2 1 →∙ EM∙ (ℤ/2 ⨂ ℤ/2) 2)
                               ((λ x → FF (EM-raw'→EM ℤ/2 1 x) y) , refl)
                               ((λ x → FF y (EM-raw'→EM ℤ/2 1 x)) , ⌣ₖ-0ₖ⊗ 1 1 y)
  Rs' = EM-raw'-elim _ 1 (λ _ → isOfHLevel↑∙' 1 1 _ _)
          λ x → →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ y → L y x)
    where
    L : (x y : EM₁-raw (AbGroup→Group ℤ/2))
      → FF (EM-raw'→EM ℤ/2 1 x) (EM-raw'→EM ℤ/2 1 y)
      ≡ FF (EM-raw'→EM ℤ/2 1 y) (EM-raw'→EM ℤ/2 1 x)
    L embase-raw embase-raw = refl
    L embase-raw (emloop-raw g i) = sym (⌣ₖ-0ₖ⊗ 1 1 (emloop g i))
    L (emloop-raw g i) embase-raw = ⌣ₖ-0ₖ⊗ 1 1 (emloop g i)
    L (emloop-raw g i) (emloop-raw h j) k =
      hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                     ; (i = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                     ; (j = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                     ; (j = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                     ; (k = i0) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                    (λ j i → EM→ΩEM+1 1 (EM→ΩEM+1 0 (g ⊗ h) j) i) (EM→ΩEM+1-0ₖ 1) (~ r) j i
                     ; (k = i1) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                    (λ j i → EM→ΩEM+1 1 (EM→ΩEM+1 0 (h ⊗ g) j) i) (EM→ΩEM+1-0ₖ 1) (~ r) i j})
            (help k i j)
      where
      help : flipSquare (ℤ/ℤ⨂→ g h) ≡ ℤ/ℤ⨂→ h g
      help = sym (sym≡flipSquare (ℤ/ℤ⨂→ g h))
           ∙ cong sym (ℤ/2→Flip''-gen g h)

⌣ₖ⊗-commℤ/2₁,₁ : (x y : EM ℤ/2 1) → _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1} x y ≡ (y ⌣ₖ⊗ x)
⌣ₖ⊗-commℤ/2₁,₁ x y i = FF-comm x i .fst y

⌣ₖ-commℤ/2₁,₁ : (x y : EM ℤ/2 1) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} x y ≡ (y ⌣ₖ x)
⌣ₖ-commℤ/2₁,₁ x y = cong (EMTensorMult 2) (⌣ₖ⊗-commℤ/2₁,₁ x y)

⌣-commℤ/2₁,₁ : ∀ {ℓ} {A : Type ℓ} (x y : coHom 1 ℤ/2 A) → (_⌣_ {G'' = ℤ/2Ring} x y) ≡ (y ⌣ x)
⌣-commℤ/2₁,₁ = ST.elim2 (λ _ _ → isSetPathImplicit)
                λ f g → cong ∣_∣₂ (funExt λ x → ⌣ₖ-commℤ/2₁,₁ (f x) (g x))


almostα : (x : KleinBottle) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} (α-raw x) (α-raw x)
                           ≡ KleinFun (0ₖ 2) refl refl (G→Ω²K² 1) x
almostα x = cong (EMTensorMult {G'' = ℤ/2Ring} 2) (KleinFunα⊗ x ∙ Klein' x)
        ∙∙ KleinFunα⊗'' x
        ∙∙ sym (Klein'' x)
         ∙ λ i → KleinFun (0ₖ 2) refl refl (lem2 (~ i)) x

cupIdα : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α α
       ≡ G→H²K² 1
cupIdα = cong ∣_∣₂ (funExt almostα)

G→Ω²K²-refl : G→Ω²K² 0 ≡ refl
G→Ω²K²-refl = Iso.leftInv Iso-Ω²K²-G refl

cupIdΒ : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β β
       ≡ ∣ KleinFun (0ₖ 2) refl refl (G→Ω²K² 0) ∣₂
cupIdΒ = cong ∣_∣₂ (funExt λ x → cong (EMTensorMult {G'' = ℤ/2Ring} 2) (KleinFunβ x)
                        ∙ KleinFunβ⊗'' x
                        ∙ λ i → KleinFun ∣ north ∣ refl refl (G→Ω²K²-refl (~ i)) x)

βα↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β α) ≡ 1
βα↦1 = cong H²K²→G (cong ∣_∣₂ (funExt (λ x → cong (EMTensorMult {G'' = ℤ/2Ring} 2) (KleinFunβα x ∙ Klein' x)
                   ∙∙ (KleinFunα⊗'' x  ∙ sym (Klein'' x))
                   ∙∙ λ i → KleinFun ∣ north ∣ refl refl (lem2 (~ i)) x)))
      ∙ G→H²K²→G 1

β↦0,1 : H¹K²→G+G β ≡ (0 , 1)
β↦0,1 = refl

β²↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β β) ≡ 0
β²↦1 = cong H²K²→G cupIdΒ ∙ G→H²K²→G 0


α↦1 : H¹K²→G+G α ≡ (1 , 0)
α↦1 = refl

α⌣α↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α α) ≡ 1
α⌣α↦1 = cong H²K²→G cupIdα ∙ G→H²K²→G 1

αβ↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α β) ≡ 1
αβ↦1 = cong H²K²→G (⌣-commℤ/2₁,₁ α β) ∙ βα↦1

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
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.KleinBottle

private
  variable
    ℓ : Level

-- ⊕HIT-AbGr

ℤ/2 : AbGroup ℓ-zero
ℤ/2 = Group→AbGroup (ℤGroup/ 2) +ₘ-comm

K₁ = EM₁ (AbGroup→Group ℤ/2)
ΩK₁ = Path K₁ embase embase

K₂ = EM ℤ/2 2

Klein→-fun : ∀ {ℓ} {A : Type ℓ} (x : A)
     (l1 l2 : x ≡ x)
  → Square l2 l2 (sym l1) l1
  → KleinBottle → A
Klein→-fun x l1 l2 sq point = x
Klein→-fun x l1 l2 sq (line1 i) = l1 i
Klein→-fun x l1 l2 sq (line2 i) = l2 i
Klein→-fun x l1 l2 sq (square i i₁) = sq i i₁



open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma


charac' : (f : KleinBottle → K₁) → Σ[ x ∈ K₁ ] Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ]
                                    Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ Klein→-fun x l1 l2 sq
charac' f = (f point) , ((cong f line1) , ((cong f line2) , (λ i j → f (square i j) )
           , funExt λ { point → refl ; (line1 i) → refl ; (line2 i) → refl ; (square i i₁) → refl}))

H¹→Prop : ∀ {ℓ} {A : (KleinBottle → K₁) → Type ℓ} → ((x : _) → isProp (A x))
  → ((l1 l2 : ΩK₁) (sq : Square l2 l2 (sym l1) l1) → A (Klein→-fun embase l1 l2 sq))
  → (x : _) → A x
H¹→Prop {A = A} pr ind f =
  PT.rec (pr f) (λ {(l1 , l2 , sq , id) → subst A (sym id) (ind _ _ _)}) (H¹→Prop' f)
  where
  charac'→ : (f : KleinBottle → K₁) (x y : K₁) (p : x ≡ y)
    → Σ[ l1 ∈ x ≡ x ] Σ[ l2 ∈ x ≡ x ] Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ Klein→-fun x l1 l2 sq
    → Σ[ l1 ∈ y ≡ y ] Σ[ l2 ∈ y ≡ y ] Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ Klein→-fun y l1 l2 sq
  charac'→ f x = J> λ x → x

  H¹→Prop' : (f : KleinBottle → K₁) → ∃[ l1 ∈ embase ≡ embase ] Σ[ l2 ∈ embase ≡ embase ]
                                        Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f
                                        ≡ Klein→-fun embase l1 l2 sq
  H¹→Prop' f =
    TR.rec squash₁ (λ r → ∣ charac'→ f (f point) embase (sym r) (charac' f .snd) ∣₁)
      (Iso.fun (PathIdTruncIso 1) (isConnectedEM 1 .snd (∣ f point ∣)))

open import Cubical.HITs.Susp
open import Cubical.Homotopy.Loopspace


H²→Prop : ∀ {ℓ} {A : (KleinBottle → K₂) → Type ℓ} → ((x : _) → isProp (A x))
  → ((sq : (Ω^ 2) (EM∙ ℤ/2 2) .fst) → A (Klein→-fun ∣ north ∣ refl refl sq))
  → (x : _) → A x
H²→Prop {A = A} pr ind f = PT.rec (pr f) (λ {(sq , fid) → subst A (sym fid) (ind sq)}) (H²→Prop' f)
  where
  charac'→ : (f : KleinBottle → K₂) (x y : K₂)
       (p : x ≡ y) (l1 : x ≡ x) (l1' : y ≡ y)
    → PathP (λ i → p i ≡ p i) l1 l1'
    → (l2 : x ≡ x) (l2' : y ≡ y)
    → PathP (λ i → p i ≡ p i) l2 l2'
    → (Σ[ sq ∈ Square l2 l2 (sym l1) l1 ] f ≡ Klein→-fun x l1 l2 sq)
    → Σ[ sq ∈ Square l2' l2' (sym l1') l1' ] f ≡ Klein→-fun y l1' l2' sq
  charac'→ f x = J> λ l1 → J> λ l2 → J> λ r → r

  H²→Prop' : (f : KleinBottle → K₂)
    → ∃[ sq ∈ (Ω^ 2) (EM∙ ℤ/2 2) .fst ] f ≡ Klein→-fun ∣ north ∣ refl refl sq
  H²→Prop' f =
    TR.rec (isProp→isSet squash₁)
      (λ p → TR.rec squash₁
            (λ pl → TR.rec squash₁
              (λ pr → ∣ charac'→ f _ _ (sym p) (cong f line1) refl pl (cong f line2) refl pr
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



elimSet : ∀ {ℓ} {A : KleinBottle → Type ℓ}
  → ((x : _) → isSet (A x))
  → (a₀ : A point)
  → (l1 : PathP (λ i → A (line1 i)) a₀ a₀)
  → (l2 : PathP (λ i → A (line2 i)) a₀ a₀)
  → (x : _) → A x
elimSet set a₀ l1 l2 point = a₀
elimSet set a₀ l1 l2 (line1 i) = l1 i
elimSet set a₀ l1 l2 (line2 i) = l2 i
elimSet {A = A} set a₀ l1 l2 (square i j) = h i j
  where
  h : SquareP (λ i j → A (square i j)) l2 l2 (symP l1) l1
  h = toPathP (isOfHLevelPathP' 1 (set _) _ _ _ _)

elimProp : ∀ {ℓ} {A : KleinBottle → Type ℓ}
  → ((x : _) → isProp (A x))
  → (a₀ : A point)
  → (x : _) → A x
elimProp prop a₀ =
  elimSet (λ _ → isProp→isSet (prop _))
    a₀
    (isProp→PathP (λ _ → prop _) _ _)
    (isProp→PathP (λ _ → prop _) _ _)





open IsAbGroup
open AbGroupStr

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

ℤ/2-elim : ∀ {ℓ} {A : fst ℤ/2 → Type ℓ} → A 0 → A 1 → (x : _) → A x
ℤ/2-elim {A = A} a₀ a₁ (zero , p) = subst (λ p → A (zero , p)) (isProp≤ (0 .snd) p) a₀
ℤ/2-elim {A = A} a₀ a₁ (suc zero , p) = subst (λ p → A (1 , p)) (isProp≤ (1 .snd) p) a₁
ℤ/2-elim {A = A} a₀ a₁ (suc (suc x) , p) = ⊥.rec (snotz (cong (λ x → predℕ (predℕ x)) (+-comm _ _ ∙ snd p)))

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
  → fun1 (Klein→-fun (0ₖ 2) refl refl p)
  ≡ λ i → p (~ i) ∙ refl
fun1-nice p =
     cong₂ _∙_ (cong (cong (λ x → (λ _ → ∣ north ∣) ∙ x)) br-refl)
               (cong₂ _∙_ l (transferCube' p))
  ∙∙ sym (lUnit _)
  ∙∙ (sym (lUnit _)
    ∙ cong (cong (λ x → x ∙ refl)) (sym (sym≡flipSquare p)))


fff : (p : Square {A = K₂} refl refl (sym refl) refl)
  → fun2 (fun1 (Klein→-fun (0ₖ 2) refl refl p))
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
G→H²K² g = ∣ Klein→-fun (0ₖ 2) refl refl (G→Ω²K² g) ∣₂

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

0ₕ≡ : Path (coHom 2 ℤ/2 KleinBottle) (0ₕ 2) (∣ (Klein→-fun ∣ north ∣ refl refl (λ _ _ → ∣ north ∣)) ∣₂)
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

{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.Torus where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Prelims

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Algebra.Group renaming (Int to IntGroup ; Bool to BoolGroup ; Unit to UnitGroup)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2) hiding (map)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁) hiding (map)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Truncation renaming (elim to trElim ; elim2 to trElim2 ; map to trMap ; rec to trRec)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.RingStructure.CupProduct

open GroupHom
open GroupIso
open Iso

-- The following section contains stengthened induction principles for cohomology groups of T². They are particularly useful for showing that
-- that some Isos are morphisms. They make things type-check faster, but should probably not be used for computations.

-- We first need some functions
elimFunT² : (n : ℕ) (p q : typ (Ω (coHomK-ptd (suc n))))
                  → Square q q p p
                  → S¹ × S¹ → coHomK (suc n)
elimFunT² n p q P (base , base) = ∣ ptSn (suc n) ∣
elimFunT² n p q P (base , loop i) = q i
elimFunT² n p q P (loop i , base) = p i
elimFunT² n p q P (loop i , loop j) = P i j

elimFunT²' : (n : ℕ) → Square (refl {ℓ-zero} {coHomK (suc n)} {∣ ptSn (suc n) ∣}) refl refl refl
           → S¹ × S¹ → coHomK (suc n)
elimFunT²' n P (x , base) = ∣ ptSn (suc n) ∣
elimFunT²' n P (base , loop j) = ∣ ptSn (suc n) ∣
elimFunT²' n P (loop i , loop j) = P i j

elimFunT²'≡elimFunT² : (n : ℕ) → (P : _) → elimFunT²' n P ≡ elimFunT² n refl refl P
elimFunT²'≡elimFunT² n P i (base , base) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (base , loop k) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (loop j , base) = ∣ ptSn (suc n) ∣
elimFunT²'≡elimFunT² n P i (loop j , loop k) = P j k

{-
The first induction principle says that when proving a proposition for some x : Hⁿ(T²), n ≥ 1, it suffices to show that it holds for
(elimFunT² p q P) for any paths p q : ΩKₙ, and square P : Square q q p p. This is useful because elimFunT² p q P (base , base) recudes to 0
-}

coHomPointedElimT² : ∀ {ℓ} (n : ℕ) {B : coHom (suc n) (S¹ × S¹) → Type ℓ}
                 → ((x : coHom (suc n) (S¹ × S¹)) → isProp (B x))
                 → ((p q : _) (P : _) → B ∣ elimFunT² n p q P ∣₂)
                 → (x : coHom (suc n) (S¹ × S¹)) → B x
coHomPointedElimT² n {B = B} isprop indp =
  coHomPointedElim _ (base , base) isprop
    λ f fId → subst B (cong ∣_∣₂ (funExt (λ { (base , base) → sym fId
                                           ; (base , loop i) j → helper f fId i1 i (~ j)
                                           ; (loop i , base) j → helper f fId i i1 (~ j)
                                           ; (loop i , loop j) k → helper f fId i j (~ k)})))
                       (indp (λ i → helper f fId i i1 i1)
                             (λ i → helper f fId i1 i i1)
                              λ i j → helper f fId i j i1)
    where
    helper : (f : S¹ × S¹ → coHomK (suc n)) → f (base , base) ≡ ∣ ptSn (suc n) ∣
           → I → I → I → coHomK (suc n)
    helper f fId i j k =
      hfill (λ k → λ {(i = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (i = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (base , loop i))) fId k j
                     ; (j = i0) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i
                     ; (j = i1) → doubleCompPath-filler (sym fId) (cong f (λ i → (loop i , base))) fId k i})
            (inS (f ((loop i) , (loop j))))
            k

private
  lem : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                   → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                   → (p : _) → (refl ≡ p)
                   → (q : _) → (refl ≡ q)
                   → (P : _)
                   → B ∣ elimFunT² (suc n) p q P ∣₂
  lem n {B = B} elimP p =
    J (λ p _ → (q : _) → (refl ≡ q)
             → (P : _)
             → B ∣ elimFunT² (suc n) p q P ∣₂)
      λ q →
        J (λ q _ → (P : _) → B ∣ elimFunT² (suc n) refl q P ∣₂)
           elimP

{- When working with Hⁿ(T²) , n ≥ 2, we are, in the case described above, allowed to assume that any f : Hⁿ(T²) is
   elimFunT² n refl refl P -}
coHomPointedElimT²' : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                 → ((x : coHom (2 + n) (S¹ × S¹)) → isProp (B x))
                 → ((P : _) → B ∣ elimFunT² (suc n) refl refl P ∣₂)
                 → (x : coHom (2 + n) (S¹ × S¹)) → B x
coHomPointedElimT²' n {B = B} prop ind =
  coHomPointedElimT² (suc n) prop
    λ p q P → trRec (isProp→isOfHLevelSuc n (prop _))
      (λ p-refl → trRec (isProp→isOfHLevelSuc n (prop _))
                         (λ q-refl → lem n {B = B} ind p (sym p-refl) q (sym q-refl) P)
      (isConnectedPath _ (isConnectedPathKn (suc n) _ _) q refl .fst))
      (isConnectedPath _ (isConnectedPathKn (suc n) _ _) p refl .fst)

{- A slight variation of the above which gives definitional equalities for all points (x , base) -}
private
  coHomPointedElimT²'' : ∀ {ℓ} (n : ℕ) {B : coHom (2 + n) (S¹ × S¹) → Type ℓ}
                   → ((x : coHom (2 + n) (S¹ × S¹)) → isProp (B x))
                   → ((P : _) → B ∣ elimFunT²' (suc n) P ∣₂)
                   → (x : coHom (2 + n) (S¹ × S¹)) → B x
  coHomPointedElimT²'' n {B = B} prop ind =
    coHomPointedElimT²' n prop λ P → subst (λ x → B ∣ x ∣₂)
                        (elimFunT²'≡elimFunT² (suc n) P) (ind P)

f≡mere : (f : coHom 2 (S¹ × S¹)) → ∃[ P ∈ Square (refl {ℓ-zero} {coHomK 2} {∣ ptSn 2 ∣}) refl refl refl ] (f ≡ ∣ elimFunT²' 1 P ∣₂)
f≡mere = coHomPointedElimT²'' 0 (λ _ → propTruncIsProp) λ P → ∣ P , refl ∣₁



refactor1 : (S¹ × S¹ → coHomK 2) → S¹ × S¹ → coHomK 2
refactor1 f (base , base) = 0ₖ _
refactor1 f (base , loop i) = 0ₖ _
refactor1 f (loop i , base) = (sym (rCancelₖ 2 (f (base , base)))
                      ∙∙ (cong (λ x → f (x , base) -ₖ f (base , base)) loop)
                      ∙∙ rCancelₖ 2 (f (base , base))) i
refactor1 f (loop i , loop j) =
  hcomp (λ k → λ { (i = i0) → rCancelₖ 2 (f (base , (loop j))) k
                 ; (i = i1) →  rCancelₖ 2 (f (base , (loop j))) k
                 ; (j = i0) → doubleCompPath-filler (sym (rCancelₖ 2 (f (base , base))))
                                                     (cong (λ x → f (x , base) -ₖ f (base , base)) loop)
                                                     (rCancelₖ 2 (f (base , base))) k i
                 ; (j = i1) → doubleCompPath-filler (sym (rCancelₖ 2 (f (base , base))))
                                                     (cong (λ x → f (x , base) -ₖ f (base , base)) loop)
                                                     (rCancelₖ 2 (f (base , base))) k i})
        (f (loop i , loop j) -ₖ f (base , loop j))

refactor2 : (S¹ × S¹ → coHomK 2) → S¹ × S¹ → coHomK 2
refactor2 f (base , base) = 0ₖ _
refactor2 f (base , loop i) = (sym (rCancelₖ 2 (f (base , base)))
                      ∙∙ (cong (λ x → f (base , x) -ₖ f (base , base)) loop)
                      ∙∙ rCancelₖ 2 (f (base , base))) i
refactor2 f (loop i , base) = 0ₖ _
refactor2 f (loop i , loop j) =
  hcomp (λ k → λ { (j = i0) → rCancelₖ 2 (f ((loop i) , base)) k
                 ; (j = i1) →  rCancelₖ 2 (f ((loop i) , base)) k
                 ; (i = i0) → doubleCompPath-filler (sym (rCancelₖ 2 (f (base , base))))
                                                     (cong (λ x → f (base , x) -ₖ f (base , base)) loop)
                                                     (rCancelₖ 2 (f (base , base))) k j
                 ; (i = i1) → doubleCompPath-filler (sym (rCancelₖ 2 (f (base , base))))
                                                     (cong (λ x → f (base , x) -ₖ f (base , base)) loop)
                                                     (rCancelₖ 2 (f (base , base))) k j})
        (f (loop i , loop j) -ₖ f (loop i , base))

refactorH2 : coHom 2 (S₊ 1 × S₊ 1) → coHom 2 (S₊ 1 × S₊ 1)
refactorH2 = Cubical.HITs.SetTruncation.map refactor1

refactorH2' : coHom 2 (S₊ 1 × S₊ 1) → coHom 2 (S₊ 1 × S₊ 1)
refactorH2' = Cubical.HITs.SetTruncation.map refactor2

elimFunEq : (f : _) → Σ[ P ∈ Square refl refl refl refl ] (refactorH2' (refactorH2 f) ≡ ∣ elimFunT²' 1 P ∣₂)
elimFunEq =
  sElim ((λ _ → isSetΣ (isOfHLevelTrunc 4 _ _ _ _)
                       λ _ → isOfHLevelPath 2 squash₂ _ _))
    λ f → P f , help2 f
  where
    module _ (f : _) where
      g = refactor2 (refactor1 f)

      lem₁ : cong (λ x → g (base , x)) loop ≡ refl
      lem₁ = (λ i → rUnit (refl ∙∙ refl ∙∙ refl) (~ i) ∙∙ refl ∙∙ rUnit (refl ∙∙ refl ∙∙ refl) (~ i))
          ∙∙ (λ i → rUnit refl (~ i) ∙∙ refl ∙∙ rUnit refl (~ i))
          ∙∙ sym (rUnit refl)

      P-filler : I → I → I → coHomK 2
      P-filler i j k =
        hfill (λ k → λ {(i = i0) → lem₁ k j
                       ; (i = i1) → lem₁ k j
                       ; (j = i0) → 0ₖ _
                       ; (j = i1) → 0ₖ _ })
              (inS (g ((loop i) , (loop j))))
              k

      P : Square refl refl refl refl
      P i j = P-filler i j i1

      help2 : refactorH2' (refactorH2 ∣ f ∣₂) ≡ ∣ elimFunT²' 1 P ∣₂
      help2 =
        cong ∣_∣₂ (funExt λ { (base , base) → refl
                           ; (base , loop i) k → lem₁ k i
                           ; (loop i , base) → refl
                           ; (loop i , loop j) k → P-filler i j k})


coHom2→Int : coHom 2 (S₊ 1 × S₊ 1) → Int
coHom2→Int f = ΩKn+1→Kn 0 (cong (ΩKn+1→Kn 1) (fst (elimFunEq f)))

test : S¹ × S¹ → coHomK 2
test (base , y) = 0ₖ _
test (loop i , base) = 0ₖ _
test (loop i , loop j) =
  hcomp (λ k → λ { (i = i0) → ∣ rCancel (merid base) k j ∣
                  ; (i = i1) → ∣ rCancel (merid base) k j ∣
                  ; (j = i0) → 0ₖ _
                  ; (j = i1) → 0ₖ _})
    ((Kn→ΩKn+1 _ (∣ loop i ∣) j))

-- t = coHom2→Int (∣ test ∣₂ +ₕ (0ₕ 2))

s : Int → Square {A = coHomK 2} {a₀₀ = 0ₖ _} refl refl refl refl
s x i j =
    hcomp (λ k → λ { (i = i0) → ∣ rCancel (merid base) k j ∣
                  ; (i = i1) → ∣ rCancel (merid base) k j ∣
                  ; (j = i0) → 0ₖ _
                  ; (j = i1) → 0ₖ _})
    ((Kn→ΩKn+1 1 (Kn→ΩKn+1 0 x i) j))

back : Int → coHom 2 (S¹ × S¹)
back x = ∣ elimFunT²' 1 (s x) ∣₂

l : Square {A = coHomK 2} {a₀₀ = 0ₖ _} refl refl refl refl → coHom 2 (S¹ × S¹)
l P = ∣ elimFunT²' 1 P ∣₂

isEquiv-s : isEquiv s
isEquiv-s = {!!}


isEquiv-l : isEquiv l
equiv-proof isEquiv-l f =
  pRec isPropIsContr (λ {(P , p) → helpi P (sym p)})
      (f≡mere f)
  where
  helpi : (P : Square refl refl refl refl) (p : l P ≡ f) → isContr (fiber l f)
  helpi P =
    J (λ f _ → isContr (fiber l f))
      ((P , refl) , uncurry λ Q p → Σ≡Prop (λ _ → squash₂ _ _) (help P Q (Iso.fun (PathIdTrunc₀Iso) p)))
    where
    help : (P Q : _) → ∥ (elimFunT²' 1 Q ≡ elimFunT²' 1 P) ∥ → P ≡ Q
    help P Q = pRec {!!} λ p k i j → {!p (~ k) (loop i , loop j)!}
      where
      hel : {!!}
      hel = {!!}

      main : elimFunT²' 1 Q ≡ elimFunT²' 1 P
          → cong (λ x → cong (λ y → elimFunT²' 1 Q (x , y)) loop) loop
          ≡ cong (λ x → cong (λ y → elimFunT²' 1 P (x , y)) loop) loop
      main p =
        trElim {!!} {!!}
        (Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedPathKn 1 _ _) ∣ funExt⁻ p (base , base) ∣ ∣ refl ∣))
        where
        help3 : cong (funExt⁻ p) (λ i → (loop i , base)) ≡ refl
        help3 = {!!}
        help4 : cong (funExt⁻ p) (λ i → (base , loop i)) ≡ refl
        help4 = {!!}
  
      help2 : cong (λ x → cong (λ y → elimFunT²' 1 Q (x , y)) loop) loop ≡ Q
      help2 = refl

      help3 : cong (λ x → cong (λ y → elimFunT²' 1 P (x , y)) loop) loop ≡ P
      help3 = refl
{-
  pRec isPropIsContr (λ {(P , p) → helpi P (sym p)})
      (f≡mere f)

  where
  helpi : (P : Square refl refl refl refl) (p : ∣ elimFunT²' 1 P ∣₂ ≡ f) → isContr (fiber back f)
  helpi P =
    J (λ f _ → isContr (fiber back f))
       (({!!} , {!!})
      , {!!})
-}
{-
back-forth : coHom2→Int ((0ₕ 2) +ₕ back 0) ≡ 0
back-forth = {!refl!}
-}


-- open import Cubical.Foundations.Path
-- open import Cubical.Foundations.Pointed.Homogeneous
-- -- compPathlEquiv
-- pathTo : ∀ {ℓ} (A : Pointed ℓ) → Type _
-- pathTo A = Σ[ X ∈ Pointed _ ] X ≡ A

-- isContrPathTo : ∀ {ℓ} {A : Pointed ℓ} → isContr (pathTo A)
-- fst (isContrPathTo {A = A}) = A , refl
-- fst (snd (isContrPathTo {A = A}) (B , x) i) = x (~ i)
-- snd (snd (isContrPathTo {A = A}) (B , x) i) j = x (~ i ∨ j)

-- mapp : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isHomogeneous (coHom n A , 0ₕ _)
-- mapp {A = A} n f = ua∙ (isoToEquiv p) (lUnitₕ n f)
--   where
--   p : Iso (coHom n A) (coHom n A) 
--   fun p = _+ₕ f
--   inv p = _+ₕ (-ₕ f)
--   rightInv p x = sym (assocₕ _ x (-ₕ f) f) ∙∙ cong (x +ₕ_) (lCancelₕ n f) ∙∙ rUnitₕ n x
--   leftInv p x = sym (assocₕ _ x f (-ₕ f)) ∙∙ cong (x +ₕ_) (rCancelₕ n f) ∙∙ rUnitₕ n x

-- open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁ ; rec to pRec ; rec2 to pRec2 ; elim to pElim) 
-- mapps : ∀ {ℓ} {A : Type ℓ} (n : ℕ) (x : ∥ coHom n A ∥₁) → pathTo (coHom n A , 0ₕ _)
-- mapps n = pRec (isContr→isProp isContrPathTo) λ f → (coHom n _ , f) , sym (mapp n f)

-- myst : ∀ {ℓ} (n : ℕ) {A : Type ℓ} → (x : ∥ coHom n A ∥₁) → (fst ∘ fst ∘ (mapps n)) x
-- myst n = snd ∘ fst ∘ mapps n

-- test' : ∀ {ℓ} (n : ℕ) {A : Type ℓ} → (x : coHom n A) → myst n ∣ x ∣₁ ≡ x
-- test' n x = {!!}

-- inver : ∀ {ℓ} (n : ℕ) {A : Type ℓ} → coHom n A → (coHom n A)
-- inver n = myst n ∘ ∣_∣₁

-- -- ua∙ (compPathlEquiv (p ⁻¹)) {!!}

-- module _ (f : S¹ × S¹ → coHomK 2) where

--       ≡∙ : (p : _) → (typ (Ω (Ω (coHomK-ptd 2))) , p) ≡ (typ (Ω (Ω (coHomK-ptd 2))) , refl)
--       ≡∙ p = ua∙ (compPathrEquiv (p ⁻¹)) (rCancel p)

--       t'' : ∥ typ ((Ω^ 2) (coHomK-ptd 2)) ∥₁
--       t'' = pRec propTruncIsProp (λ {(P , _) → ∣ P ∣₁}) (f≡mere ∣ f ∣₂)


--       t** : (x : ∃[ P ∈ Square refl refl refl refl ] (∣ f ∣₂ ≡ ∣ elimFunT²' 1 P ∣₂)) → pathTo (typ ((Ω^ 2) (coHomK-ptd 2)) , refl)
--       t** = pRec (isContr→isProp isContrPathTo)
--                 (λ {(P , p) → (typ ((Ω^ 2) (coHomK-ptd 2)) , P) , ≡∙ P})

--       t* : pathTo (typ ((Ω^ 2) (coHomK-ptd 2)) , refl)
--       t* = t** (f≡mere ∣ f ∣₂)

--       s : fst (fst t*)
--       s = transport (λ i → {!!}) {!!}

--       t'≡ : typ ((Ω^ 2) (coHomK-ptd 2))
--       t'≡ = transport (cong fst (t* .snd)) {!!} -- transport (cong fst (t* .snd)) (t* .fst .snd)

      

-- refactor : coHom 2 (S¹ × S¹) → typ ((Ω^ 2) (coHomK-ptd 2))
-- refactor = sRec (isOfHLevelTrunc 4 _ _ _ _) λ f → t'≡ f


-- -- lem₁ : (f : _) (P : Square refl refl refl refl) (p : ∣ f ∣₂ ≡ ∣ elimFunT²' 1 P ∣₂)
-- --   → f≡mere ∣ f ∣₂ ≡ ∣ P , p ∣₁ →  ∥ refactor ∣ f ∣₂ ≡ {!!} ∥₁
-- -- lem₁ f P p _ = ∣ (λ i → transport (sym (cong fst (t* f .snd))) (t* f .fst .snd))
-- --                ∙ {!!}
-- --                ∙ {!!} ∣₁ -- refl -- {!!} ∙∙ {!compPathlEquiv!} ∙∙ {!!}
-- --   where
-- --   t' : t'' f ≡ ∣ P ∣₁
-- --   t' = cong (pRec propTruncIsProp (λ {(P , _) → ∣ P ∣₁})) (squash (f≡mere ∣ f ∣₂) ∣ P , p ∣₁)

-- --   t*≡ : t* f ≡ (((typ ((Ω^ 2) (coHomK-ptd 2))) , P) , ≡∙ f P)
-- --   t*≡ = cong (pRec (isContr→isProp isContrPathTo)
-- --                 (λ p → ((typ ((Ω^ 2) (coHomK-ptd 2))) , p) , ≡∙ f p)) t' {- cong (pRec (isContr→isProp isContrPathTo)
-- --                 (λ p → ((typ ((Ω^ 2) (coHomK-ptd 2))) , p) , ≡∙ f p)) t' -}

-- --   t'≡-final : t'≡ f ≡ ?
-- --   t'≡-final =
-- --     (λ i → transport (sym (cong fst (t*≡ i .snd))) (t*≡ i .fst .snd)) ∙∙ ? ∙∙ ?

-- -- toInt : coHom 2 (S¹ × S¹) → Int
-- -- toInt = (ΩKn+1→Kn 0 ∘ cong (ΩKn+1→Kn 1)) ∘ refactor

-- -- isoCool : Iso (coHom 2 (S¹ × S¹)) (typ ((Ω^ 2) (coHomK-ptd 2)))
-- -- fun isoCool = refactor
-- -- inv isoCool P = ∣ elimFunT²' 1 P ∣₂
-- -- rightInv isoCool P = {!λ i → transport (cong fst (t* (elimFunT²' 1 P) .snd)) (t* (elimFunT²' 1 P) .fst .snd)!} ∙∙ {!!} ∙∙ {!!}
-- -- leftInv isoCool = coHomPointedElimT²'' {!!} {!!} λ P → {!!}


-- -- -- transport (λ i → (f : coHom 2 (S¹ × S¹))
-- --    --                        → (fst ∘ fst ∘ (mapps 2)) (pRec propTruncIsProp (λ {(P , p) → cong ∣_∣₁ p i}) (f≡mere f))) {!!}
-- -- -- transport (λ i → (f : coHom 2 (S¹ × S¹)) → (fst ∘ fst ∘ (mapps 2)) (squash ∣ {!!} ∣₁ ∣ f ∣₁ i ))
-- --   -- {!!}


-- -- -- --------- H⁰(T²) ------------
-- -- -- H⁰-T²≅ℤ : GroupIso (coHomGr 0 (S₊ 1 × S₊ 1)) IntGroup
-- -- -- H⁰-T²≅ℤ =
-- -- --   H⁰-connected (base , base)
-- -- --     λ (a , b) → pRec propTruncIsProp
-- -- --                      (λ id1 → pRec propTruncIsProp
-- -- --                                    (λ id2 → ∣ ΣPathP (id1 , id2) ∣₁)
-- -- --                                    (Sn-connected 0 b) )
-- -- --                      (Sn-connected 0 a)

-- -- -- --------- H¹(T²) -------------------------------

-- -- -- H¹-T²≅ℤ×ℤ : GroupIso (coHomGr 1 ((S₊ 1) × (S₊ 1))) (DirProd IntGroup IntGroup)
-- -- -- H¹-T²≅ℤ×ℤ = theIso □ GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ 0) (H⁰-Sⁿ≅ℤ 0)
-- -- --   where
-- -- --   typIso : Iso _ _
-- -- --   typIso = setTruncIso (curryIso ⋄ codomainIso S1→K₁≡S1×Int ⋄ toProdIso)
-- -- --                       ⋄ setTruncOfProdIso

-- -- --   theIso : GroupIso _ _
-- -- --   isom theIso = typIso
-- -- --   isHom theIso =
-- -- --       coHomPointedElimT² _ (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
-- -- --       λ pf qf Pf →
-- -- --         coHomPointedElimT² _ (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
-- -- --           λ pg qg Pg i → ∣ funExt (helperFst pf qf pg qg Pg Pf) i  ∣₂
-- -- --                         , ∣ funExt (helperSnd pf qf pg qg Pg Pf) i ∣₂
-- -- --      where
-- -- --        module _ (pf qf pg qg : 0ₖ 1 ≡ 0ₖ 1) (Pg : Square qg qg pg pg) (Pf : Square qf qf pf pf) where
-- -- --          helperFst : (x : S¹)
-- -- --                 → fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst
-- -- --                  ≡ fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst
-- -- --                 +ₖ fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst
-- -- --          helperFst base = refl
-- -- --          helperFst (loop i) j = loopLem j i
-- -- --            where
-- -- --            loopLem : cong (λ x → fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
-- -- --                    ≡ cong (λ x → fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .fst
-- -- --                                +ₖ fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .fst) loop
-- -- --            loopLem = (λ i j → S¹map-id (pf j +ₖ pg j) i)
-- -- --                    ∙ (λ i j → S¹map-id (pf j) (~ i) +ₖ S¹map-id (pg j) (~ i))

-- -- --          helperSnd : (x : S¹)
-- -- --                 → fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y) +ₖ elimFunT² 0 pg qg  Pg (x , y)) .snd
-- -- --                 ≡ fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pf qf Pf (x , y)) .snd +ℤ fun S1→K₁≡S1×Int (λ y → elimFunT² 0 pg qg  Pg (x , y)) .snd
-- -- --          helperSnd =
-- -- --            toPropElim (λ _ → isSetInt _ _)
-- -- --                       ((λ i → winding (basechange2⁻ base λ j → S¹map (∙≡+₁ qf qg (~ i) j)))
-- -- --                     ∙∙ cong (winding ∘ basechange2⁻ base) (congFunct S¹map qf qg)
-- -- --                     ∙∙ (cong winding (basechange2⁻-morph base (cong S¹map qf) (cong S¹map qg))
-- -- --                       ∙ winding-hom (basechange2⁻ base (cong S¹map qf)) (basechange2⁻ base (cong S¹map qg))))

-- -- -- ----------------------- H²(T²) ------------------------------

-- -- -- H²-T²≅ℤ : GroupIso (coHomGr 2 (S₊ 1 × S₊ 1)) IntGroup
-- -- -- H²-T²≅ℤ = compGroupIso helper2 (Hⁿ-Sⁿ≅ℤ 0)
-- -- --   where
-- -- --   helper : Iso (∥ ((a : S¹) → coHomK 2) ∥₂ × ∥ ((a : S¹) → coHomK 1) ∥₂) (coHom 1 S¹)
-- -- --   inv helper s = 0ₕ _ , s
-- -- --   fun helper = snd
-- -- --   leftInv helper _ =
-- -- --     ΣPathP (isOfHLevelSuc 0 (isOfHLevelRetractFromIso 0 (isom (Hⁿ-S¹≅0 0)) (isContrUnit)) _ _
-- -- --           , refl)
-- -- --   rightInv helper _ = refl
-- -- --   theIso : Iso (coHom 2 (S¹ × S¹)) (coHom 1 S¹)
-- -- --   theIso = setTruncIso (curryIso ⋄ codomainIso S1→K2≡K2×K1 ⋄ toProdIso)
-- -- --          ⋄ setTruncOfProdIso
-- -- --          ⋄ helper

-- -- --   helper2 : GroupIso (coHomGr 2 (S¹ × S¹)) (coHomGr 1 S¹)
-- -- --   helper2 = groupiso theIso (
-- -- --     coHomPointedElimT²'' 0 (λ _ → isPropΠ λ _ → setTruncIsSet _ _)
-- -- --       λ P → coHomPointedElimT²'' 0 (λ _ → setTruncIsSet _ _)
-- -- --       λ Q → ((λ i → ∣ (λ a → ΩKn+1→Kn 1 (sym (rCancel≡refl 0 i)
-- -- --                                         ∙∙ cong (λ x → (elimFunT²' 1 P (a , x) +ₖ elimFunT²' 1 Q (a , x)) -ₖ ∣ north ∣) loop
-- -- --                                         ∙∙ rCancel≡refl 0 i)) ∣₂))
-- -- --           ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 P (a , x) +ₖ elimFunT²' 1 Q (a , x)) i) loop) (~ i))) ∣₂)
-- -- --           ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn 1 (∙≡+₂ 0 (cong (λ x → elimFunT²' 1 P (a , x)) loop) (cong (λ x → elimFunT²' 1 Q (a , x)) loop) (~ i))) ∣₂)
-- -- --           ∙∙ (λ i → ∣ (λ a → ΩKn+1→Kn-hom 1 (cong (λ x → elimFunT²' 1 P (a , x)) loop) (cong (λ x → elimFunT²' 1 Q (a , x)) loop) i) ∣₂)
-- -- --           ∙∙ (λ i → ∣ ((λ a → ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 P (a , x)) (~ i)) loop) i)
-- -- --                                            +ₖ ΩKn+1→Kn 1 (rUnit (cong (λ x → rUnitₖ 2 (elimFunT²' 1 Q (a , x)) (~ i)) loop) i))) ∣₂)
-- -- --            ∙ (λ i → ∣ ((λ a → ΩKn+1→Kn 1 (sym (rCancel≡refl 0 (~ i))
-- -- --                                                          ∙∙ cong (λ x → elimFunT²' 1 P (a , x) +ₖ ∣ north ∣) loop
-- -- --                                                          ∙∙ rCancel≡refl 0 (~ i))
-- -- --                                            +ₖ ΩKn+1→Kn 1 (sym (rCancel≡refl 0 (~ i))
-- -- --                                                          ∙∙ cong (λ x → elimFunT²' 1 Q (a , x) +ₖ ∣ north ∣) loop
-- -- --                                                          ∙∙ rCancel≡refl 0 (~ i)))) ∣₂))

-- -- -- private
-- -- --   to₂ : coHom 2 (S₊ 1 × S₊ 1) → Int
-- -- --   to₂ = fun (isom H²-T²≅ℤ)

-- -- --   from₂ : Int → coHom 2 (S₊ 1 × S₊ 1)
-- -- --   from₂ = inv (isom H²-T²≅ℤ)

-- -- --   to₁ : coHom 1 (S₊ 1 × S₊ 1) → Int × Int
-- -- --   to₁ = fun (isom H¹-T²≅ℤ×ℤ)

-- -- --   from₁ : Int × Int → coHom 1 (S₊ 1 × S₊ 1)
-- -- --   from₁ = inv (isom H¹-T²≅ℤ×ℤ)

-- -- --   to₀ : coHom 0 (S₊ 1 × S₊ 1) → Int
-- -- --   to₀ = fun (isom H⁰-T²≅ℤ)

-- -- --   from₀ : Int → coHom 0 (S₊ 1 × S₊ 1)
-- -- --   from₀ = inv (isom H⁰-T²≅ℤ)

-- -- -- {-
-- -- -- -- Compute fast:
-- -- -- test : to₁ (from₁ (0 , 1) +ₕ from₁ (1 , 0)) ≡ (1 , 1)
-- -- -- test = refl

-- -- -- test2 : to₁ (from₁ (5 , 1) +ₕ from₁ (-2 , 3)) ≡ (3 , 4)
-- -- -- test2 = refl

-- -- -- -- Compute pretty fast

-- -- -- test3 : to₂ (from₂ 1) ≡ 1
-- -- -- test3 = refl

-- -- -- test4 : to₂ (from₂ 2) ≡ 2
-- -- -- test4 = refl

-- -- -- test5 : to₂ (from₂ 3) ≡ 3
-- -- -- test5 = refl

-- -- -- -- Compute, but slower

-- -- -- test6 : to₂ (from₂ 0 +ₕ from₂ 0) ≡ 0
-- -- -- test6 = refl

-- -- -- test6 : to₂ (from₂ 0 +ₕ from₂ 1) ≡ 1
-- -- -- test6 = refl

-- -- -- -- Does not compute
-- -- -- test7 : to₂ (from₂ 1 +ₕ from₂ 0) ≡ 1
-- -- -- test7 = refl
-- -- -- -}

-- -- -- ff : (S₊ 1 × S₊ 1 → coHomK 1)
-- -- -- ff (x , y) = ∣ x ∣

-- -- -- ff2 : (S₊ 1 × S₊ 1 → coHomK 1)
-- -- -- ff2 (x , y) = ∣ y ∣

-- -- -- f : coHom 1 (S₊ 1 × S₊ 1)
-- -- -- f = ∣ ff ∣₂

-- -- -- f2 : coHom 1 (S₊ 1 × S₊ 1)
-- -- -- f2 = ∣ ff2 ∣₂

-- -- -- elem1 : coHom 2 (S₊ 1 × S₊ 1)
-- -- -- elem1 = ((f ⌣ 0ₕ 1) ⌣ ∣ (λ x → 1) ∣₂) +ₕ 0ₕ _

-- -- -- w = to₂ (f ⌣ f2)

-- -- -- w≡1 : w ≡ 1
-- -- -- w≡1 = {!refl!}


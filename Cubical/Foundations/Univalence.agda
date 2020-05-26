{-

Proof of the standard formulation of the univalence theorem and
various consequences of univalence

- Re-exports Glue types from Cubical.Core.Glue
- The ua constant and its computation rule (up to a path)
- Proof of univalence using that unglue is an equivalence ([EquivContr])
- Equivalence induction ([EquivJ], [elimEquiv])
- Univalence theorem ([univalence])
- The computation rule for ua ([uaβ])
- Isomorphism induction ([elimIso])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Core.Glue public
  using ( Glue ; glue ; unglue ; lineToEquiv )

private
  variable
    ℓ ℓ' : Level

-- The ua constant
ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })

uaIdEquiv : {A : Type ℓ} → ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)

-- the unglue and glue primitives specialized to the case of ua

ua-unglue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i)
            → B {- [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → x }) ] -}
ua-unglue e i x = unglue (i ∨ ~ i) x

ua-glue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
          → ua e i {- [ _ ↦ (λ { (i = i0) → x 1=1 ; (i = i1) → outS y }) ] -}
ua-glue e i x y = glue {φ = i ∨ ~ i} (λ { (i = i0) → x 1=1 ; (i = i1) → outS y }) (outS y)

-- sometimes more useful are versions of these functions with the (i : I) factored in

ua-ungluePath : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
                → PathP (λ i → ua e i) x y
                → e .fst x ≡ y
ua-ungluePath e p i = ua-unglue e i (p i)

ua-gluePath : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
              → e .fst x ≡ y
              → PathP (λ i → ua e i) x y
ua-gluePath e {x} p i = ua-glue e i (λ { (i = i0) → x }) (inS (p i))

-- ua-ungluePath and ua-gluePath are definitional inverses
ua-ungluePath-Equiv : ∀ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
                      → (PathP (λ i → ua e i) x y) ≃ (e .fst x ≡ y)
ua-ungluePath-Equiv e = isoToEquiv (iso (ua-ungluePath e) (ua-gluePath e) (λ _ → refl) (λ _ → refl))

-- ua-unglue and ua-glue are also definitional inverses, in a way
-- strengthening the types of ua-unglue and ua-glue gives a nicer formulation of this, see below

ua-unglue-glue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : Partial (~ i) A) (y : B [ _ ↦ _ ])
                 → ua-unglue e i (ua-glue e i x y) ≡ outS y
ua-unglue-glue _ _ _ _ = refl

ua-glue-unglue : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i)
                 → ua-glue e i (λ { (i = i0) → x }) (inS (ua-unglue e i x)) ≡ x
ua-glue-unglue _ _ _ = refl

-- mainly for documentation purposes, ua-unglue and ua-glue wrapped in cubical subtypes

ua-unglueS : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : A) (y : B)
             → ua e i [ _ ↦ (λ { (i = i0) → x        ; (i = i1) → y }) ]
             → B      [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ]
ua-unglueS e i x y s = inS (ua-unglue e i (outS s))

ua-glueS : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : A) (y : B)
           → B      [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ]
           → ua e i [ _ ↦ (λ { (i = i0) → x        ; (i = i1) → y }) ]
ua-glueS e i x y s = inS (ua-glue e i (λ { (i = i0) → x }) (inS (outS s)))

ua-unglueS-glueS : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : A) (y : B)
                     (s : B [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ])
                   → outS (ua-unglueS e i x y (ua-glueS e i x y s)) ≡ outS s
ua-unglueS-glueS _ _ _ _ _ = refl

ua-glueS-unglueS : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : A) (y : B)
                     (s : ua e i [ _ ↦ (λ { (i = i0) → x ; (i = i1) → y }) ])
                   → outS (ua-glueS e i x y (ua-unglueS e i x y s)) ≡ outS s
ua-glueS-unglueS _ _ _ _ _ = refl


-- a version of ua-glue with a single endpoint, identical to `ua-gluePath e {x} refl i`
ua-gluePt : ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : A)
            → ua e i {- [ _ ↦ (λ { (i = i0) → x ; (i = i1) → e .fst x }) ] -}
ua-gluePt e i x = ua-glue e i (λ { (i = i0) → x }) (inS (e .fst x))


-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ (A : Type ℓ) (φ : I)
                (f : PartialP φ (λ o → Σ[ T ∈ Type ℓ ] T ≃ A)) →
                isEquiv {A = Glue A f} (unglue φ)
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .snd) b .snd (~ i) }
      ctr : fiber (unglue φ) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .snd) b .fst }) (hcomp u b)
            , λ j → hfill u (inS b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue φ) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .snd (~ j)
                      ; (i = i0) → hfill u (inS b) j
                      ; (i = i1) → v .snd (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .snd) b v i .fst }) (hcomp u' b)
            , λ j → hfill u' (inS b) (~ j)))

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ (A : Type ℓ) (φ : I)
              (f : PartialP φ (λ o → Σ[ T ∈ Type ℓ ] T ≃ A)) →
              (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue φ , unglueIsEquiv A φ f )


-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can be found in
-- Cubical/Basics/Univalence.
--
EquivContr : ∀ (A : Type ℓ) → isContr (Σ[ T ∈ Type ℓ ] T ≃ A)
EquivContr {ℓ = ℓ} A =
  ( (A , idEquiv A)
  , idEquiv≡ )
 where
  idEquiv≡ : (y : Σ (Type ℓ) (λ T → T ≃ A)) → (A , idEquiv A) ≡ y
  idEquiv≡ w = \ { i .fst                   → Glue A (f i)
                 ; i .snd .fst              → unglueEquiv _ _ (f i) .fst
                 ; i .snd .snd .equiv-proof → unglueEquiv _ _ (f i) .snd .equiv-proof
                 }
    where
      f : ∀ i → PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Type ℓ ] T ≃ A)
      f i = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }

contrSinglEquiv : {A B : Type ℓ} (e : A ≃ B) → (B , idEquiv B) ≡ (A , e)
contrSinglEquiv {A = A} {B = B} e =
  isContr→isProp (EquivContr B) (B , idEquiv B) (A , e)

-- Equivalence induction
EquivJ : {A B : Type ℓ} (P : (A : Type ℓ) → (e : A ≃ B) → Type ℓ')
       → (r : P B (idEquiv B)) → (e : A ≃ B) → P A e
EquivJ P r e = subst (λ x → P (x .fst) (x .snd)) (contrSinglEquiv e) r

-- Assuming that we have an inverse to ua we can easily prove univalence
module Univalence (au : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B)
                  (aurefl : ∀ {ℓ} {A B : Type ℓ} → au refl ≡ idEquiv A) where

  ua-au : {A B : Type ℓ} (p : A ≡ B) → ua (au p) ≡ p
  ua-au {B = B} = J (λ _ p → ua (au p) ≡ p)
                    (cong ua (aurefl {B = B}) ∙ uaIdEquiv)

  au-ua : {A B : Type ℓ} (e : A ≃ B) → au (ua e) ≡ e
  au-ua {B = B} = EquivJ (λ _ f → au (ua f) ≡ f)
                         (subst (λ r → au r ≡ idEquiv _) (sym uaIdEquiv) (aurefl {B = B}))

  thm : ∀ {ℓ} {A B : Type ℓ} → isEquiv au
  thm {A = A} {B = B} = isoToIsEquiv {B = A ≃ B} (iso au ua au-ua ua-au)

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv p = lineToEquiv (λ i → p i)

pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq _ _ (λ i x → transp (λ _ → A) i x)

pathToEquiv-ua : {A B : Type ℓ} (e : A ≃ B) → pathToEquiv (ua e) ≡ e
pathToEquiv-ua = Univalence.au-ua pathToEquiv pathToEquivRefl

ua-pathToEquiv : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-pathToEquiv = Univalence.ua-au pathToEquiv pathToEquivRefl

-- Univalence
univalence : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = ( pathToEquiv , Univalence.thm pathToEquiv pathToEquivRefl  )

-- The original map from UniMath/Foundations
eqweqmap : {A B : Type ℓ} → A ≡ B → A ≃ B
eqweqmap {A = A} e = J (λ X _ → A ≃ X) (idEquiv A) e

eqweqmapid : {A : Type ℓ} → eqweqmap refl ≡ idEquiv A
eqweqmapid {A = A} = JRefl (λ X _ → A ≃ X) (idEquiv A)

univalenceStatement : {A B : Type ℓ} → isEquiv (eqweqmap {ℓ} {A} {B})
univalenceStatement = Univalence.thm eqweqmap eqweqmapid

univalenceUAH : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceUAH = ( _ , univalenceStatement )

univalencePath : {A B : Type ℓ} → (A ≡ B) ≡ Lift (A ≃ B)
univalencePath = ua (compEquiv univalence LiftEquiv)

-- The computation rule for ua. Because of "ghcomp" it is now very
-- simple compared to cubicaltt:
-- https://github.com/mortberg/cubicaltt/blob/master/examples/univalence.ctt#L202
uaβ : {A B : Type ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
uaβ e x = transportRefl (equivFun e x)

uaη : ∀ {A B : Type ℓ} → (P : A ≡ B) → ua (pathToEquiv P) ≡ P
uaη = J (λ _ q → ua (pathToEquiv q) ≡ q) (cong ua pathToEquivRefl ∙ uaIdEquiv)

-- Useful lemma for unfolding a transported function over ua
-- If we would have regularity this would be refl
transportUAop₁ : ∀ {A B : Type ℓ} → (e : A ≃ B) (f : A → A) (x : B)
               → transport (λ i → ua e i → ua e i) f x ≡ equivFun e (f (invEq e x))
transportUAop₁ e f x i = transportRefl (equivFun e (f (invEq e (transportRefl x i)))) i

-- Binary version
transportUAop₂ : ∀ {ℓ} {A B : Type ℓ} → (e : A ≃ B) (f : A → A → A) (x y : B)
               → transport (λ i → ua e i → ua e i → ua e i) f x y ≡
                 equivFun e (f (invEq e x) (invEq e y))
transportUAop₂ e f x y i =
    transportRefl (equivFun e (f (invEq e (transportRefl x i))
                                 (invEq e (transportRefl y i)))) i

-- Alternative version of EquivJ that only requires a predicate on functions
elimEquivFun : {A B : Type ℓ} (P : (A : Type ℓ) → (A → B) → Type ℓ')
             → (r : P B (idfun B)) → (e : A ≃ B) → P A (e .fst)
elimEquivFun P r e = subst (λ x → P (x .fst) (x .snd .fst)) (contrSinglEquiv e) r

-- Isomorphism induction
elimIso : {B : Type ℓ} → (Q : {A : Type ℓ} → (A → B) → (B → A) → Type ℓ') →
          (h : Q (idfun B) (idfun B)) → {A : Type ℓ} →
          (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
elimIso {ℓ} {ℓ'} {B} Q h {A} f g sfg rfg = rem1 f g sfg rfg
  where
  P : (A : Type ℓ) → (f : A → B) → Type (ℓ-max ℓ' ℓ)
  P A f = (g : B → A) → section f g → retract f g → Q f g

  rem : P B (idfun B)
  rem g sfg rfg = subst (Q (idfun B)) (λ i b → (sfg b) (~ i)) h

  rem1 : {A : Type ℓ} → (f : A → B) → P A f
  rem1 f g sfg rfg = elimEquivFun P rem (f , isoToIsEquiv (iso f g sfg rfg)) g sfg rfg


uaInvEquiv : ∀ {A B : Type ℓ} → (e : A ≃ B) → ua (invEquiv e) ≡ sym (ua e)
uaInvEquiv {B = B} = EquivJ (λ _ e → ua (invEquiv e) ≡ sym (ua e))
                            (cong ua (invEquivIdEquiv B))

uaCompEquiv : ∀ {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) → ua (compEquiv e f) ≡ ua e ∙ ua f
uaCompEquiv {B = B} {C} = EquivJ (λ _ e → (f : B ≃ C) → ua (compEquiv e f) ≡ ua e ∙ ua f)
                                 (λ f → cong ua (compEquivIdEquiv f)
                                        ∙ sym (cong (λ x → x ∙ ua f) uaIdEquiv
                                        ∙ sym (lUnit (ua f))))

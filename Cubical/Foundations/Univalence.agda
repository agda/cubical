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
{-# OPTIONS --safe #-}
module Cubical.Foundations.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Glue public
  using (Glue ; glue ; unglue)
  renaming (pathToEquiv to lineToEquiv)

open import Cubical.Reflection.StrictEquiv

private variable
  ℓ ℓ' : Level
  A B C : Type ℓ

-- The ua constant
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })

uaIdEquiv : ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)

-- Propositional extensionality
hPropExt : isProp A → isProp B → (A → B) → (B → A) → A ≡ B
hPropExt Aprop Bprop f g = ua (propBiimpl→Equiv Aprop Bprop f g)

-- the unglue and glue primitives specialized to the case of ua

ua-unglue : ∀ (e : A ≃ B) (i : I) (x : ua e i)
            → B {- [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → x }) ] -}
ua-unglue e i x = unglue (i ∨ ~ i) x

ua-glue : ∀ (e : A ≃ B) (i : I) (x : Partial (~ i) A)
            (y : B [ _ ↦ (λ { (i = i0) → e .fst (x 1=1) }) ])
          → ua e i {- [ _ ↦ (λ { (i = i0) → x 1=1 ; (i = i1) → outS y }) ] -}
ua-glue e i x y = glue {φ = i ∨ ~ i} (λ { (i = i0) → x 1=1 ; (i = i1) → outS y }) (outS y)

module _ {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B} where
  -- sometimes more useful are versions of these functions with the (i : I) factored in

  ua-ungluePath : PathP (λ i → ua e i) x y → e .fst x ≡ y
  ua-ungluePath p i = ua-unglue e i (p i)

  ua-gluePath : e .fst x ≡ y → PathP (λ i → ua e i) x y
  ua-gluePath p i = ua-glue e i (λ { (i = i0) → x }) (inS (p i))

  -- ua-ungluePath and ua-gluePath are definitional inverses
  ua-ungluePath-Equiv : (PathP (λ i → ua e i) x y) ≃ (e .fst x ≡ y)
  unquoteDef ua-ungluePath-Equiv =
    defStrictEquiv ua-ungluePath-Equiv ua-ungluePath ua-gluePath

ua-ungluePathExt : (e : A ≃ B) → PathP (λ i → ua e i → B) (fst e) (idfun B)
ua-ungluePathExt e i = ua-unglue e i

ua-gluePathExt : (e : A ≃ B) → PathP (λ i → A → ua e i) (idfun _) (fst e)
ua-gluePathExt e i x =
  ua-glue e i (λ { (i = i0) → x }) (inS (fst e x))

-- ua-unglue and ua-glue are also definitional inverses, in a way
-- strengthening the types of ua-unglue and ua-glue gives a nicer formulation of this, see below

ua-unglue-glue : ∀ (e : A ≃ B) (i : I) (x : Partial (~ i) A) (y : B [ _ ↦ _ ])
                 → ua-unglue e i (ua-glue e i x y) ≡ outS y
ua-unglue-glue _ _ _ _ = refl

ua-glue-unglue : ∀ (e : A ≃ B) (i : I) (x : ua e i)
                 → ua-glue e i (λ { (i = i0) → x }) (inS (ua-unglue e i x)) ≡ x
ua-glue-unglue _ _ _ = refl

-- mainly for documentation purposes, ua-unglue and ua-glue wrapped in cubical subtypes

ua-unglueS : ∀ (e : A ≃ B) (i : I) (x : A) (y : B)
             → ua e i [ _ ↦ (λ { (i = i0) → x        ; (i = i1) → y }) ]
             → B      [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ]
ua-unglueS e i x y s = inS (ua-unglue e i (outS s))

ua-glueS : ∀ (e : A ≃ B) (i : I) (x : A) (y : B)
           → B      [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ]
           → ua e i [ _ ↦ (λ { (i = i0) → x        ; (i = i1) → y }) ]
ua-glueS e i x y s = inS (ua-glue e i (λ { (i = i0) → x }) (inS (outS s)))

ua-unglueS-glueS : ∀ (e : A ≃ B) (i : I) (x : A) (y : B)
                     (s : B [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → y }) ])
                   → outS (ua-unglueS e i x y (ua-glueS e i x y s)) ≡ outS s
ua-unglueS-glueS _ _ _ _ _ = refl

ua-glueS-unglueS : ∀ (e : A ≃ B) (i : I) (x : A) (y : B)
                     (s : ua e i [ _ ↦ (λ { (i = i0) → x ; (i = i1) → y }) ])
                   → outS (ua-glueS e i x y (ua-unglueS e i x y s)) ≡ outS s
ua-glueS-unglueS _ _ _ _ _ = refl


-- a version of ua-glue with a single endpoint, identical to `ua-gluePath e {x} refl i`
ua-gluePt : ∀ (e : A ≃ B) (i : I) (x : A)
            → ua e i {- [ _ ↦ (λ { (i = i0) → x ; (i = i1) → e .fst x }) ] -}
ua-gluePt e i x = ua-glue e i (λ { (i = i0) → x }) (inS (e .fst x))

ua-unglueSquare : ∀ (e : A ≃ B) (i j : I) → ua e i → B
ua-unglueSquare e i j x = hcomp (λ where
    k (i = i0) → commSqIsEq (e .snd) x j (~ k)
    k (i = i1) → b
    k (j = i0) → secEq e b (~ k ∨ i)
    k (j = i1) → b
  ) b where b = ua-unglue e i x

ua-unglueIso : ∀ (e : A ≃ B) i → Iso (ua e i) B
ua-unglueIso e i .Iso.fun = ua-unglue e i
ua-unglueIso e i .Iso.inv b = ua-glue e i (λ _ → invEq e b) (inS (secEq e b i))
ua-unglueIso e i .Iso.rightInv b j = secEq e b (i ∨ j)
ua-unglueIso e i .Iso.leftInv b j =
  ua-glue e i (λ { (i = i0) → retEq e b j }) (inS (ua-unglueSquare e i j b))

equivFunFiller : ∀ (e : A ≃ B) (x : A)
               → PathP (λ i → ua e i) x (equivFun e x)
equivFunFiller e x = ua-gluePath e refl

invEqFiller : ∀ (e : A ≃ B) (x : B)
            → PathP (λ i → ua e i) (invEq e x) x
invEqFiller e x = ua-gluePath e (secEq e x)

equivFiller : (e : A ≃ B) → PathP (λ i → ua e i ≃ B) e (idEquiv B)
equivFiller e = equivPathP (ua-ungluePathExt e)

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

ua-unglueEquiv : ∀ (e : A ≃ B) →
                    PathP (λ i → ua e i ≃ B)
                       e
                       (idEquiv _)
fst (ua-unglueEquiv e i) = ua-unglue e i
snd (ua-unglueEquiv e i) =
  isProp→PathP (λ i → isPropIsEquiv (ua-unglue e i))
   (snd e) (idIsEquiv _) i

-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can be found in
-- Cubical/Basics/Univalence.
--
EquivContr : ∀ (A : Type ℓ) → ∃![ T ∈ Type ℓ ] (T ≃ A)
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
contrSinglEquiv {A = A} {B = B} e = EquivContr B .snd (A , e)

-- Equivalence induction
EquivJ : (P : (A : Type ℓ) → (e : A ≃ B) → Type ℓ')
       → (r : P B (idEquiv B)) → (e : A ≃ B) → P A e
EquivJ P r e = subst (λ x → P (x .fst) (x .snd)) (contrSinglEquiv e) r

-- Transport along a path is an equivalence.
-- The proof is a special case of isEquivTransp where the line of types is
-- given by p, and the extend φ -- where the transport is constant -- is i0.
-- Warning: this is deprecated
isEquivTransport' : (p : A ≡ B) → isEquiv (transport p)
isEquivTransport' p = isEquivTransp T φ where
  T : I → Type _
  T i = p i

  φ : I
  φ = i0

-- Note that isEquivTransp does not compute well,
-- so we prefer this definition using the builtin lineToEquiv.
pathToEquiv : A ≡ B → A ≃ B
pathToEquiv p = lineToEquiv λ i → p i

isEquivTransport : (p : A ≡ B) → isEquiv (transport p)
isEquivTransport p = pathToEquiv p .snd

private module test where
  _ : (p : A ≡ B) (b : B) → invIsEq (isEquivTransport p) b ≡ transport (sym p) b
  _ = λ _ _ → refl

  -- isEquivTransport' introduces an extra reflexive transport
  _ : (p : A ≡ B) (b : B) → invIsEq (isEquivTransport' p) b ≡ transport refl (transport (sym p) b)
  _ = λ _ _ → refl

pathToEquivOver : {A B : Type ℓ} (p : A ≡ B)
                → PathP (λ i → p i ≃ B) (pathToEquiv p) (idEquiv B)
pathToEquivOver p = equivPathP λ i x → transp (λ j → p (i ∨ j)) i x

pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl = pathToEquivOver refl

-- The computation rule for ua. Because of "ghcomp" it is now very
-- simple compared to cubicaltt:
-- https://github.com/mortberg/cubicaltt/blob/master/examples/univalence.ctt#L202
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
uaβ e x = transportRefl (equivFun e x)

~uaβ : (e : A ≃ B) (x : B) → transport (sym (ua e)) x ≡ invEq e x
~uaβ e x = cong (invEq e) (transportRefl x)

uaη : ∀ (P : A ≡ B) → ua (pathToEquiv P) ≡ P
uaη {A = A} {B = B} P i j = Glue B {φ = φ} sides where
  -- Adapted from a proof by @dolio, cf. commit e42a6fa1
  φ = i ∨ j ∨ ~ j

  sides : Partial φ (Σ[ T ∈ Type _ ] T ≃ B)
  sides (i = i1) = P j , pathToEquivOver P j
  sides (j = i0) = A , pathToEquiv P
  sides (j = i1) = B , idEquiv B

pathToEquiv-ua : (e : A ≃ B) → pathToEquiv (ua e) ≡ e
pathToEquiv-ua e = equivEq (funExt (uaβ e))

ua-pathToEquiv : (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-pathToEquiv = uaη

-- Univalence
univalenceIso : Iso (A ≡ B) (A ≃ B)
univalenceIso .Iso.fun = pathToEquiv
univalenceIso .Iso.inv = ua
univalenceIso .Iso.rightInv = pathToEquiv-ua
univalenceIso .Iso.leftInv = ua-pathToEquiv

isEquivPathToEquiv : isEquiv (pathToEquiv {A = A} {B = B})
isEquivPathToEquiv = isoToIsEquiv univalenceIso

univalence : (A ≡ B) ≃ (A ≃ B)
univalence .fst = pathToEquiv
univalence .snd = isEquivPathToEquiv

univalencePath : (A ≡ B) ≡ Lift (A ≃ B)
univalencePath = ua (compEquiv univalence LiftEquiv)

-- Assuming that we have an inverse to ua we can easily prove univalence
module Univalence (au : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B)
                  (aurefl : ∀ {ℓ} {A : Type ℓ} → au refl ≡ idEquiv A) where

  ua-au : (p : A ≡ B) → ua (au p) ≡ p
  ua-au {B = B} = J (λ _ p → ua (au p) ≡ p)
                    (cong ua aurefl ∙ uaIdEquiv)

  au-ua : (e : A ≃ B) → au (ua e) ≡ e
  au-ua {B = B} = EquivJ (λ _ f → au (ua f) ≡ f)
                         (subst (λ r → au r ≡ idEquiv _) (sym uaIdEquiv) aurefl)

  isoThm : Iso (A ≡ B) (A ≃ B)
  isoThm .Iso.fun = au
  isoThm .Iso.inv = ua
  isoThm .Iso.rightInv = au-ua
  isoThm .Iso.leftInv = ua-au

  thm : isEquiv (au {ℓ} {A} {B})
  thm {A = A} {B = B} = isoToIsEquiv {B = A ≃ B} isoThm

-- The original map from UniMath/Foundations
eqweqmap : A ≡ B → A ≃ B
eqweqmap {A = A} e = J (λ X _ → A ≃ X) (idEquiv A) e

eqweqmapid : {A : Type ℓ} → eqweqmap refl ≡ idEquiv A
eqweqmapid {A = A} = JRefl (λ X _ → A ≃ X) (idEquiv A)

univalenceStatement : isEquiv (eqweqmap {ℓ} {A} {B})
univalenceStatement = Univalence.thm eqweqmap eqweqmapid

univalenceUAH : (A ≡ B) ≃ (A ≃ B)
univalenceUAH = _ , univalenceStatement

-- Lemmas for constructing and destructing dependent paths in a function type where the domain is ua.
module _ {A A' : Type ℓ} (e : A ≃ A')
         {B : I → Type ℓ'} {f₀ : A → B i0} {f₁ : A' → B i1} where
  ua→ : (∀ a → PathP B (f₀ (invEq e a)) (f₁ a))
         → PathP (λ i → ua e i → B i) f₀ f₁
  ua→ h i a = hcomp (λ where
      j (i = i0) → f₀ $ retEq e a j
      j (i = i1) → f₁ a
    ) (h (ua-unglue e i a) i)

  ua→Iso : Iso (∀ a → PathP B (f₀ (invEq e a)) (f₁ a))
               (PathP (λ i → ua e i → B i) f₀ f₁)
  ua→Iso .Iso.fun = ua→
  ua→Iso .Iso.inv h a i = h i $ ua-unglueIso e i .Iso.inv a
  ua→Iso .Iso.rightInv h i j a = hcomp (λ where
      k (i = i1) → h j a
      k (j = i0) → f₀ $ retEq e a (k ∨ i)
      k (j = i1) → f₁ a
    ) (h j $ ua-unglueIso e j .Iso.leftInv a i)
  ua→Iso .Iso.leftInv h i a j = hcomp (λ where
      k (i = i1) → h (secEq e a (j ∨ k)) j
      k (j = i0) → f₀ $ commPathIsEq' (e .snd) a i k
      k (j = i1) → f₁ a
    ) (h (secEq e a j) j)

  ua→Equiv : (∀ a → PathP B (f₀ (invEq e a)) (f₁ a))
           ≃ PathP (λ i → ua e i → B i) f₀ f₁
  ua→Equiv = isoToEquiv ua→Iso

-- Useful lemma for unfolding a transported function over ua
-- If we would have regularity this would be refl
transportUAop₁ : ∀ (e : A ≃ B) (f : A → A) (x : B)
               → transport (λ i → ua e i → ua e i) f x ≡ equivFun e (f (invEq e x))
transportUAop₁ e f x i = transportRefl (equivFun e (f (invEq e (transportRefl x i)))) i

-- Binary version
transportUAop₂ : ∀ (e : A ≃ B) (f : A → A → A) (x y : B)
               → transport (λ i → ua e i → ua e i → ua e i) f x y ≡
                 equivFun e (f (invEq e x) (invEq e y))
transportUAop₂ e f x y i =
    transportRefl (equivFun e (f (invEq e (transportRefl x i))
                                 (invEq e (transportRefl y i)))) i

-- Alternative version of EquivJ that only requires a predicate on functions
elimEquivFun : (P : (A : Type ℓ) → (A → B) → Type ℓ')
             → (r : P B (idfun B)) → (e : A ≃ B) → P A (e .fst)
elimEquivFun P r e = subst (λ x → P (x .fst) (x .snd .fst)) (contrSinglEquiv e) r

-- Isomorphism induction
elimIso : {B : Type ℓ} → (Q : {A : Type ℓ} → (A → B) → (B → A) → Type ℓ') →
          (h : Q (idfun B) (idfun B)) → {A : Type ℓ} →
          (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
elimIso {ℓ} {ℓ'} {B} Q h {A} = rem1
  where
  P : (A : Type ℓ) → (f : A → B) → Type (ℓ-max ℓ' ℓ)
  P A f = (g : B → A) → section f g → retract f g → Q f g

  rem : P B (idfun B)
  rem g sfg rfg = subst (Q (idfun B)) (λ i b → (sfg b) (~ i)) h

  rem1 : {A : Type ℓ} → (f : A → B) → P A f
  rem1 f g sfg rfg = elimEquivFun P rem (isoToEquiv (iso f g sfg rfg)) g sfg rfg

uaInvEquiv : ∀ (e : A ≃ B) → ua (invEquiv e) ≡ sym (ua e)
uaInvEquiv {A = A} {B = B} e i j = Glue (ua e i) λ where
  (j = i0) → B , filler₁ i
  (j = i1) → A , filler₂ i
    where
    filler₁ : PathP (λ i → B ≃ ua e i) (invEquiv e) (idEquiv _)
    filler₁ = equivPathP $ funExt λ x → invEqFiller e x

    filler₂ : PathP (λ i → A ≃ ua e i) (idEquiv _) e
    filler₂ = equivPathP $ funExt λ x → equivFunFiller e x

uaCompEquiv-filler : (e : A ≃ B) (f : B ≃ C) → Square (ua e) (ua (e ∙ₑ f)) refl (ua f)
uaCompEquiv-filler e f = congP (λ _ → ua) $
  equivPathP $ funExt λ x → equivFunFiller f (e .fst x)

uaCompEquiv : ∀ {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) → ua (e ∙ₑ f) ≡ ua e ∙ ua f
uaCompEquiv e f = cong fst $ compPath-unique refl (ua e) (ua f)
  (ua (compEquiv e f) , uaCompEquiv-filler e f)
  (ua e ∙ ua f , compPath-filler (ua e) (ua f)) 

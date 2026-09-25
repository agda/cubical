{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.SmashLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Data.Nat

open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.SmashProduct.SymmetricMonoidal
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Connected

open import Cubical.Homotopy.Serre.FiniteCW
open import Cubical.Homotopy.Serre.LastMinuteLemmas.ConnectedLemmas
open import Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

-- move to Cubical.HITs.SmashProduct.Base
Iso-Smash-⋀ : {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (Smash A B) (A ⋀ B)
Iso-Smash-⋀ .Iso.fun = Smash→⋀
Iso-Smash-⋀ .Iso.inv = ⋀→Smash
Iso-Smash-⋀ {A = A} {B = B} .Iso.sec x =
  ⋀-fun≡ (Smash→⋀ ∘ ⋀→Smash) (idfun _)
    refl
    (λ _ → refl)
    (λ a i j → push (inl a) i)
    (λ x → flipSquare
            (cong-∙∙ Smash→⋀
              (sym (gluel (pt A))) (gluer (pt B)) (sym (gluer x))
            ∙ doubleCompPath≡compPath _ _ _
            ∙ assoc _ _ _
            ∙ cong₂ _∙_ (cong₂ _∙_ (λ j i → push (push tt j) i) refl
                       ∙ rCancel (push (inr (pt B)))) refl
            ∙ sym (lUnit (push (inr x))))) x
Iso-Smash-⋀ .Iso.ret basel = refl
Iso-Smash-⋀ {A = A} {B = B} .Iso.ret baser =
  sym (gluel (pt A)) ∙' gluer (pt B)
Iso-Smash-⋀ .Iso.ret (proj x y) = refl
Iso-Smash-⋀ .Iso.ret (gluel a i) = refl
Iso-Smash-⋀ {A = A} {B = B} .Iso.ret (gluer b i) j =
  hcomp (λ k → λ {(i = i0) → gluer b (~ k)
                 ; (j = i0) → doubleCompPath-filler
                                (sym (gluel (pt A)))
                                (gluer (pt B)) (sym (gluer b)) k (~ i)
                 ; (j = i1) → gluer b (i ∨ ~ k)})
        (gluer (pt B) (~ i ∨ j))

-- move to Cubical.HITs.SmashProduct.Base
⋀-fun≡Dep : {A : Pointed ℓ} {B : Pointed ℓ'} {C : A ⋀ B → Type ℓ''}
  → (f g : (x : A ⋀ B) → C x)
  → (p : f (inl tt) ≡ g (inl tt))
  → (h : (x : _) → f (inr x) ≡ g (inr x))
  → ((a : fst A) → SquareP (λ i j → C (push (inl a) j))
                            (cong f (push (inl a)))
                            (cong g (push (inl a)))
                            p (h (a , (pt B))))
  → ((b : fst B) → SquareP (λ i j → C (push (inr b) j))
                            (cong f (push (inr b)))
                            (cong g (push (inr b)))
                            p (h ((pt A) , b)))
  → (x : _) → f x ≡ g x
⋀-fun≡Dep {A = A} {B} {C} f g p h pl pr x i =
  comp (λ k → C (Iso.sec Iso-Smash-⋀ x k))
       (λ k → λ {(i = i0) → f (Iso.sec Iso-Smash-⋀ x k)
                ; (i = i1) → g (Iso.sec Iso-Smash-⋀ x k)})
       (lem (⋀→Smash x) i)
  where
  lem : (x : Smash A B) → f (Smash→⋀ x) ≡ g (Smash→⋀ x)
  lem basel = p
  lem baser = p
  lem (proj x y) = h (x , y)
  lem (gluel a i) j = pl a j (~ i)
  lem (gluer b i) j = pr b j (~ i)

-- move to Cubical.Homotopy.Connected
private
  ⋀→idfun' : (A : Pointed ℓ) {B : Type ℓ'} (C : Pointed ℓ'')
    (f : typ A → B) → A ⋀ C → (B , f (pt A)) ⋀ C
  ⋀→idfun' A C f = f ⋀→refl idfun (typ C)

  ⋀→idfun'≡⋀→idfun : (A : Pointed ℓ) {B : Type ℓ'} {C : Pointed ℓ''}
    → (f : typ A → B) (x : A ⋀ C)
    → ((f , refl) ⋀→ idfun∙ C) x ≡ ⋀→idfun' A C f x
  ⋀→idfun'≡⋀→idfun A {C = C} f =
    ⋀-fun≡ ((f , refl) ⋀→ idfun∙ _) (⋀→idfun' A C f)
      refl (λ _ → refl)
      (λ x → flipSquare (sym (rUnit (push (inl (f x))))))
      λ x → flipSquare (sym (rUnit (push (inr x))))

module isConnected⋀→Lemmas
  {A : Pointed ℓ} {B' : Type ℓ'} {C : Pointed ℓ''}
  (f : typ A → B') (nC nf : ℕ)
  (P : (B' , f (pt A)) ⋀ C → TypeOfHLevel ℓ''' (predℕ (nC + nf)))
  (d : (x : _) → P ((⋀→idfun' A C f) x) .fst) where
  B : Pointed _
  B = B' , f (pt A)

  Q : fst C → Type _
  Q c = fiber {A = (k : fst B) → fst (P (inr (k , c)))}
               {B = (k : fst A) → fst (P (inr (f k , c)))}
               (_∘ f) (d ∘ λ a → inr (a , c))

  Q⋆ : Q (pt C)
  Q⋆ .fst b = subst (fst ∘ P) (push (inl b)) (d (inl tt))
  Q⋆ .snd i a =
    transp (λ j → fst (P ((push (inl (f a))) (i ∨ j))))
         i (d (push (inl a) i))

  module _ (Q-full : (c : fst C) → Q c)
           (Q-fullβ : Q-full (pt C) ≡ Q⋆) where
    g : (b : fst B)(c : fst C) → P (inr (b , c)) .fst
    g b c = Q-full c .fst b

    gₗ : (a : fst A) (c : fst C)
      → g (f a) c ≡ d (inr (a , c))
    gₗ a c = funExt⁻ (Q-full c .snd) a

    gᵣ : (b : fst B)
      → g b (pt C) ≡ Q⋆ .fst b
    gᵣ b = funExt⁻ (cong fst Q-fullβ) b

    gₗ≡gᵣ : (a : fst A)
      → Square (gₗ a (pt C)) (gᵣ (f a))
                refl (sym (funExt⁻ (snd Q⋆) a))
    gₗ≡gᵣ a i j =
      hcomp (λ k → λ {(i = i0) → gₗ a (pt C) (j ∨ ~ k)
                     ; (i = i1) → gᵣ (f a) j
                     ; (j = i0) → gₗ a (pt C) (~ i ∧ ~ k)
                     ; (j = i1) → snd Q⋆ (~ i) a})
            (snd (Q-fullβ j) (~ i) a)

    r : (b : B ⋀ C) → P b .fst
    r (inl x) = d (inl tt)
    r (inr (x , c)) = g x c
    r (push (inl x) i) =
      ((λ j → transp (λ k → fst (P (push (inl x) (j ∧ k))))
                      (~ j) (d (inl tt)))
      ▷ (sym (gᵣ x))) i
    r (push (inr x) i) =
      (cong d (push (inr x)) ▷ sym (gₗ (pt A) x)) i
    r (push (push a j) i) = lem j i
      where
      lem : SquareP (λ i j → P (push (push a i) j) .fst)
            ((λ j → transp (λ k → fst (P (push (inl (f (pt A)))
                            (j ∧ k)))) (~ j) (d (inl tt)))
            ▷ sym (gᵣ (pt B)))
            ((cong d (push (inr (pt C)))
            ▷ sym (gₗ (pt A) (pt C))))
            refl
            refl
      lem i =
          (λ j → comp
            (λ k → P (push (push a (i ∧ k)) j) .fst)
            (λ k → λ {(i = i0) →
              transp (λ k → fst (P (push (inl (f (pt A))) (j ∧ k))))
                     (~ j) (d (inl tt))
                    ; (i = i1) → d (push (push tt k) j)
                    ; (j = i0) → d (inl tt)
                    ; (j = i1) →
              transp (λ k → fst (P (push (inl (f (pt A)))
                                      (i ∨ k)))) i
                       (d (push (inl (pt A)) i))})
                  (transp (λ k → fst (P (push (inl (f (snd A)))
                                          ((i ∨ k) ∧ j))))
                          (i ∨ ~ j) (d (push (inl (snd A)) (i ∧ j)))))
        ▷ sym (gₗ≡gᵣ (pt A) (~ i))

    sec : r ∘ ⋀→idfun' A C f ≡ d
    sec = funExt
      (⋀-fun≡Dep (r ∘ (⋀→idfun' A C f)) d
        refl
        (λ x → gₗ (fst x) (snd x))
        (λ a i j → hcomp (λ k →
          λ {(i = i0) → cong (λ x → r (⋀→idfun' A C f x))
                              (push (inl a)) j
           ; (i = i1) → transp (λ r → fst (P (push (inl (f a))
                                              (j ∧ (r ∨ k)))))
                                (~ j ∨ k) (d (push (inl a) (j ∧ k)))
           ; (j = i0) → d (inl tt)
           ; (j = i1) → gₗ≡gᵣ a (~ k) i})
           (doubleWhiskFiller refl
             (λ j → transp (λ k → fst (P (push (inl (f a)) (j ∧ k))))
                            (~ j) (d (inl tt)))
                (sym (gᵣ (f a))) (~ i) j))
        (λ a i j → hcomp (λ k →
          λ {(i = i1) → d (push (inr a) j)
           ; (j = i0) → d (inl tt)
           ; (j = i1) → gₗ (pt A) a (i ∨ ~ k)})
          (d (push (inr a) j))))

isConnected⋀→ : {A B C D : Pointed ℓ} (nf ng nC nB : ℕ)
  → isConnected nC (fst C)
  → isConnected nB (fst B)
  → (f : A →∙ B) (g : C →∙ D)
  → isConnectedFun nf (fst f)
  → isConnectedFun ng (fst g)
  → isConnectedFun (min (predℕ (nC +  nf)) (predℕ (nB + ng))) (f ⋀→ g)
isConnected⋀→ nf ng nC nB cC cD f g cf cg =
  subst (isConnectedFun (min (predℕ (nC + nf)) (predℕ (nB + ng))))
     (sym (cong fst (⋀→∙-comp f (idfun∙ _) (idfun∙ _) g))
     ∙ funExt (λ x → cong₂ (λ f g → (f ⋀→ g) x) (∘∙-idʳ f) (∘∙-idˡ g)))
     (isConnectedFunCompMin (predℕ (nC + nf)) (predℕ (nB + ng))
       (f ⋀→ idfun∙ _) (idfun∙ _ ⋀→ g)
       (isConnected⋀ₗ→ nf nC cC f cf)
       (isConnected⋀ᵣ→ ng nB cD g cg))
  where
  isConnected⋀ₗ→' : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ}
    {B : Type ℓ'} {C : Pointed ℓ''} (nf nC : ℕ)
    → isConnected nC (fst C)
    → (f : typ A → B)
    → isConnectedFun nf f
    → isConnectedFun (predℕ (nC + nf)) (⋀→idfun' A C f)
  isConnected⋀ₗ→' {A = A} {B = B'} {C = C} zero zero cC f cf =
    λ b → tt* , (λ y i → tt*)
  isConnected⋀ₗ→' {A = A} {B = B'} {C = C} (suc nf) zero cC f cf =
    elim.isConnectedPrecompose (⋀→idfun' A C f) nf
      λ P → (λ d → r P d (fst ∘ hLevQ P d) (snd (hLevQ  P d (pt C)) (Q⋆ P d)))
      , λ d → sec P d (fst ∘ hLevQ P d) (snd (hLevQ  P d (pt C)) (Q⋆ P d))
    where
    module _ {ℓ} (P : (B' , f (pt A)) ⋀ C → TypeOfHLevel ℓ nf)
                 (d : (x : _) → P (⋀→idfun' A C f x) .fst) where
      open isConnected⋀→Lemmas {A = A} {B'} {C} f 0 (suc nf) P d public
      hLevQ : (c' : fst C) → isOfHLevel zero (Q c')
      hLevQ c' = isOfHLevelPrecomposeConnected zero nf
        (λ b → P (inr (b , c'))) f (isConnectedFunSubtr nf 1 f cf)
        (λ x → d (inr (x , c')))
  isConnected⋀ₗ→' {A = A} {B = B'} {C = C} nf (suc nC) cC f cf =
    elim.isConnectedPrecompose (⋀→idfun' A C f) (nC + nf)
      λ P → (λ d → r P d (Q-full P d) (Q-fullβ P d))
      , λ d → sec P d (Q-full P d) (Q-fullβ P d)
    where
    module _ {ℓ} (P : (B' , f (pt A)) ⋀ C → TypeOfHLevel ℓ (nC + nf))
                 (d : (x : _) → P (⋀→idfun' A C f x) .fst) where
      open isConnected⋀→Lemmas {A = A} {B'} {C} f (suc nC) nf P d public
      hLevQ : (c' : fst C) → isOfHLevel nC (Q c')
      hLevQ c' = isOfHLevelPrecomposeConnected nC (nf)
                   (λ b → P (inr (b , c'))) f cf λ x → d (inr (x , c'))

      Q-full = Iso.inv (elim.isIsoPrecompose (λ _ → pt C) nC
                       (λ t → Q t , hLevQ t)
                       (isConnectedPoint _ cC (pt C)))
                       (λ _ → Q⋆)

      Q-fullβ = elim.isIsoPrecomposeβ (λ _ → pt C) nC
                     (λ t → Q t , hLevQ t)
                     (isConnectedPoint _ cC (pt C))
                     (λ _ → Q⋆) tt

  isConnected⋀ₗ→ : ∀ {ℓA ℓB ℓC}
    {A : Pointed ℓA} {B : Pointed ℓB}
    {C : Pointed ℓC} (nf nC : ℕ)
    → isConnected nC (fst C)
    → (f : A →∙ B)
    → isConnectedFun nf (fst f)
    → isConnectedFun (predℕ (nC + nf)) (f ⋀→ idfun∙ C)
  isConnected⋀ₗ→ {A = A} {B = B , b} {C} nf nC cC =
    uncurry λ f p cf
      → J (λ b p → isConnectedFun (predℕ (nC + nf)) ((f , p) ⋀→ idfun∙ C))
          (transport (λ i → isConnectedFun (predℕ (nC + nf))
                             (λ x → ⋀→idfun'≡⋀→idfun A {C = C} f x (~ i)))
            (isConnected⋀ₗ→' nf nC cC f cf)) p

  isConnected⋀ᵣ→ : {A B C  : Pointed ℓ} (nf nC : ℕ)
    → isConnected nC (fst C)
    → (f : A →∙ B)
    → isConnectedFun nf (fst f)
    → isConnectedFun (predℕ (nC + nf)) (idfun∙ C ⋀→ f)
  isConnected⋀ᵣ→ {C = C} nf nC x f cf =
    subst (isConnectedFun (predℕ (nC + nf)))
      (sym (cong fst (⋀comm-sq' (idfun∙ _) f)))
      (isConnectedComp ⋀comm→ ((f ⋀→ idfun∙ _) ∘ ⋀comm→)
        (predℕ (nC + nf))
        (isEquiv→isConnected _ (isoToIsEquiv ⋀CommIso) (predℕ (nC + nf)))
         (isConnectedComp (f ⋀→ idfun∙ _) ⋀comm→ (predℕ (nC + nf))
           (isConnected⋀ₗ→ nf nC x f cf)
               (isEquiv→isConnected _ (isoToIsEquiv ⋀CommIso) _)))

-- move to Cubical.HITs.SmashProducts
Susp^⋀≃∙⋀Susp^ : (A B : Pointed ℓ) (nA nB : ℕ)
   → (Susp∙^ (nA + nB) (A ⋀∙ B))
   ≃∙ ((Susp∙^ nA A) ⋀∙ (Susp∙^ nB B))
Susp^⋀≃∙⋀Susp^ A B zero zero = idEquiv∙ _
Susp^⋀≃∙⋀Susp^ A B zero (suc nB) =
  compEquiv∙ (Susp^Equiv∙ nB
   (compEquiv∙ ((congSuspEquiv (isoToEquiv ⋀CommIso)) , refl)
    (compEquiv∙ (invEquiv (isoToEquiv (SuspSmashCommIso {A = B} {A}))
                , refl)
                (isoToEquiv ⋀CommIso , refl))))
     (Susp^⋀≃∙⋀Susp^ A (Susp∙ (typ B)) zero nB)
Susp^⋀≃∙⋀Susp^ A B (suc nA) nB =
  compEquiv∙ (Susp^Equiv∙ (nA + nB)
    (isoToEquiv (invIso SuspSmashCommIso) , refl))
    (Susp^⋀≃∙⋀Susp^ (Susp∙ (typ A)) B nA nB)

-- move to Cubical.HITs.Susp.Properties
Susp∙^Susp≡Susp^Susp∙ : {A : Pointed ℓ} (n : ℕ)
  → Susp∙ (Susp^ n (typ A)) ≡ Susp∙^ n (Susp∙ (typ A))
Susp∙^Susp≡Susp^Susp∙ {A = A} zero = refl
Susp∙^Susp≡Susp^Susp∙ {A = A} (suc n) =
  Susp∙^Susp≡Susp^Susp∙ {A = Susp∙ (typ A)} n

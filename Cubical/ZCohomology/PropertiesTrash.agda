{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.PropertiesTrash where


open import Cubical.ZCohomology.Base
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.NatMinusTwo.Base renaming (-1+_ to -1+₋₂_ ; 1+_ to 1+₋₂_)
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Prod.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation 
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; _-_)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

is-_-Truncated : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                 (n : ℕ₋₂) → (f : A → B) → Type (ℓ-max ℓ ℓ')
is-_-Truncated {A = A} {B = B} n f = (b : B) → isOfHLevel (2+ n) (fiber f b)

_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m

canceller : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q
canceller {ℓ} {A} {a} {b} {c} p q r id = (rUnit p ∙ (λ j → (p ∙ (rCancel r (~ j)))) ∙ assoc p r (sym r)) ∙ (cong (λ x → x ∙ (sym r)) id) ∙ sym (assoc q r (sym r)) ∙ (λ j → q ∙ (rCancel r j)) ∙ sym (rUnit q)

switcher : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p : a ≡ b) (q r : a ≡ c) → p ∙ (sym p) ≡ q ∙ (sym r) → r ≡ q
switcher {ℓ} {A} {a} {b} {c} p q r id = (lUnit r) ∙ ((λ j → ((rCancel p (~ j))) ∙ r)) ∙ (cong (λ x → x ∙ r) id) ∙ sym (assoc q (sym r) r) ∙  (λ j → q ∙ (lCancel r j)) ∙ sym (rUnit q)


Lemma296b : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A y) → transport (λ i → B (p (~ i) )) (g a) ≡ f (transport (λ i → A (p (~ i))) a))
Lemma296b {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x} (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A y) → transport (λ i → B (p (~ i))) (g a) ≡ f (transport (λ i → A (p (~ i))) a)))
                                                                     λ f g → transport (λ i → helper1 f g (~ i)) (helper2 f g)
  where
  helper1 : (f : (A x) → (B x)) (g : (A x) → (B x)) →
            ((transport (λ i → A (refl {x = x} i) → B (refl {x = x} i)) f ≡ g) ≡ ((a : A x) → transport (λ i → B (refl {x = x} (~ i))) (g a) ≡ f (transport (λ i → A (refl {x = x} (~ i))) a)))
           ≡ ((f ≡ g) ≡ ((a : A x) → g a ≡ f a))
  helper1 f g i = ((transportRefl f i ≡ g) ≡ ((a : A x) → transportRefl (g a) i ≡ f (transportRefl a i)))

  helper2 : (f : (A x) → (B x)) (g : (A x) → (B x)) → ((f ≡ g) ≡ ((a : A x) → g a ≡ f a))
  helper2 f g =  isoToPath (iso (λ p a → sym (funExt⁻ p a)) (λ p → sym (funExt p) ) (λ x → refl) λ x → refl)

Lemma296 : ∀{ℓ ℓ' ℓ''} {X : Type ℓ} {x y : X} {A : X → Type ℓ'} {B : X → Type ℓ''}
           (p : x ≡ y)
           (f : (A x) → (B x))
           (g : (A y) → (B y)) →
           (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡ ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a))
Lemma296 {ℓ = ℓ} {X = X} {x = x} {y = y} {A = A} {B = B} = J {ℓ} {X} {x}
                                                            (λ y p → (f : (A x) → (B x)) (g : (A y) → (B y)) →
                                                                     (transport (λ i → (A (p i)) → (B (p i))) f ≡ g) ≡
                                                                          ((a : A x) → transport (λ i → B (p i)) (f a) ≡ g (transport (λ i → A (p i)) a)))
                                                            (λ f g → transport (λ i → reflTransport f g (~ i)) (reflCase f g))
  where
  reflTransport : (f g : A x → B x) → ((transport (λ i → A (refl {x = x} i) → B (refl {x = x} i)) f ≡ g) ≡ ((a : A x) → transport (λ i → B (refl {x = x} i)) (f a) ≡ g (transport (λ i → A (refl {x = x} i)) a))) ≡ ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflTransport f g j = (transportRefl f j ≡ g) ≡ ((a : A x) → transportRefl (f a) j ≡ g (transportRefl a j))

  reflCase : (f g : A x → B x) → ((f ≡ g) ≡ ((a : A x) → f a ≡ g a))
  reflCase f g = isoToPath (iso (λ p → funExt⁻ p) (λ p → funExt p) (λ x → refl) λ x → refl) 





{- TODO: Prove Kₙ ≡ Ω Kₙ₊₁  -}

invPathCancel : {a b : A} → (p : a ≡ b) → p ∙ (sym p) ≡ refl
invPathCancel {a = a} {b = b} p = J {x = a} (λ y p → p ∙ (sym p) ≡ refl ) (sym (lUnit refl)) p
invPathCancel2 : {a b : A} → (p : a ≡ b) →  (sym p) ∙ p ≡ refl
invPathCancel2 {a = a} {b = b} p = J {x = a} (λ y p → (sym p) ∙ p ≡ refl ) (sym (lUnit refl)) p

cancelReflMid : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q : b ≡ a) → p ∙ refl ∙ q ≡ p ∙ q
cancelReflMid {ℓ = ℓ}{A = A} {a = a} {b = b} p q = J {ℓ} {A} {a} {ℓ} (λ b p → ((q : b ≡ a) →  p ∙ refl ∙ q ≡ p ∙ q)) (λ r → sym (lUnit (refl  ∙ r ))) {b} p q



inducedFun : ∀{ℓ''} {k : ℕ₋₂}
             (f : A → B) →
             (P : (B → HLevel ℓ'' (2+ k))) →
             (((b : B) → fst (P b)) → (a : A) → fst (P (f a)) )
inducedFun  f P  = λ g a → g (f a)

Lemma757i→ii : ∀ {ℓ} (f : A → B) (n : ℕ₋₂) →
                is- n -Connected f →
                (P : B → HLevel ℓ (2+ n)) →
                isEquiv (inducedFun f P)
Lemma757i→ii f n isCon P = {!!}

Lemma757i→iii : ∀ {ℓ} (f : A → B) (n : ℕ₋₂) →
                is- n -Connected f →
                (P : B → HLevel ℓ (2+ n)) →
                hasSection (inducedFun f P)
Lemma757i→iii f n isCon P = {!!} , (λ b  → {!!})

Lemma861* : ∀{ℓ} (n k : ℕ₋₂) (f : A → B) →
           (n ≡ neg2 → ⊥) → (k ≡ neg2 → ⊥) →
           (n ≡ (suc neg2) → ⊥) → (k ≡ (suc neg2) → ⊥) →
           (is- n -Connected f) →
           (P : B → HLevel ℓ (2+ k)) →
           Σ ℕ₋₂ (λ a → (a +₋₂ n ≡ k) × ((a ≡ neg2 → ⊥) × (a ≡ (suc neg2) → ⊥)))  →
           is- ((k -₋₂ n) -₋₂ (suc (suc (suc (suc neg2))))) -Truncated (inducedFun {k = k } f P)
Lemma861* n neg2 f n2 k2 n1 k1 isCon P pair = ⊥-elim (k2 refl)
Lemma861* n (suc neg2) f n2 k2 n1 k1 isCon P pair = ⊥-elim (k1 refl)
Lemma861* neg2 (suc (suc k)) f n2 k2 n1 k1 isCon P pair = ⊥-elim (n2 refl)
Lemma861* (suc neg2) (suc (suc k)) f n2 k2 n1 k1 isCon P pair = ⊥-elim (n1 refl)
Lemma861* (suc (suc n)) (suc (suc k)) f n2 k2 n1 k1 isCon P (neg2 , (x , (x₁ , x₂))) = ⊥-elim (x₁ refl)
Lemma861* (suc (suc n)) (suc (suc k)) f n2 k2 n1 k1 isCon P (suc neg2 , (x , (x₁ , x₂))) = ⊥-elim (x₂ refl)
Lemma861* (suc (suc n)) (suc (suc k)) f n2 k2 n1 k1 isCon P (suc (suc neg2) , (pf , (x₁ , x₂))) = {!pf!}
Lemma861* (suc (suc n)) (suc (suc k)) f n2 k2 n1 k1 isCon P (suc (suc (suc dif)) , (pf , (x₁ , x₂))) = {!isCon!}


Lemma861 : ∀{ℓ} (n k : ℕ) (f : A → B) →
           (is- (ℕ→ℕ₋₂ n) -Connected f) →
           (P : B → HLevel ℓ (suc (suc k))) →
           Σ ℕ (λ a → a + n ≡ k)  →
           is- (ℕ→ℕ₋₂ ((k - n) - 2)) -Truncated (inducedFun f P)
Lemma861 {A = A} {B = B} n k f isCon P (dif , pf) = {!!} where

  helper1 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (a ≡ b) ≡ Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)
  helper1 l a b = sym (ua (Σ≡ )) 

  helper2 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (Σ (fst a ≡ fst b) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) (snd a) (snd b)) ≡ Σ ((x : B) → (fst a) x ≡ (fst b) x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)
  helper2 l (g , p) (h , q) = isoToPath (iso lrFun  rlFun (λ b → refl) λ b → refl) where
    lrFun : (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q) → Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q
    lrFun (a , b) = funExt⁻ a , b
    rlFun : (Σ ((x : B) → g x ≡ h x) λ r → PathP (λ i → (x : A) → r (f x) i ≡ l x) p q) → (Σ (g ≡ h) λ r → PathP (λ i → (x : A) → (r i) (f x) ≡ l x) p q)
    rlFun (a , b) = (funExt a) , b
  abstract
    helper3 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (r : (x : B) → (fst a) x ≡ (fst b) x) → (PathP (λ i → (x : A) → r (f x) i ≡ l x) (snd a) (snd b)) ≡ ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) )
    helper3 l (g , p) (h , q) r j = hcomp (λ k → λ{ (j = i0) → (PathP (λ i → (x : A) → r (f x) (i ∧  i1) ≡ l x) p λ x → (sym (lUnit (q x)) k ))
                                                ; (j = i1) → throwAbout k})
                                        ((PathP (λ i → (x : A) → r (f x) (i ∧  ~ j) ≡ l x) p λ x → (λ i → r (f x) (~ j ∨ i)) ∙ (q x)))
      where
        postulate
          throwAbout : (p ≡ λ x → r (f x) ∙ q x) ≡ ((x : A) → (((r (f x))) ≡ (p x) ∙ (sym (q x))))
      {- Very heavy proof  
      throwAbout : (p ≡ λ x → r (f x) ∙ q x) ≡ ((x : A) → (((r (f x))) ≡ (p x) ∙ (sym (q x)))) 
      throwAbout = isoToPath (iso (λ g x → transport (λ i → throwAboutHelper (p x) (r (f x)) (sym (q x)) i ) (funExt⁻ g x) )
                                (λ g → funExt λ x → transport (λ i → throwAboutHelper (p x) (r (f x)) (sym (q x)) (~ i) ) (g x))
                                (λ b → funExt λ x → (λ j → transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (i ∨ j)) (transport (λ i₁ → throwAboutHelper (p x) (r (f x)) (λ i₂ → q x (~ i₂)) ((~ i₁) ∨ ( j))) (b x))) ∙ λ j → transportRefl (transportRefl (b x) j) j  )
                                λ b → (λ j → funExt (λ x → transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (~ i ∧ (~ j)))
                                                                     (transport (λ i → throwAboutHelper (p x) (r (f x)) (λ i₁ → q x (~ i₁)) (i ∧ (~ j)))
                                                                                (λ i → b i x))))
                                             ∙ (λ j → funExt (λ x → transportRefl ((transportRefl (λ i → b i x)) j) j  ) )) where


        throwAboutHelper : ∀{ℓ} {A : Type ℓ} {a b c : A} →  (p : a ≡ b) (q : a ≡ c) (r : b ≡ c) → (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r)
        throwAboutHelper {ℓ} {A} {a} {b} {c}  = J {ℓ} {A} {a} (λ b p → (q : a ≡ c) (r : b ≡ c) → (p ≡ q ∙ (sym r) ) ≡ (q ≡ p ∙ r))
                                              (J {ℓ} {A} {a} (λ c q → (r : a ≡ c) → (refl ≡ q ∙ (sym r) ) ≡ (q ≡ refl ∙ r) )
                                                 λ r → (λ i → refl ≡ lUnit (sym r) (~ i)) ∙ isoToPath (iso (λ id → cong (λ x → sym x) id) (λ id → cong (λ x → sym x) id ) (λ b → refl) λ b → refl)  ∙ λ i → (refl ≡ lUnit r i) )
      -}

    helper4 : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (r : (x : B) → (fst a) x ≡ (fst b) x) → ((x : A) → r (f x) ≡ ((snd a) x) ∙ sym ((snd b) x) ) ≡  ((λ (x : A) → r (f x)) ≡ (λ (x : A) → ((snd a) x) ∙ sym ((snd b) x)))
    helper4 l (h , q) (g , p) r = isoToPath (iso (λ p → funExt p) (λ p → funExt⁻ p) (λ b → refl) λ b → refl)


    FINAL : (l : (a : A) → fst (P (f a))) (a b : Σ ((b : B) → fst (P b)) λ g → (a : A) → g (f a) ≡ l a ) → (a ≡ b) ≡ Σ ((x : B) → (fst a) x ≡ (fst b) x) (λ r → ((λ (x : A) → r (f x)) ≡ (λ (x : A) → ((snd a) x) ∙ sym ((snd b) x))))
    FINAL l (g , p) (h , q)  = helper1 _ _ _  ∙ helper2 _ _ _ ∙ (λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper3 l (g , p) (h , q) r j)) ∙ λ j → Σ ((x : B) → g x ≡ h x) (λ r → helper4 l (g , p) (h , q) r j)

    
      
{-
Lemma862 : (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ₋₂) →
           (is- (suc (suc n)) -ConnectedType (typ A)) →
           (is- (suc (suc m)) -ConnectedType (typ B)) →
           (P : (typ A) → (typ B) → HLevel (ℓ-max ℓ ℓ') (2+ ((suc (suc n)) +₋₂ (suc (suc m))))) →
           (f : ((a : (typ A)) → fst (P a (pt B)))) →
           (g : ((b : (typ B)) → fst (P (pt A) b))) →
           (p : f (pt A) ≡ g (pt B)) →
           Σ ((a : typ A) → (b : typ B) → fst (P a b)) λ h → Σ (((a : typ A) → h a (pt B) ≡ f a) × ((b : typ B) → h (pt A) b ≡ g b) ) λ pair → p ≡ sym ((proj₁ pair) (pt A) ) ∙ (proj₂ pair) (pt B)
Lemma862 {ℓ = ℓ} {ℓ' = ℓ'} (A , a₀) (B , b₀) n m conA conB P f g p = (λ a b → {!!}) , ({!!} , {!!}) where
  Q : A → Type (ℓ-max ℓ ℓ')
  Q a = Σ ((b : B) → fst (P a b )) λ k → f a ≡ k (b₀)

  a₀-map : Unit → A
  a₀-map x = a₀

  conOfa₀-map : is- (suc n) -Connected a₀-map
  conOfa₀-map = {!!}

  b₀-map : Unit → B
  b₀-map x = b₀

  conOfb₀-map : is- (suc n) -Connected b₀-map
  conOfb₀-map = {!!}

  conOfQ : (a : A) → isOfHLevel (2+ (suc n)) (Q a)
  conOfQ = {!!}

  typesQ : (a : A) → Σ ((a : A) → Q a) λ ℓ → ℓ a₀ ≡ (g , p)
  typesQ a  = (fst (Lemma757i→iii a₀-map (suc n) conOfa₀-map (λ a → (Q a , conOfQ a ))) (λ x → (g , p))) ,
              cong (λ f → f tt) (snd (Lemma757i→iii a₀-map (suc n) conOfa₀-map (λ a → (Q a , conOfQ a ))) (λ x → (g , p)))

  QisFib : (a : A) → Q a ≡ fiber ( λ x → inducedFun {A = Unit} {B = B} b₀-map (P a) x tt) (f a)
  QisFib a = {!!}

  Ok : (a : A) → is- (suc n) -ConnectedType (fiber ( λ x → inducedFun {A = Unit} {B = B} b₀-map (P a) x tt) (f a))
  Ok a = {!!}

σ : A → {a : A} → typ (Ω ((Susp A) , north))
σ x {a} = merid x ∙ sym (merid a)


code : ∀{ℓ} {A : Type ℓ} {a : A} (n : ℕ₋₂) → is- (suc (suc n)) -ConnectedType A → (y : Susp A) → (north ≡ y → Type ℓ)
code {A = A} {a = a} n iscon north p = (∥ fiber (λ y → σ y {a}) p ∥ ((suc (suc n)) +₋₂ (suc (suc n))))
code {ℓ} {A = A} {a = a} n iscon south q = ∥ fiber merid q ∥ ((suc (suc n)) +₋₂ (suc (suc n)))
code {ℓ} {A = A} {a = a} n iscon (merid c i) = pathToConstruct i where
  pathToConstruct : PathP (λ i → north ≡ merid c i → Type ℓ) (code {a = a} n iscon north) (code {a = a} n iscon south)
  pathToConstruct = toPathP (transport (λ i → transpId (~ i)) λ q → sym (ua ((RlFun q) , (RlFunEquiv q))))
    where

    transpId : (transport (λ i₁ → north ≡ merid c i₁ → Type ℓ) (code {a = a} n iscon north) ≡ code {a = a} n iscon south) ≡
                ((q : north ≡ south) → (code {a = a} n iscon south q) ≡ (code {a = a} n iscon north (q ∙ sym (merid c))))
    transpId = (transport (λ i₁ → north ≡ merid c i₁ → Type ℓ) (code {a = a} n iscon north) ≡ code {a = a} n iscon south)
                             ≡⟨ Lemma296b {A = λ x → north ≡ x} {B = λ _ → Type ℓ} (merid c) (code {a = a} n iscon north) (code {a = a} n iscon south) ⟩
                          ((q : north ≡ south) → code {a = a} n iscon south q ≡ code {a = a} n iscon north (transport (λ i →  north ≡ (merid c (~ i))) q))
                             ≡⟨ (λ i → ((q : north ≡ south) → code {a = a} n iscon south q ≡ code {a = a} n iscon north (helper q (sym (merid c)) i))) ⟩
                          ((q : north ≡ south) → (code {a = a} n iscon south q) ≡ (code {a = a} n iscon north (q ∙ sym (merid c)))) ∎
                          
      where
      helper : ∀{ℓ} {A : Type ℓ} {a b c : A} (q : a ≡ b) (p : b ≡ c) →
                    (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p)
      helper {ℓ = ℓ} {A = A} {a = a} {b = b} {c = c} q = J {ℓ} {A} {b}
                                                          (λ c p → (transport (λ i →  a ≡ (p i)) q) ≡ (q ∙ p))
                                                          (transportRefl q ∙ rUnit q)

    

    RlFun : {c : A} (q : north ≡ south) → code {a = a} n iscon north (q ∙ sym (merid c)) → code {a = a} n iscon south q
    RlFun {c = c} q x  = (funHelper a) x
      where
        funHelper :  (a : A) → (∥ Σ A (λ x₁ → merid x₁ ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ sym (merid c)) ∥ (suc (suc n) +₋₂ suc (suc n))) → ∥ Σ A (λ x → merid x ≡ q) ∥ ((suc (suc n) +₋₂ suc (suc n)))
        funHelper a = ind (λ x → isOfHLevel∥∥ _) λ r → sufMap (fst r) (snd r)
          where

          sufMap : (x₂ : A) → (merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ ((suc (suc n) +₋₂ suc (suc n))) 
          sufMap x₂  = fst (Lemma862 (A , a) (A , a) n n iscon iscon (λ x₂ c → (((merid x₂  ∙ sym (merid a)) ≡ (q ∙ sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ ((suc (suc n) +₋₂ suc (suc n))) ) , isOfHLevelPi (2+ ((suc (suc n) +₋₂ suc (suc n)))) λ _ → isOfHLevel∥∥ _)) firstFun secondFun  (funExt (λ x → λ j → ∣ (refl j) , (maybe (merid a) q (canceller (merid a) q (sym (merid a)) x ) x j) ∣  ))) x₂ c
            where

            

            firstFun : (a₁ : A) → merid a₁ ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ (λ i₁ → merid (pt (A , a)) (~ i₁)) → ∥ Σ A (λ x₁ → merid x₁ ≡ q) ∥ (suc (suc n) +₋₂ suc (suc n))
            firstFun x r = ∣ x , canceller (merid x) q (sym (merid a)) r ∣
        
          {-J {ℓ} {A} {b} (λ d r → ((p ∙ r) ≡ (q ∙ r)) ≡ (p ≡ q)) λ i → sym (rUnit p) i ≡ sym (rUnit q) i-}
            secondFun : (b : typ (A , a)) → merid (pt (A , a)) ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ (λ i₁ → merid b (~ i₁)) → ∥ Σ A (λ x₁ → merid x₁ ≡ q) ∥ (suc (suc n) +₋₂ suc (suc n))
            secondFun b s = ∣ b , switcher (merid a) q (merid b) s ∣

      {- need eckmann hilton -}


            maybe : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p q : a ≡ b) → (p ≡ q) → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller p q (sym p) P ≡ switcher p q p P
            maybe {ℓ} {A} {a} {b} p q = J {ℓ} {a ≡ b} {p} (λ q _ → (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller p q (sym p) P ≡ switcher p q p P) (J {ℓ} {A} {a} (λ b p → (P : p ∙ (sym p) ≡ p ∙ (sym p)) → canceller p p (sym p) P ≡ switcher p p p P) (λ P → {!refl!}) p)


    canceller2 : ∀ {ℓ} {A : Type ℓ} {a b c : A} → (p q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q
    canceller2 {ℓ} {A} {a} {b} {c} p q r id = (rUnit p ∙ (λ j → (p ∙ (rCancel r (~ j)))) ∙ assoc p r (sym r)) ∙ (cong (λ x → x ∙ (sym r)) id) ∙ sym (assoc q r (sym r)) ∙ (λ j → q ∙ (rCancel r j)) ∙ sym (rUnit q)

    RlFunEquiv : {c : A} → (q : north ≡ south) → isEquiv (RlFun {c = c} q)
    RlFunEquiv {c = c} q = fst (Lemma757i→iii {A = Unit} {B = A} (λ x → a) ((suc (suc n))) (λ b → {!fst iscon!} , {!!}) (λ a → ((isEquiv (RlFun {c = a} q)) , {!!} ))) (λ t → baseCase) c where
        baseCase : isEquiv (RlFun {c = a} q)
        baseCase = snd (isoToEquiv (iso (RlFun {c = a} q) (ind (λ _ → isOfHLevel∥∥ _) λ a → {!!}) {!!} {!!}))

        claim : RlFun {c = a} q ≡ ind (λ _ → isOfHLevel∥∥ _) λ b → ∣ (fst b) , canceller2 _ _ _ (snd b)  ∣
        claim = {!!} --cannot say before I have prev lemmas
        
        isCona₀ : is- (suc (suc n)) -Connected (λ (x₁ : Unit) → a)
        isCona₀ = λ b → {!!} , {!!}


Lemma8610 : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {a1 a2 : A} {B : A → Type ℓ'} (C : (a : A) → (B a → Type ℓ'')) (p : a1 ≡ a2) (b : B a2) → transport (λ i → {!uncurry C ?!}) {!!} ≡ {!(ua ?)!}
Lemma8610 = {!!}

Thm864 : (n : ℕ₋₂) (a : A) (iscon : is- (suc (suc n)) -ConnectedType A) {y : Susp A} → (p : north ≡ y) → isContr (code {a = a} n iscon y p)
Thm864 {ℓ} {A} n a iscon =  J {ℓ} {Susp A} {north} (λ y p → (isContr (code {a = a} n iscon y p))) (∣ a , (rCancel _) ∣ , (λ y → {!refl!}))  where
  center : {!!}
  center = {!!}

Freudenthal : (n : ℕ₋₂ ) (A : Pointed ℓ) → is- (suc (suc n)) -ConnectedType (typ A) → ∥ typ A ∥ (((suc (suc n) +₋₂ suc (suc n))) ) ≡ ∥ typ (Ω (Susp (typ A) , north)) ∥ (((suc (suc n) +₋₂ suc (suc n))) )
Freudenthal n A isCon = ua ({!!} , {!Lemma757i→ii ? ? ? ?!})



-}


















{- J {ℓ} {A} {a} (λ b p → ((q : a ≡ b) (P : p ∙ (sym p) ≡ q ∙ (sym p)) → canceller p q (sym p) P ≡ switcher p q p P)) λ q id → (λ i → canceller refl q ((sym symRefl ) (~ i)) id) ∙ {!!} ∙ λ j → switcher refl q (symRefl (~ j)) id where
      test : {q : a ≡ a} {id : refl ∙ (λ i₁ → refl (~ i₁)) ≡ q ∙ (λ i₁ → refl {x = a} (~ i₁))} → canceller refl q refl id ≡ (sym (rCancel refl)) ∙ (cong (λ x → x ∙ refl) ((lUnit refl) ∙ id)) ∙ (sym (assoc q refl refl)) ∙ (λ j → q ∙ (rCancel refl j)) ∙ (sym (rUnit q))
      test {q = q} {id = id} i = {!(sym (rCancel refl)) ∙ (cong (λ x → x ∙ (symRefl (~ i))) ((lUnit refl) ∙ id)) ∙ (sym (assoc q refl (symRefl (~ i)))) ∙ (λ j → q ∙ (rCancel refl j)) ∙ (sym (rUnit q))!} -}

{-

  RlFun : (q : north ≡ south) → (∥ ((fiber (λ y → σ y) (q ∙ sym (merid c))) ≡  (Σ A (λ x₁ → merid x₁ ∙ (λ i₁ → merid a (~ i₁)) ≡ q ∙ sym (merid c)))) ∥ ((suc n) +₋₂ suc (suc n))) → (∥ (fiber merid q)  ≡  (Σ A (λ x₁ → merid x₁ ≡ q)) ∥ ((suc n) +₋₂ suc (suc n)))
  RlFun q x = ind (λ x → isOfHLevel∥∥ _) ({!cong funHelper!}) x where
    funHelper : (a : A) → merid a ∙ (sym (merid c)) ≡ q ∙ (sym (merid c)) → ∥ Σ A (λ x → merid x ≡ q) ∥ ((suc (suc n) +₋₂ suc (suc n)))
    funHelper a = {!!}

  LrFun : ((q : north ≡ south) → (code {a = a} n iscon south q) → (code {a = a} n iscon north (q ∙ sym (merid c))))
  LrFun = {!!}

-}

    -- fst gp (f x) ≡ fst hq (f x)
    -- fst gp (f x) ≡ fst gp (f x)


{-

  helper2 : (l : (x : A) → (fst (P (f x)) ))
            (gp hq  : Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)) →
            Σ (fst gp ≡ fst hq) (λ a≡ → PathP (λ i → (a : A) → a≡ i (f a) ≡ l a) (snd gp) (snd hq))
              ≡ Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) ( λ r → ((λ x → (r (f x))) ≡ λ (x : A) → (snd gp x) ∙ sym (snd hq x) ))
  helper2 l gp hq = isoToPath (iso fun finv (λ b i → {!fst gp x!} , {!!}) {!!}) where


    finv : Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) (λ r → (inducedFun {k = (suc (suc k))} f (λ b → (fst gp b ≡ fst hq b) ,   hLevelSuc (suc (suc (1+ (1+₋₂ k)))) (fst (P b)) (snd (P b)) (fst gp b) (fst hq b) ) r ≡ (λ (x : A) → (snd gp x) ∙ sym (snd hq x)))) → Σ (fst gp ≡ fst hq) (λ a≡ → PathP (λ i → (a : A) → a≡ i (f a) ≡ l a) (snd gp) (snd hq))
    finv (fs , sn) = {!!} {- (funExt fs) , {!(snd hq) !}-} where
      propLemma : (a : A) → isProp (fst hq (f a) ≡ l a)
      propLemma a f g = {!!}
      

    fun : Σ (fst gp ≡ fst hq) (λ a≡ → PathP (λ i → (a : A) → a≡ i (f a) ≡ l a) (snd gp) (snd hq)) → Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) (λ r → (inducedFun {k = (suc (suc k))} f (λ b → (fst gp b ≡ fst hq b) ,   hLevelSuc (suc (suc (1+ (1+₋₂ k)))) (fst (P b)) (snd (P b)) (fst gp b) (fst hq b) ) r ≡ (λ (x : A) → (snd gp x) ∙ sym (snd hq x))))
    fun (fs , sn) = (funExt⁻ fs) , (funExt (λ x → test5)) where        

        test5 : {x : A} → PathP (λ _ → fst gp (f x) ≡ fst hq (f x) ) (λ i → (fs i) (f x))  (snd gp x ∙ sym (snd hq x))
        test5 {x = x} i j = hcomp ((λ k → λ{ (i = i0) → fs j (f x) ; (i = i1) → test3 {x = x} k j ; (j = i0) → fst gp (f x) ; (j = i1) → fs (~ i ∨ k) (f x) })) (test4 {x = x}  i j) where
          test3 : {x : A} → PathP (λ i → fst gp (f x) ≡ fs i (f x)) (snd gp x ∙ sym (snd gp x)) (snd gp x ∙ sym (snd hq x))
          test3  {x = x} i = (snd gp x) ∙ (sym (sn i x))
          
          test4 : {x : A} → PathP (λ i → fst gp (f x) ≡ fs (~ i) (f x)) (λ i → (fs i) (f x)) (snd gp x ∙ (sym (snd gp x)))
          test4 {x = x} i = hcomp (λ j → λ { (i = i0) → (λ i → (fs i) (f x)) ; (i = i1) → (sym (invPathCancel (snd gp x)) j)  } ) (test i) where
            test : {x : A} → PathP (λ i → fst gp (f x) ≡ fs (~ i) (f x)) (λ i → (fs i) (f x)) (refl {x = (fst gp (f x))})
            test {x = x} j i =  fs (i ∧ ( ~ j)) (f x)

  helper3 : (l : (x : A) → (fst (P (f x)) )) (gp hq  : Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)) → (gp ≡ hq) ≡ Σ (fst gp ≡ fst hq)
      (λ a≡ → PathP (λ i → (a : A) → a≡ i (f a) ≡ l a) (snd gp) (snd hq))
  helper3 l gp hq = sym (ua (Σ≡ {A = ((a : B) → fst (P a))} {B = (λ x → (a : A) → x (f a) ≡ l a)} {x = gp} {y = hq}))


-}













































    
{-





















------------------
{- Sn ≡ Ω(Sn+1) -}








-------------------- Guillaume Test --------------------










sphereSuc : (n : ℕ) → (S₊ n) → (S₊ (suc n))
sphereSuc n north = north
sphereSuc n south = south
sphereSuc (suc n) (merid a i) = merid (sphereSuc n a) i

helplemma : {A : Type ℓ}  {a : A} {p q : a ≡ a} {P : p ≡ q} → (C : (a ≡ a) → Type ℓ) → (a1 a2 : C (P i0)) → (b1 b2 : C (P (i1))) → PathP (λ i → C (P i)) a1 b2 → (a1 ≡ a2) → (b1 ≡ b2) → PathP (λ i → C (P i)) a2 b2
helplemma {ℓ = ℓ} {a = a}{p = p} {q = q} {P = P} C a1 a2 b1 b2 depP a1a2 b1b2 = {!J {ℓ} {?} !}

pathExtender : (B : A → Type ℓ) → {!!}
pathExtender = {!!}

promote : (n : ℕ) → (S₊ n) → typ (Ω ((S₊ (suc n)) , north) )
promote zero north = refl {x = north}
promote zero south = refl {x = north}
promote (suc n) north = refl {x = north}
promote (suc n) south = refl {x = north}
promote (suc n) (merid a i) = (( sym (rCancel (merid (merid a i0))) ∙ (λ i → (merid (merid a i) ∙ (sym (merid (merid north i)))))) ∙ rCancel (merid (merid a i1)) ) i

decode' : (n : ℕ) → ∥ (S₊ n) ∥ (ℕ→ℕ₋₂ n) → ∥ typ (Ω (S₊ (suc n) , north)) ∥ (ℕ→ℕ₋₂ n) 
decode' n = rec {A = (S₊ n)} {B = ∥ typ (Ω (S₊ (suc n) , north)) ∥ (ℕ→ℕ₋₂ n) } (isOfHLevel∥∥ {A =  typ (Ω (S₊ (suc n) , north))} (ℕ→ℕ₋₂ n)) λ x → ∣ promote n x ∣ 

CODES : (n : ℕ) → S₊ (suc n) → Type₀
CODES n north = ∥ S₊ n ∥ (ℕ→ℕ₋₂ n)
CODES n south = ∥ S₊ n ∥ (ℕ→ℕ₋₂ n)
CODES n (merid a i) = {!(typ ((Ω^ (suc n)) (Type₀ , ∥ S₊ n ∥ (ℕ→ℕ₋₂ n))))!}

encode' : (n : ℕ) →  ∥ typ (Ω ((S₊ (suc n)) , north)) ∥ (ℕ→ℕ₋₂ n) → ∥ S₊ n ∥ (ℕ→ℕ₋₂ n)
encode' n = rec {A = typ (Ω ((S₊ (suc n)) , north))}
                {B = ∥ S₊ n ∥ (ℕ→ℕ₋₂ n)}
                (isOfHLevel∥∥ {A = (S₊ n )} (ℕ→ℕ₋₂ n))
                λ x → {!(cong (CODES n) x) ?!} 

{-
functions : (n : ℕ) (f : A → B) →
            (typ ((Ω^ n) ((A → B) , f))) ≡
                ((x : A) → (typ ((Ω^ n) (B , f x))))
functions zero = {!!}
functions {A = A} {B = B}(suc zero) f = isoToPath (iso (λ g x i  → (g i) x) (λ g → funExt {f = f} {g = f} g  ) (λ b → refl) λ b → refl) 
functions (suc (suc zero)) f =  isoToPath (iso {!!} {!!} {!!} {!!})
  where
  helper' : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           typ (Ω (Ω ((A → B) , f))) ≡ ( _≡_ {A = ( _≡_ f f)} (refl {x = f})  (refl {x = f}))
  helper' f = refl
  helper : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           (typ (Ω (Ω ((A → B) , f)))) ≡ ( _≡_ {A = ((x : A) → (f x ≡ f x) )}
                                         (λ x _ → f x)
                                         (λ x _ → f x))
  helper f = isoToPath (iso (λ g i x j → (g i j) x) (λ x k j y → ((x k) y) j) (λ b  → refl) λ b → refl)

  helper2 :{A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           ( _≡_ {A = ((x : A) → (f x ≡ f x) )} (λ x _ → f x) (λ x _ → f x))
            ≡
             ((x : A) → (_≡_ {A = f x ≡ f x} (λ _ → f x) (λ _ → f x )))
  helper2 = {!!}
  

functions (suc (suc (suc n))) f = {!!} -- isoToPath (iso {!!} (λ x → {!!}) {!!} {!!})
  where
  helper : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           typ (Ω (Ω (Ω ((Ω^ n) ((A → B) , f))))) ≡ ( _≡_ {A =  typ (Ω (Ω ((Ω^ n) ((A → B) , f))))}
                                         (λ _ → pt (Ω ((Ω^ n) ((A → B) , f))))
                                         (λ _ → pt (Ω ((Ω^ n) ((A → B) , f)))))
  helper f = refl

    where
    Ω^n : {A : Type ℓ} {B : Type ℓ'} →
          (f : A → B) →
          typ (Ω (Ω ((Ω^ n) ((A → B) , f)))) ≡ ((x : A) → typ (Ω (Ω ((Ω^ n) (B , f x)))))
    Ω^n f = functions (suc (suc n)) f
    Ω^n' : {A : Type ℓ} {B : Type ℓ'} →
          (f : A → B) →
           typ (Ω (Ω (Ω ((Ω^ n) ((A → B) , f))))) ≡  typ (Ω (((x : A) → typ (Ω (Ω ((Ω^ n) (B , f x))))) , (λ _ → refl)))
    Ω^n' f i = typ (Ω (( Ω^n f i) , {!!}))


-}

Fun1000 : (n : ℕ) {f : A → B} →
        ((typ ((Ω^ (suc n)) ((A → B) , f))) →
        (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
-- Fun1001 : (n : ℕ) {f : A → B} → Fun1000 n {f} refl ≡ (λ x → refl)
Fun1000 zero p x i = p i x
Fun1000 (suc n) p x = {!Fun1000 n (p j) x i!}
-- Fun1001 = {!!}


lrFun2* : (n : ℕ) {f : A → B} →
          Σ ((typ ((Ω^ (suc n)) ((A → B) , f))) →
              (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
            (λ g  → (g refl) ≡ (λ x → refl))
lrFun2* zero {f = f} = funExt⁻ , refl
lrFun2* (suc n) {f = f} = (λ p x → {!(funExt⁻ (cong (fst (lrFun2* n)) p) x)!})
                          ,
                          funExt (λ y → cancelReflMid (λ i → snd (lrFun2* n) (~ i) y)
                                                      (λ i → snd (lrFun2* n {f = f}) i y) ∙
                                                        invPathCancel (λ i → snd (lrFun2* n) (~ i) y))

lrFun : (n : ℕ) {f : A → B} →
        ((typ ((Ω^ (suc n)) ((A → B) , f))) →
        (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
lrFun n = fst (lrFun2* n)


  where
  

rlFun* : (n : ℕ) {f : A → B} →
         Σ ((((x : A) → (typ ((Ω^ (suc n)) (B , f x))))) →
             ((typ ((Ω^ (suc n)) ((A → B) , f)))) )
           (λ g → (g (λ x → snd (((Ω^ (suc n)) (B , f x)))) ≡ pt  ((Ω^ (suc n)) ((A → B) , f))))
              
rlFun* zero {f = f} = (λ g → funExt g) , refl
rlFun* {A = A} {B = B}(suc n) {f = f} = (λ g → (sym (snd (rlFun* n)) ∙ cong (fst (rlFun* n)) (funExt g) ∙ snd (rlFun* n)))
                                        ,
                                        (cancelReflMid (λ i → snd (rlFun* n) (~ i)) (snd (rlFun* n))) ∙
                                          invPathCancel (λ i → snd (rlFun* n) (~ i))

rlFun : (n : ℕ) {f : A → B} →
              (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))) →
              ((typ ((Ω^ (suc n)) ((A → B) , f)))) 
rlFun n {f = f} = fst (rlFun* n {f = f})
  where

functions2 : (n : ℕ) (f : A → B) →
             ((x : A) → (typ ((Ω^ n) (B , f x)))) ≃ (typ ((Ω^ n) ((A → B) , f)))
                
functions2 {A = A} {B = B} zero f = idEquiv (A → B)
functions2 {A = A} {B = B} (suc n) f = rlFun n  , record { equiv-proof = λ y → ((fst (lrFun2* n)) y , {!!}) , {!!} } where

  helper : (n : ℕ) (y : (typ ((Ω^ (suc n)) ((A → B) , f)))) →  (rlFun n ((fst (lrFun2* n)) y) ≡ y)
  helper zero y = refl 
  helper (suc n) y  = (λ i → (sym (snd (rlFun* n))) ∙ ((helper5 (funExt (λ x → sym (cong (λ g → g x ) (snd (lrFun2* n))))) (cong (fst (lrFun2* n)) y) (funExt (λ x → (cong (λ g → g x ) (snd (lrFun2* n))))) (fst (rlFun* n))) i ) ∙ (snd (rlFun* n))) ∙ {!helper !} 
         where


          idTest : (n : ℕ) → (rlFun n {f} (λ x → snd (lrFun2* n {f}) i1 x) ≡ rlFun n (λ x → snd (lrFun2* n {f}) i0 x)) ≡  ((fst (rlFun* n) (λ x → snd (Ω ((Ω^ n) (B , f x))))) ≡ (pt (Ω ((Ω^ n) ((A → B) , f)))))
          idTest n  i = refl {x = rlFun n {f} (λ x → snd (lrFun2* n {f}) i1 x)} i ≡ idTest1 i where
            idTest1 : rlFun n (λ x → snd (lrFun2* n {f}) i0 x) ≡  (pt (Ω ((Ω^ n) ((A → B) , f))))
            idTest1 = helper n (pt (Ω ((Ω^ n) ((A → B) , f))))


          test : (n : ℕ) → PathP (λ i → {!!}) ( (cong (rlFun n {f}) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x))))))  (snd (rlFun* n {f}))
          test n i = {!!} where
          

          maybe2 : {n : ℕ} (i : I) → snd (rlFun* n) (~ i) ≡  (pt (Ω ((Ω^ n) ((A → B) , f))))
          maybe2 {n} i j = snd (rlFun* n) ((~ i) ∨ j)

          maybe3 : (n : ℕ) → (pt (Ω ((Ω^ n) ((A → B) , f)))  ≡ rlFun n (λ x → snd (lrFun2* n {f}) i0 x))
          maybe3 n =    sym (snd (rlFun* n {f})) ∙ λ i → rlFun n (hihih ( ~ i)) where
            hihih : (λ (x : A) → snd (lrFun2* n {f}) i0 x) ≡ (λ x → snd (Ω ((Ω^ n) (B , f x))))
            hihih = funExt λ x → cong (λ g → g x) (snd (lrFun2* n))

          maybe : (n : ℕ) (y : (typ (Ω ((Ω^ (suc n)) ((A → B) , f))))) →  ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x)))))) ∙ (cong (rlFun n) (funExt (λ x → (λ i → fst (lrFun2* n) (y i) x)))) ∙  ((sym (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x))))))) ≡  (snd (rlFun* n)) ∙ y ∙ (sym (snd (rlFun* n)))
          maybe n y i =  test n i ∙ (cong (λ x → (helper n x) i) y ) ∙ sym (test n i)
          -- (λ j → (snd (rlFun* n)) (~ j ∨ i)) ∙ {!!}
          
          --  ∙ {!λ i → (cong (λ x → helper n x i ) y)!} ∙ {!!}  -- (cong (λ x → helper n x i ) ?)   

          compTest : (n : ℕ) (y : (typ (Ω ((Ω^ (suc n)) ((A → B) , f))))) →
            (sym (snd (rlFun* n))) ∙
            ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x)))))) ∙
            (cong (rlFun n) (funExt (λ x → (λ i → fst (lrFun2* n) (y i) x)))) ∙
            ((sym (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x))))))) ∙
            (snd (rlFun* n)) ≡
            refl ∙ {!!} ∙ y ∙ {!!} ∙ refl
          compTest n y i =  (λ i₁ → snd (rlFun* n {f}) (~ i₁ ∨ i)) ∙
                            {!snd (rlFun* n {f}) (~ i1 ∨ i)!} {- hcomp (λ k → λ{(i = i0) → {!maxZeuner i0!} ; (i = i1) → (maxZeuner i1)}) (maxZeuner i) -} ∙
                            (cong (λ x → (helper n x) i) y ) ∙
                            {!snd (rlFun* n {f}) (~ i1 ∨ i)!} 
                            ∙ λ i₁ → snd (rlFun* n {f}) (i₁ ∨ i)

            where

            maxZeuner : (i : I) → snd (rlFun* n) i ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i
            maxZeuner i j = hcomp (λ k → λ{(j = i0) → snd (rlFun* n) i ; (j = i1) → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i ∨ (~ k)) }) (snd (rlFun* n {f}) (i ∨ j))
            maxZeunerHelper : (i : I) → maxZeuner i0 ≡ {!snd (rlFun* n) i0 ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i0!}
            maxZeunerHelper = {!!}

            gimmeMore : (i : I) → rlFun n (λ x → snd (lrFun2* n {f}) i0 x) ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i
            gimmeMore i = (λ j → rlFun n (λ x → snd (lrFun2* n {f}) j x)) ∙ (snd (rlFun* n {f})) ∙ λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i ∨ (~ j))

            gimmeLeft : (i : I) → rlFun n (λ x → snd (lrFun2* n {f}) i1 x) ≡ snd (rlFun* n) i
            gimmeLeft i = λ j → snd (rlFun* n {f}) (j ∧ i)

            gimmei0 : ((sym (gimmeLeft i0)) ∙  ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x)))))) ∙ (gimmeMore i0)) ≡ ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x))))))
            gimmei0 = {!((sym (gimmeLeft i0)))!} where

              gimmei0' : ((sym (gimmeLeft i0))) ≡ refl
              gimmei0' j = refl


  

            gimmei1 : ((sym (gimmeLeft i1)) ∙  ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x)))))) ∙ (gimmeMore i1)) ≡ refl
            gimmei1 = gimmei1' ∙ more!! where

              gimmei1' : ((sym (gimmeLeft i1)) ∙  ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x)))))) ∙ (gimmeMore i1)) ≡ (sym (gimmeLeft i1)) ∙ (snd (rlFun* n {f})) ∙ λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j))
              gimmei1' = ∙-assoc (sym (gimmeLeft i1)) (( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x))))))) ((snd (rlFun* n {f})) ∙ λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j))) where

                ∙-assoc : {A : Type ℓ}{a b c d : A} (p : a ≡ b) (q : b ≡ c) (t : b ≡ d) → p ∙ q ∙ (sym q ∙ t) ≡ p ∙ t
                ∙-assoc {ℓ = ℓ} {A = A} {a = a} {b = b} {c = c} {d = d} p q t  = cong (λ x → p ∙ x) {!q ∙ (sym q ∙ t) ≡ t!}
                

              more!! : (sym (gimmeLeft i1)) ∙ (snd (rlFun* n {f})) ∙ (λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j))) ≡ refl
              more!! = (assoc (sym (gimmeLeft i1))  (snd (rlFun* n {f}))  (λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j)))) ∙ (λ j → (invPathCancel (sym (gimmeLeft i1)) j) ∙ (λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j)))) ∙ lCancel (λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j)))

              more!!! : (λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i1 ∨ (~ j))) ≡ refl
              more!!! = refl
  


            hello : (i : I) → snd (rlFun* n) i ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i
            hello i = (λ j → snd (rlFun* n {f}) (i ∨ j)) ∙ λ j → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (i ∨ (~ j))

            kittyHelper : PathP (λ i → (snd (rlFun* n {f})) i ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i) (hello i0) refl
            kittyHelper j = hcomp (λ k → λ{ (j = i0) → hello i0 ;
                                            (j = i1) → invPathCancel refl k })
                                  ((λ i → snd (rlFun* n {f}) (j ∨ i)) ∙ λ i → helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) (j ∨ (~ i)))
{-
            kittyHelperB : PathP (λ i → (snd (rlFun* n {f})) i ≡ helper n (snd (Ω ((Ω^ n) ((A → B) , f)))) i) ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x)))))) refl
            kittyHelperB i j = hcomp (λ k → λ{ (j = i0) → {!!}
                                           ; (j = i1) → {!(cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x)))))!}} )
                                   {!( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ j) x))))))!}
-}

            -- helloKitty : hello i0 ≡ ( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n) (~ i) x))))))
            -- helloKitty k = {!!}

            -- helloKitty2 : hello i1 ≡ refl
            -- helloKitty2 = {!!}

          mini : (n : ℕ) → rlFun n (λ x → snd (lrFun2* n {f}) i0 x) ≡ pt (Ω ((Ω^ n) ((A → B) , f)))
          mini n = helper n refl

          mini2 : (n : ℕ) → rlFun n (λ x → snd (lrFun2* n {f}) i1 x) ≡ pt (Ω ((Ω^ n) ((A → B) , f)))
          mini2 n = (λ i → rlFun n (λ x → snd (lrFun2* n {f}) (~ i) x)) ∙ helper n refl
          
          leftMost : PathP (λ i → (pt (Ω ((Ω^ n) ((A → B) , f))) ≡ (snd (rlFun* n)) i)) (sym (snd (rlFun* n))) refl
          leftMost i = λ i₁ → snd (rlFun* n) (~ i₁ ∨ i)

  

          notLeftMost : (n : ℕ) → PathP (λ i → mini2 n i ≡ mini n i ) (( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x))))))) refl
          notLeftMost zero i j = {!fst (rlFun* (suc n)) (λ x → snd (lrFun2* (suc n) {f}) (i1) x)!}
          notLeftMost (suc n) i = {!(( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x)))))))!}
            where
            ffs2 : (n : ℕ) (i : I) → (fst (rlFun* n {f}) (λ x → snd (lrFun2* n {f}) (~ i1 ∨ i) x))  ≡ mini n i
            ffs2 n i = ((λ j → fst (rlFun* n) (λ x → snd (lrFun2* n {f}) (i ∨ j) x)) ∙ snd (rlFun* n {f}) ) ∙ λ j → mini n (i ∨ (~ j))

            ffs : (n : ℕ) (i : I) → (fst (rlFun* n {f}) (λ x → snd (lrFun2* n {f}) (~ i0 ∨ i) x))  ≡ mini2 n i
            ffs n i = snd (rlFun* n {f}) ∙ {!mini2 i1!}

            {-

            tester :  ((sym (ffs i0)) ∙ (λ j → fst (rlFun* n) (snd (lrFun2* n {f}) (i0 ∨ (~ j)))) ∙ (ffs2 i0)) ≡ (( (cong (rlFun n) (funExt ((λ x → (λ i → snd (lrFun2* n {f}) (~ i) x)))))))
            tester  = (({!((sym (ffs i1)) ∙ (λ j → fst (rlFun* n) (snd (lrFun2* n {f}) (i1 ∨ (~ j)))) ∙ (ffs2 i1))!}) ∙ sym (rUnit (refl ∙ (λ j → fst (rlFun* n) (snd (lrFun2* n {f}) (~ j)))))) ∙ sym (lUnit (λ j → fst (rlFun* n) (snd (lrFun2* n {f}) (i0 ∨ (~ j)))))
              where
                helpi : (ffs2 i0) ≡ refl
                helpi = {!!}

          snLeftMost : {!(λ j → fst (rlFun* n {f}) (snd (lrFun2* n) (~ j)))!}
          snLeftMost = {!!}

          -}
            
         
          helper2 : (n : ℕ)  (y : typ (Ω (Ω ((Ω^ n) ((A → B) , f))))) → funExt ((λ (x : A) → (λ i → snd (lrFun2* n) (~ i) x) ∙ (λ i → fst (lrFun2* n) (y i) x) ∙ (λ i → snd (lrFun2* n {f = f}) i x))) ≡ (funExt (λ (x : A) → (λ i → snd (lrFun2* n) (~ i) x))) ∙ funExt (λ (x : A) → (λ i → fst (lrFun2* n) (y i) x)) ∙ funExt λ (x : A) → (λ i → snd (lrFun2* n {f = f}) i x)
          helper2 zero y = refl
          helper2 (suc n) y = refl

          helper4 : {A : Type ℓ} {B : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) (g : A → B) → cong g (p ∙ q) ≡ ((cong g p) ∙ (cong g q))
          helper4 {ℓ = ℓ}  {A} {B} {a} {b} {c} p q g  = J {ℓ} {A} {a} {ℓ} (λ b1 p → ((q1 : b1 ≡ c) → cong g (p ∙ q1) ≡ ((cong g p) ∙ (cong g q1))))
                                                             (λ q1 → J {ℓ} {A} {a} {ℓ} (λ c2 q2 → (λ i → g ((refl ∙ q2) i)) ≡ (λ i → g (refl i)) ∙ (λ i → g (q2 i))) ( (λ j → ((λ i → g (((rUnit (λ _ → a)) (~ j) ) i)))) ∙ lUnit ((λ i → g (refl i)))) {c} q1  )
                                                             p  q

          helper5 : {A : Type ℓ} {B : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (g : A → B) → cong g (p ∙ q ∙ r) ≡ ((cong g p) ∙ (cong g q) ∙ (cong g r))
          helper5 {ℓ = ℓ} {A} {B} {a} {b} {c} {d} p q r g = helper4 p (q ∙ r) g ∙  ((cong (λ x → (cong g p) ∙ x )) (helper4 q r g))

          helper3 : (n : ℕ)  (y : typ (Ω (Ω ((Ω^ n) ((A → B) , f))))) → (cong (rlFun n) (funExt (λ x → (λ i₁ → fst (lrFun2* n) (y i₁) x)))) ≡ {!!} 
          helper3 zero y = {!!}
          helper3 (suc n) y = {!(cong (rlFun (suc n)) (funExt (λ x → (λ i₁ → fst (lrFun2* (suc n)) (y i₁) x))))!}

{-
functions' {A = A} {B = B}(suc zero) f = isoToPath (iso (λ g x i  → (g i) x) (λ g → funExt {f = f} {g = f} g  ) (λ b → refl) λ b → refl)
  where
  helper : transport (λ i → (sym (functions' (suc zero) f)) i)  (λ x → refl) ≡ (pt ((Ω ) ((A → B) , f)))
  helper =  {!!}
functions' (suc (suc zero)) f =  isoToPath (iso {!!} {!!} {!!} {!!})
  where
  helper' : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           typ (Ω (Ω ((A → B) , f))) ≡ ( _≡_ {A = ( _≡_ f f)} (refl {x = f})  (refl {x = f}))
  helper' f = refl
  helper : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           (typ (Ω (Ω ((A → B) , f)))) ≡ ( _≡_ {A = ((x : A) → (f x ≡ f x) )}
                                         (λ x _ → f x)
                                         (λ x _ → f x))
  helper f = isoToPath (iso (λ g i x j → (g i j) x) (λ x k j y → ((x k) y) j) (λ b  → refl) λ b → refl)

  helper2 :{A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           ( _≡_ {A = ((x : A) → (f x ≡ f x) )} (λ x _ → f x) (λ x _ → f x))
            ≡
             ((x : A) → (_≡_ {A = f x ≡ f x} (λ _ → f x) (λ _ → f x )))
  helper2 = {!!}
functions' (suc (suc (suc n))) f = {!!}
  where
  helper : {A : Type ℓ} {B : Type ℓ'} →
           (f : A → B) →
           typ (Ω (Ω (Ω ((Ω^ n) ((A → B) , f))))) ≡ ( _≡_ {A =  typ (Ω (Ω ((Ω^ n) ((A → B) , f))))}
                                         (λ _ → pt (Ω ((Ω^ n) ((A → B) , f))))
                                         (λ _ → pt (Ω ((Ω^ n) ((A → B) , f)))))
  helper f = refl

    where
    Ω^n : {A : Type ℓ} {B : Type ℓ'} →
          (f : A → B) →
          typ (Ω (Ω ((Ω^ n) ((A → B) , f)))) ≡ ((x : A) → typ (Ω (Ω ((Ω^ n) (B , f x)))))
    Ω^n f = functions (suc (suc n)) f
    Ω^n' : {A : Type ℓ} {B : Type ℓ'} →
          (f : A → B) →
           (Ω (Ω (Ω ((Ω^ n) ((A → B) , f))))) ≡  (Ω (((x : A) → typ (Ω (Ω ((Ω^ n) (B , f x))))) , (λ _ → refl)))
    Ω^n' f i = (Ω (( Ω^n f i) , {!(transport (λ j → ( Ω^n f j)) (refl i)) !})) where
      lemma : transport (λ i → Ω^n f i) refl ≡ λ _ → refl
      lemma = funExt {f = transport (λ i → Ω^n f i) refl} {g = λ _ → refl} λ x →  {!!} 




 ----------

lrFun3* : (n : ℕ) {f : A → B} →
             Σ ((typ ((Ω^ (suc n)) ((A → B) , f))) →
              (((x : A) → (typ ((Ω^ (suc n)) (B , f x)))))) (λ g  → (g refl) ≡ (λ x → refl))
lrFun3* zero {f = f} = funExt⁻ , refl
lrFun3* {A = A} {B = B} (suc n) {f = f} = (λ p x → transport (λ i → (cong (λ g → g x) (snd (lrFun3* n {f = f}))) i ≡ (cong (λ g → g x) (snd (lrFun3* n {f = f}))) i) (funExt⁻ (cong (λ x → (fst (lrFun3* n) x )) p) x)) ,  funExt (λ x → transpLemma x) 
  module lr where
  helpLemma : (x : A) → ((fst (lrFun3* n) (snd (Ω ((Ω^ n) ((A → B) , f)))) x  ≡ (fst (lrFun3* n) (snd (Ω ((Ω^ n) ((A → B) , f)))) x))) ≡ (typ (Ω (Ω ((Ω^ n) (B , f x)))))
  helpLemma x i = helper x i ≡ helper x i where

    helper : (x : A) → fst (lrFun3* n) (snd (Ω ((Ω^ n) ((A → B) , f)))) x ≡ pt ((Ω ((Ω^ n) (B , f x))))
    helper x = cong (λ g → g x) (snd (lrFun3* n {f = f}))

  transpLemma : (x : A) → transp (λ i → helpLemma x i) i0 refl ≡ refl
  transpLemma x j = transp (λ i → helpLemma x (i ∨ j)) j refl

lrFun3 : (n : ℕ) {f : A → B} → ((typ ((Ω^ (suc n)) ((A → B) , f))) → (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
lrFun3 n {f = f} = (fst (lrFun3* n {f = f})) 

  
rlFun3* : (n : ℕ) {f : A → B} →
              Σ ((((x : A) → (typ ((Ω^ (suc n)) (B , f x))))) →
              ((typ ((Ω^ (suc n)) ((A → B) , f)))) )
              (λ g → (g (λ x → snd (((Ω^ (suc n)) (B , f x)))) ≡ pt  ((Ω^ (suc n)) ((A → B) , f))))



              
rlFun3* zero {f = f} = (λ g → funExt g) , refl
rlFun3* {A = A} {B = B}(suc n) {f = f} = (λ g → transport (λ i → (snd (rlFun3* n {f})) i ≡ (snd (rlFun3* n {f})) i) (cong (fst (rlFun3* n)) (funExt g))) , transpLemma -- (cancelReflMid (λ i → snd (rlFun* n) (~ i)) (snd (rlFun* n))) ∙ invPathCancel (λ i → snd (rlFun* n) (~ i))
  module rl where
  helpLemma : (fst (rlFun3* n) (λ x → snd (Ω ((Ω^ n) (B , f x)))) ≡ fst (rlFun3* n) (λ x → snd (Ω ((Ω^ n) (B , f x))))) ≡ typ (Ω (Ω ((Ω^ n) ((A → B) , f))))
  helpLemma i = (snd (rlFun3* n {f})) i ≡ (snd (rlFun3* n {f})) i

  transpLemma :  transport (λ i → helpLemma i) refl ≡ refl
  transpLemma j = transp (λ i → helpLemma (i ∨ j)) j refl  -- transp (λ i → helpLemma (i ∨ j)) j refl 
  
rlFun3 : (n : ℕ) {f : A → B} →
              (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))) →
              ((typ ((Ω^ (suc n)) ((A → B) , f)))) 
rlFun3 n {f = f} = fst (rlFun3* n {f = f})
  where

functions3 : (n : ℕ) (f : A → B) →
             ((x : A) → (typ ((Ω^ n) (B , f x)))) ≃ (typ ((Ω^ n) ((A → B) , f)))
                
functions3 {A = A} {B = B} zero f = idEquiv (A → B)
functions3 {A = A} {B = B} (suc n) f = rlFun3 n  , record { equiv-proof = λ y → (( (fst (lrFun3* n)) y) , λ i → {!!}) , {!!} } where
  linv : (n : ℕ) (y : typ (Ω ((Ω^ n) ((A → B) , f)))) → rlFun3 n (fst (lrFun3* n {f = f}) y) ≡ y
  linv zero y = refl
  linv (suc n) y  =  {!!}  where
    maybe : rlFun3 (suc n) (fst (lrFun3* (suc n) {f = f}) y) ≡ λ j x → {!((cong (λ x → (fst (lrFun3* n) x )) y) (~ j)) x!}
    maybe = {!!}


inv1 : (n : ℕ) {f : A → B} (g : ((typ ((Ω^ (suc n)) ((A → B) , f))) )) → (rlFun3 n) ((lrFun3 n) g ) ≡ g
inv1 zero {f = f} g = refl
inv1 {A = A} {B = B}(suc n) {f = f} g j = {! -- transp (λ i → (snd (rlFun3* n {f})) (i ∨ j) ≡ (snd (rlFun3* n {f})) (i ∨ j)) i0
                                                     (cong (fst (rlFun3* n)) (funExt (
                                                       (λ x → transp (λ i → (cong (λ g → g x) (snd (lrFun3* n {f = f}))) (i ∨ j)
                                                                             ≡ (cong (λ g → g x) (snd (lrFun3* n {f = f}))) (i ∨ j)) (~ j)
                                                              (funExt⁻ (cong (λ x → (fst (lrFun3* n) x )) g) x))  ) )  )!}

     where
     maybe : PathP (λ i → {! !} ≡ {!!} ) (cong (fst (rlFun3* n)) (funExt (
                                                       (λ x → transport (λ i → (cong (λ g → g x) (snd (lrFun3* n {f = f}))) i
                                                                             ≡ (cong (λ g → g x) (snd (lrFun3* n {f = f}))) i)
                                                              (funExt⁻ (cong (λ x → (fst (lrFun3* n {f}) x )) g) x))  ) )  )
                                                                {!(cong (fst (rlFun3* n)) (funExt ( (λ x → (funExt⁻ (cong (λ x → (fst (lrFun3* n {f}) x )) g) x))))) !}
     maybe j = {!fst (rlFun3* n) (λ x → snd (lrFun3* n {f}) i1 x)!}
-}
-}









{-
Lemma861 : ∀{ℓ''} (n k : ℕ₋₂) →
             Σ ℕ₋₂ (λ num → (suc (suc n)) +₋₂ num ≡ (suc (suc k)) ) →
             (f : A → B) →
             (is- (suc (suc n)) -Connected f) →
             (P : (B → HLevel ℓ'' (2+ (suc (suc k))))) →
             is- (((suc (suc n)) -₋₂ (suc (suc k))) -₋₂ (suc (suc neg2))) -Connected (inducedFun {k = (suc (suc k))}  f P)
Lemma861 n k (neg2 , pf) f conf P b = {!!}
  where
  helper : (((suc (suc n)) -₋₂ (suc (suc k))) -₋₂ (suc (suc neg2))) ≡ neg2
  helper = {!!}
Lemma861 {A = A} {B = B} n k (suc j , pf) f conf P g =  {!!} where
  helper : (l : (x : A) → (fst (P (f x)) )) →
           (fiber (inducedFun {k = (suc (suc k))} f P) l) ≡ Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)
  helper l = isoToPath (iso (fun) finv (λ b → refl) λ b → refl) where
    fun : (fiber (inducedFun {k = (suc (suc k))} f P) l) → Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)
    fun (fs , sn) = fs , λ a  → cong (λ x → x a) sn

    finv : (Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)) →  (fiber (inducedFun {k = (suc (suc k))} f P) l)
    finv (fs , sn) = fs , (funExt sn)

  helper'3 : (l : (x : A) → (fst (P (f x)) ))
            (gp hq  : Σ ((b : B) → (fst (P b))) λ g → (a : A) → (g (f a)) ≡ (l a)) →
            (gp ≡ hq)
              ≡ Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) ( λ r → ((λ x → (r (f x))) ≡ λ (x : A) → (snd gp x) ∙ sym (snd hq x) ))
  helper'3 l gp hq = isoToPath (iso fun finv (λ b i → ({!!})) {!!}) where
    fun : (gp ≡ hq) → Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) ( λ r → ((λ x → (r (f x))) ≡ λ (x : A) → (snd gp x) ∙ sym (snd hq x) ))
    fun path = (λ x i → fst (path i) x ) , funExt λ x → pathFinal {x} where
      pathHelper : {x : A} →  PathP (λ i → fst gp (f x) ≡ fst (path i) (f x)) refl (snd gp x ∙ sym (snd hq x))
      pathHelper {x = x} i = hcomp (λ j → λ{ (i = i0) → rCancel (snd gp x) j ; (i = i1) → (snd gp x ∙ sym (snd hq x))  } ) (snd gp x ∙ sym (snd (path i) x))

      pathHelper2 : {x : A} → PathP (λ i → fst gp (f x) ≡ fst (path (~ i)) (f x)) (λ i → fst (path i) (f x)) refl
      pathHelper2 {x = x} i = λ i₁ → fst (path (i₁ ∧ (~ i))) (f x)

      pathFinal : {x : A} → (λ i → fst (path i) (f x)) ≡ snd gp x ∙ sym (snd hq x)
      pathFinal {x = x} = transport (λ i → PathP (λ j₁ → (lCancel (λ i → fst gp (f x) ≡ fst (path i) (f x))) i j₁)
                                                         (λ i → fst (path i) (f x))
                                                         (snd gp x ∙ sym (snd hq x)))
                                    (compPathP pathHelper2 pathHelper)


    finv : Σ ((x : B) → (((fst gp) x) ≡ ((fst hq) x))) ( λ r → ((λ x → (r (f x))) ≡ λ (x : A) → (snd gp x) ∙ sym (snd hq x) )) → (gp ≡ hq)
    finv (fs , sn) = ΣPathP {x = gp} {y = hq} (funExt (λ b → fs b) , {! !})  -- (λ b → (fs b) i) , λ a →  hcomp (λ k → λ{(i = i0) → (snd gp a) ; (i = i1) → {!!}}) (transp (λ j → fs (f a) (i ∧ j) ≡ l a) (~ i) ((snd gp) a))
      where
      potTerm : {a : A} → PathP (λ i → (a : A) → funExt (λ b → fs b) i (f a) ≡ l a) (snd gp) (snd hq)
      potTerm {a = a} j = λ a → hcomp {!(transp (λ i → funExt (λ b → fs b) (i) (f a) ≡ l a) i0 ((snd gp a))) !} (transp (λ i → funExt (λ b → fs b) (i ∧ j) (f a) ≡ l a) i0 ((snd gp a))) 
       
      helper2 : {a : A} → (fs (f a)) ∙ (snd hq a)  ≡ snd gp a
      helper2 {a = a} = (cong (λ x → x ∙ (snd hq a)) (cong (λ x → x a) sn)) ∙ sym (assoc (snd gp a) (sym (snd hq a))  (snd hq a)) ∙ (λ j → (snd gp a) ∙ (lCancel (snd hq a)) j) ∙ sym (rUnit (snd gp a)) -}

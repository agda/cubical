{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.Loopspace where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- homotopy Group -}
π : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π n A = ∥ typ ((Ω^ n) A) ∥ 2

{- loop space map -}
Ω→ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → (Ω A →∙ Ω B)
Ω→ (f , f∙) = (λ p → (sym f∙ ∙ cong f p) ∙ f∙) , cong (λ q → q ∙ f∙) (sym (rUnit (sym f∙))) ∙ lCancel f∙

{- Commutativity of loop spaces -}
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p
{-
s : ∀ {ℓ} {A : Type ℓ} {x : A} → (p q : refl {x = x} ≡ refl {x = x}) → {!!} -- (λ i → p i (~ i)) ∙ refl ≡ (λ i → q i i) ∙ refl
s α β i = {!!}

-- (λ j z → doubleCompPath-filler (α (j ∧ ~ i)) refl (β (j ∧ i)) z i) ∙ {!λ j z → doubleCompPath-filler (β (j ∨ i)) refl (α (j ∨ ~ i)) (~ j) i!}
-- (λ j → doubleCompPath-filler (α (j ∧ ~ i)) refl (β (j ∧ i)) j i) ∙ λ j → doubleCompPath-filler (α (~ i ∨ j)) refl (β (i ∨ j)) (~ j) i


filler⋆ : ∀ {ℓ} {A : Pointed ℓ} (p q : refl {x = pt A} ≡ refl)
  → PathP (λ i → PathP (λ j → pt A ≡ q j i) (λ i → p i0 i0) λ i → p i0 i0) (sym p)
             λ i j → hcomp (λ k → λ { (j = i0) → p i0 i0
                                     ; (j = i1) → q i (j ∧ k)
                                     ; (i = i0) → p i0 i0
                                     ; (i = i1) → p i0 i0})
                                    (p (~ i) j)
filler⋆ p q z i j =
  hfill (λ k → λ { (j = i0) → p i0 i0
                  ; (j = i1) → q i (j ∧ k)
                  ; (i = i0) → p i0 i0
                  ; (i = i1) → p i0 i0})
        (inS (p (~ i) j))
        z

module _ {ℓ} {A : Pointed ℓ} (n : ℕ) where

  top : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ k → (refl {x = α i0 i0}) ≡ (λ j → filler⋆ α β i1 k j)) α β
  top α β l i j =
    hcomp
      (λ k → λ
        { (i = i0) → α i0 i0
        ; (j = i0) → α i0 i0
        ; (i = i1) → filler⋆ α β k l j
        ; (j = i1) → β (i ∧ l) k
        ; (l = i0) → α i j
        ; (l = i1) → β i (j ∧ k)
        })
      (α (i ∧ ~ l) j)

  side : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ k → (λ j → filler⋆ α β i1 k j) ≡ (refl {x = α i0 i0})) β α
  side α β l i j =
    hcomp
      (λ k → λ
        { (i = i1) → α i0 i0
        ; (i = i0) → filler⋆ α β k l j
        ; (j = i0) → α i0 i0
        ; (j = i1) → β (i ∨ l) k
        ; (l = i0) → β i (j ∧ k)
        ; (l = i1) → α i j
        })
      (α (i ∨ ~ l) j)
  Eckmann-Hilton : (α β : typ ((Ω^ (2 + n)) A)) → α ∙ β ≡ β ∙ α
  Eckmann-Hilton α β l =
    (λ i j → top α β l i j) ∙ (λ i j → side α β l i j)



  anot : (α β : typ ((Ω^ (2 + n)) A)) → sym (filler⋆ β α i1) ≡ filler⋆ α β i1
  anot α β i j k =
    hcomp (λ l → λ { (j = i0) → {!!}
                    ; (j = i1) → {!!}
                    ; (k = i0) → {!!}
                    ; (k = i1) → {!!}})
          {!!}
-}
{-
i = i0 ⊢ sym
         (λ i₁ j₁ →
            hcomp
            (λ { k₁ (j₁ = i0) → β i0 i0
               ; k₁ (j₁ = i1) → α i₁ (i1 ∧ k₁)
               ; k₁ (i₁ = i0) → β i0 i0
               ; k₁ (i₁ = i1) → β i0 i0
               })
            (β (~ i₁) j₁))
         j k
i = i1 ⊢ hcomp
         (λ { k₁ (k = i0) → α i0 i0
            ; k₁ (k = i1) → β j (i1 ∧ k₁)
            ; k₁ (j = i0) → α i0 i0
            ; k₁ (j = i1) → α i0 i0
            })
         (α (~ j) k)
j = i0 ⊢ refl i0
j = i1 ⊢ refl i0
k = i0 ⊢ snd ((Ω^ n) A)
k = i1 ⊢ snd ((Ω^ n) A)
-}
{-
  test3 : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ j → PathP (λ k → refl ≡ anot α β j k) α β)
                                                (symP (top β α)) (top α β)
  test3 α β r i j k =
    hcomp (λ s → λ { (i = i0) → {!!}
                    ; (r = i0) → {!!}
                    ; (i = i1) → {!!}
                    ; (j = i0) → {!!}
                    ; (j = i1) → {!anot α β (~ s ∨ r) i k!}
                    ; (k = i0) → {!!}
                    ; (k = i1) → {!!}})
          {!!}
  {-
r = i0 ⊢ symP (top β α) i j k
r = i1 ⊢ top α β i j k
i = i0 ⊢ α j k
i = i1 ⊢ β j k
j = i0 ⊢ refl k
j = i1 ⊢ anot α β r i k
k = i0 ⊢ snd ((Ω^ n) A)
k = i1 ⊢ snd ((Ω^ n) A)
-}

  test4 : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ j → PathP (λ k → anot α β j k ≡ refl) β α)
                                                (symP (side β α)) (side α β)
  test4 = {!!}

  syll : (α β : typ ((Ω^ (2 + n)) A)) → Eckmann-Hilton α β ≡ sym (Eckmann-Hilton β α) 
  syll α β z l = (λ i j → test3 α β (~ z) l i j) ∙ λ i j → test4 α β (~ z) l i j

  s1 : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ k → refl ≡ filler⋆ β α i1 (~ k)) α β
  s1 α β = symP (top β α)

  s2 : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ k → refl ≡ filler⋆ α β i1 k) α β
  s2 α β = top α β

  mapath : (α β : typ ((Ω^ (2 + n)) A)) (k z : I) → PathP (λ i → α i0 i0 ≡ ((λ i → α (~ k ∨ i) (~ z ∨ i)) ∙ (λ i → α (k ∧ i) (z ∧ i))) i) (filler⋆ β α (~ z) (~ k)) (filler⋆ β α z k)
  mapath α β k = {!!} -- compPathP (λ z k → filler⋆ β α (~ z) (~ k)) (filler⋆ β α)

  test14 : (α β : typ ((Ω^ (2 + n)) A)) → PathP (λ j → PathP (λ k → refl ≡ {!s1 α β!}) α β) (s1 α β) (top α β)
  test14 = {!!}


-}
{-
z = i0 ⊢ Eckmann-Hilton α β l i j
z = i1 ⊢ sym (Eckmann-Hilton β α) l i j
l = i0 ⊢ (α ∙ β) i j
l = i1 ⊢ (β ∙ α) i j
i = i0 ⊢ snd (Ω ((Ω^ n) A)) j
i = i1 ⊢ snd (Ω ((Ω^ n) A)) j
j = i0 ⊢ snd ((Ω^ n) A)
j = i1 ⊢ snd ((Ω^ n) A)
-}


-- syll : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : refl {x = pt A} ≡ refl) → Eckmann-Hilton 0 p q ≡ sym (Eckmann-Hilton 0 q p)
-- syll n p q z l =
--  {- {!z = i0 ⊢ Eckmann-Hilton 0 (λ i i₁ → p i i₁) (λ i i₁ → q i i₁) l
-- z = i1 ⊢ sym (Eckmann-Hilton 0 (λ i i₁ → q i i₁) (λ i i₁ → p i i₁))
--          l
-- l = i0 ⊢ (λ i i₁ → p i i₁) ∙ (λ i i₁ → q i i₁)
-- l = i1 ⊢ (λ i i₁ → q i i₁) ∙ (λ i i₁ → p i i₁)!} -}
--   hcomp (λ k → λ { (z = i0) → {!refl!}
--                   ; (z = i1) → {!!} 
--                   ; (l = i0) → {!!}
--                   ; (l = i1) → {!!}})
--         {!!}

-- Eckmann-Hilton' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) {z : pt A ≡ pt A} → (l p q : refl {x = pt A} ≡ z) → q ∙ sym p ≡ l ∙∙ (sym p ∙ q) ∙∙ sym l
-- Eckmann-Hilton' {A = A} n =
--   J (λ z l → (p q : _) → q ∙ sym p ≡ (l ∙∙ sym p ∙ q ∙∙ sym l))
--     λ p q → Eckmann-Hilton {A = A} 0 q (sym p) ∙ rUnit _

-- Eckmann-Hilton'' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) {z : pt A ≡ pt A} (p q l : refl {x = pt A} ≡ z)
--   → cong (λ x → x) (Eckmann-Hilton' n l p q) ≡ ({!!} ∙∙ sym (Eckmann-Hilton' n l q p) ∙∙ {!!})
-- Eckmann-Hilton'' = {!!}


-- {-
-- dapath : ∀ {ℓ} {A : Type ℓ}{x : A} (p : x ≡ x) → PathP (λ i → p ≡ (sym (lUnit p) ∙ rUnit p) i) (lUnit p) (rUnit p)
-- dapath = {!!}

-- EH : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
-- EH {A = A} n α β i j =
--   hcomp (λ k → λ {(i = i0) → (cong (λ x → rUnit x (~ k)) α ∙ cong (λ x → lUnit x (~ k)) β) j
--                  ; (i = i1) → (cong (λ x → lUnit x (~ k)) β ∙ cong (λ x → rUnit x (~ k)) α) j
--                  ; (j = i0) → rUnit (λ i₁ → snd ((Ω^ n) A)) (~ k)
--                  ; (j = i1) → rUnit (λ i₁ → snd ((Ω^ n) A)) (~ k)})
--         (((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)) j)

-- test : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (p q : typ ((Ω^ (2 + n)) A))  → EH n p q ≡ sym (EH n q p)
-- test {A = A} n p q k i j =
--   hcomp (λ r → λ { (i = i0) → ((λ z → dapath (p z) (~ k) (~ r)) ∙ λ z → dapath (q z) k (~ r)) j
--                   ; (i = i1) → ((λ z → dapath (q z) k (~ r)) ∙ λ z → dapath (p z) (~ k) (~ r)) j
--                   ; (j = i0) → rUnit (λ i₁ → snd ((Ω^ n) A)) (~ r)
--                   ; (j = i1) → rUnit (λ i₁ → snd ((Ω^ n) A)) (~ r)})
--         (hcomp (λ r → λ { (k = i0) → {!!}
--                          ; (k = i1) → {!!}
--                          ; (i = i0) → ({!sym p!} ∙ {!!}) j
--                          ; (i = i1) → {!!}
--                          ; (j = i0) → {!!}
--                          ; (j = i1) → {!!}})
--                {!!})
--   where
--   c : Cube (λ i j → ((λ j → p (j ∧ ~ i) ∙ q (j ∧ i)) ∙ λ j → p (~ i ∨ j) ∙ q (i ∨ j)) j)
--            (λ i j → ((λ j → q (j ∧ i) ∙ p (j ∧ ~ i)) ∙ λ j → q (i ∨ j) ∙ p (~ i ∨ j)) j)
--            {!!} {!!}
--            refl refl
--   c = {!!}

-- {-
-- k = i0 ⊢ EH n p q i j
-- k = i1 ⊢ sym (EH n q p) i j
-- i = i0 ⊢ (p ∙ q) j
-- i = i1 ⊢ (q ∙ p) j
-- j = i0 ⊢ snd (Ω ((Ω^ n) A))
-- j = i1 ⊢ snd (Ω ((Ω^ n) A))
-- -}

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
Eckmann-Hilton {A = A} n α β =
  transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
                 ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)
             λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)
             


-- Eckmann-Hilton- : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (p q : typ ((Ω^ (2 + n)) A)) → q ∙ p ≡ p ∙ q
-- Eckmann-Hilton- n β α =
--   transport (λ i → cong (λ x → lUnit x (~ i)) α ∙ cong (λ x → rUnit x (~ i)) β
--                  ≡ cong (λ x → rUnit x (~ i)) β ∙ cong (λ x → lUnit x (~ i)) α)
--              λ i → (λ j → β (j ∧ i) ∙ α (j ∧ ~ i)) ∙ λ j → β (i ∨ j) ∙ α (~ i ∨ j)

-- test' : ∀ {ℓ} {A : Type ℓ} {x y :A} → (p : x ≡ y) → PathP (λ i → p ≡ {!!}) (lUnit p) (rUnit p)
-- test' = {!!}


-- test : ∀ {ℓ }  {A : Pointed ℓ} (n : ℕ) → (p q : typ ((Ω^ (3 + n)) A)) → Eckmann-Hilton- (suc n) q p ≡ Eckmann-Hilton (suc n) p q
-- test n α β = {!!}
--   where
--   tpart₁ = transport (λ i → cong (λ x → lUnit x (~ i)) α ∙ cong (λ x → rUnit x (~ i)) β
--                           ≡ cong (λ x → rUnit x (~ i)) β ∙ cong (λ x → lUnit x (~ i)) α)

--   tpart₂ = transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
--                           ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)

--   tpart₃ = transport (λ i → cong (λ x → rUnit x i) α ∙ cong (λ x → lUnit x i) β
--                           ≡ cong (λ x → lUnit x i) β ∙ cong (λ x → rUnit x i) α)

--   t₁ = λ i → (λ j → β (j ∧ i) ∙ α (j ∧ ~ i)) ∙ λ j → β (i ∨ j) ∙ α (~ i ∨ j)
--   t₂ =(λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))

--   t2 = tpart₁ t₁
--   t2' = tpart₂ t₂

--   t3 : t₁ ≡ {!!} -- ({!!} ∙∙ t₂ ∙∙ {!!} ∙∙ {!!} ∙∙ {!!})
--   t3 =
--     rUnit _
--     ∙∙ (λ k → (λ i → (λ j → refl ∙ α (j ∧ ~ (k ∧ i))) ∙ (λ j → β j ∙ α (~ (k ∧ i) ∨ j)))
--             ∙∙ (λ i → (λ j → β (j ∧ i) ∙ α ((j ∧ ~ i) ∧ ~ k)) ∙ λ j → β (i ∨ j) ∙ α ((~ i ∧ ~ k) ∨ j))
--             ∙∙ refl)
--     ∙∙ (λ k → (λ i → (λ j → refl ∙ α (j ∧ ~ i)) ∙ (λ j → β j ∙ α (j ∨ ~ i)))
--             ∙∙ (λ i → (λ j → β (j ∧ (i ∧ ~ k)) ∙ refl) ∙ λ j → β ((i ∧ ~ k) ∨ j) ∙ α j)
--             ∙∙  λ i → (λ j → β ((~ k ∨ i) ∧ j) ∙ refl) ∙ λ j → β (~ k ∨ j ∨ i) ∙ α j)
--     ∙∙ (λ _ → (λ i → (λ j → refl ∙ α (j ∧ ~ i)) ∙ (λ j → β j ∙ α (j ∨ ~ i)))
--             ∙∙ refl
--             ∙∙ λ i → (λ j → β (i ∧ j) ∙ refl) ∙ λ j → β (i ∨ j) ∙ α j)
--     ∙∙ refl -- (λ k → {!!} ∙∙ {!!} ∙∙ {!!})
--     {-
--     ∙∙ {!!}
--     ∙∙ {!!}
-- -}
--   t4 : transport (λ i → cong (λ x → lUnit x (~ i)) α ∙ cong (λ x → rUnit x (~ i)) β ≡ {!(λ j → refl ∙ refl) ∙ (λ j → β j ∙ α j)!}) (λ i → (λ j → refl ∙ α (j ∧ ~ i)) ∙ (λ j → β j ∙ α (j ∨ ~ i))) ≡ {!!}
--   t4 = {!t3 i!}
--     ∙∙ {!!}
--     ∙∙ {!!}


-- test'' : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl)
--        → transport (λ i → cong (λ x → rUnit x (~ i)) α ≡ {!!}) {!!} ≡ {!!}
-- test'' = {!!}


-- -- test2 : {!Eckmann-Hilton  p q ∙ Eckmann-Hilton n q p!}
-- -- test2 = {!!}

-- -- EH-bottom : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : typ ((Ω^ (2 + n)) A))
-- --          → cong (_∙ refl) p ∙ cong (refl ∙_) q
-- --           ≡ cong (refl ∙_) q ∙ cong (_∙ refl) p
-- -- EH-bottom n p q i =
-- --   (λ j → p (j ∧ ~ i) ∙ q (j ∧ i)) ∙ λ j → p (~ i ∨ j) ∙ q (i ∨ j)
-- -- symtest : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : typ ((Ω^ (2 + n)) A)) → Eckmann-Hilton n p q ≡ Eckmann-Hilton n p q
-- -- symtest n p q z =
-- --   transport (λ i → cong (λ x → rUnit x (~ i)) p ∙ cong (λ x → lUnit x (~ i)) q
-- --                  ≡ cong (λ x → lUnit x (~ i)) q ∙ cong (λ x → rUnit x (~ i)) p)
-- --             {!sym (EH-bottom n q p) !}

-- -- transportLem : ∀ {ℓ} {A : Type ℓ} {x L₁ R₁ : A} {p1 p2 : x ≡ x} (p : p1 ≡ p2) (Pl-l : x ≡ L₁) (Pl-r : x ≡ R₁) {PL? : L₁ ≡ R₁}{PR? : L₁ ≡ R₁} (PPl : PathP (λ i → Pl-l i ≡ Pl-r i) p1 PL?) (PPr : PathP (λ i → Pl-l i ≡ Pl-r i) p2 PR?) 
-- --              → sym (transport (λ i → PPl i ≡ PPr i) p) ≡ transport (λ i → PPr i ≡ PPl i) (sym p)
-- -- transportLem {x = x} {L₁ = L} {R₁ = R} {p1 = p1} {p2 = p2} p Pl-l Pl-r PPl PPr = refl


-- -- EH-test :  ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : typ ((Ω^ (2 + n)) A)) → sym (Eckmann-Hilton n p q) ≡ _
-- -- EH-test n α β = transportLem (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)) _ _
-- --                              (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β)
-- --                              λ i → cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α



-- -- EH-bottom2 : ∀ {ℓ} {A : Pointed ℓ} (p q : typ ((Ω^ 2) A))
-- --          → p ∙ q
-- --           ≡ q ∙ p
-- -- EH-bottom2 p q i = {!!} ∙ λ j z → compPath-filler (p (~ i ∨ j)) (q (i ∨ j)) (~ i) {!~ z!}

-- -- Eckmann-Hilton'' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
-- -- Eckmann-Hilton'' {A = A} n p q = {!(λ j → compPath-filler (p (j ∧ ~ i)) (q (j ∧ i)))!} ∙∙ (λ i → {!!} ∙ λ j z → compPath-filler (p (~ i ∨ j)) (q (i ∨ j)) {!z ∨ (~ i)!} (i ∧ ~ j)) ∙∙ {!!}

-- -- Eckmann-Hilton' : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
-- -- Eckmann-Hilton' {A = A} n α β =
-- --      rUnit (α ∙ β)
-- --   ∙∙ ((λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → rUnit (α j) i) ∙ (λ j → lUnit (β j) i)
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ i))
-- --   ∙∙ (λ i → rUnit (α i0)
-- --          ∙∙ ((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
-- --          ∙∙ sym (rUnit (α i1)))
-- --   ∙∙ (λ i → (λ j → compPath-filler refl refl (j ∧ ~ i))
-- --           ∙∙ (λ j → lUnit (β j) (~ i)) ∙ (λ j → rUnit (α j) (~ i))
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ ~ i)))
-- --   ∙∙ sym (rUnit (β ∙ α))


-- -- Eckmann-Hilton-sym : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (α β : typ (Ω ((Ω^ (suc n)) A))) → β ∙ α ≡ α ∙ β
-- -- Eckmann-Hilton-sym {A = A} n β α =
-- --      rUnit (α ∙ β)
-- --   ∙∙ ((λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → lUnit (α j) i) ∙ (λ j → rUnit (β j) i)
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ i))
-- --   ∙∙ ((λ i → rUnit refl
-- --          ∙∙ ((λ j → β (j ∧ i) ∙ α (j ∧ ~ i)) ∙ λ j → β (i ∨ j) ∙ α (~ i ∨ j))
-- --          ∙∙ sym (rUnit refl)))
-- --   ∙∙ (λ i → (λ j → compPath-filler refl refl (j ∧ ~ i))
-- --           ∙∙ (λ j → rUnit (β j) (~ i)) ∙ (λ j → lUnit (α j) (~ i))
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ ~ i)))
-- --   ∙∙ sym (rUnit (β ∙ α))


-- -- syll : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → (α β : typ (Ω ((Ω^ (suc n)) A))) → Eckmann-Hilton' n α β ≡ Eckmann-Hilton-sym n β α
-- -- syll {A = A} n α β i = rUnit (α ∙ β) ∙∙ helpre i ∙∙ sym (rUnit (β ∙ α))
-- --   where
-- --   Lp₁ : (α β : _) → _ ≡ _
-- --   Lp₁ α β = (((λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → rUnit (α j) i) ∙ (λ j → lUnit (β j) i)
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ i))))

-- --   Lp₂ : (α β : _) → _ ≡ _
-- --   Lp₂ α β = (λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → lUnit (α j) i) ∙ (λ j → rUnit (β j) i)
-- --           ∙∙ λ j → compPath-filler refl refl (~ j ∧ i))

-- --   P : (α β : _) → ((compPath-filler refl refl)
-- --        ∙∙ (λ j → refl ∙ α j) ∙ (λ j → β j ∙ refl) ∙∙
-- --        (sym (compPath-filler refl refl)))
-- --     ≡ ((compPath-filler refl refl)
-- --        ∙∙ (λ j → α j ∙ refl) ∙ (λ j → refl ∙ β j) ∙∙
-- --        (sym (compPath-filler refl refl)))
-- --   P α β = (λ i → (λ j → compPath-filler refl refl (j ∧ ~ i))
-- --           ∙∙ (λ j → lUnit (α j) (~ i)) ∙ (λ j → rUnit (β j) (~ i))
-- --           ∙∙ (λ j → compPath-filler refl refl (~ j ∧ ~ i)))
-- --     ∙ (λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → rUnit (α j) i) ∙ (λ j → lUnit (β j) i)
-- --           ∙∙ (λ j → compPath-filler refl refl (~ j ∧ i)))

-- --   Test : Lp₁ α β ≡ Lp₂ α β ∙ P α β
-- --   Test = {!!}

-- --   cor : (α β : _) → Lp₂ α β ≡ Lp₁ α β ∙ sym (P α β)
-- --   cor = {!!}


-- --   helpre : (Lp₁ α β
-- --      ∙∙ (λ i → rUnit (α i0)
-- --             ∙∙ ((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
-- --             ∙∙ sym (rUnit (α i1)))
-- --      ∙∙ sym (Lp₂ β α))
-- --         ≡ ((Lp₂ α β
-- --      ∙∙ ((λ i → rUnit refl
-- --             ∙∙ ((λ j → β (j ∧ i) ∙ α (j ∧ ~ i)) ∙ λ j → β (i ∨ j) ∙ α (~ i ∨ j))
-- --             ∙∙ sym (rUnit refl)))
-- --      ∙∙ sym (Lp₁ β α)))
-- --   helpre =
-- --        (λ k → (Test k
-- --      ∙∙ (λ i → rUnit (α i0)
-- --             ∙∙ ((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))
-- --             ∙∙ sym (rUnit (α i1)))
-- --      ∙∙ sym (cor β α k)))
-- --     ∙∙ (λ k → ((Lp₂ α β
-- --               ∙ {!(λ i → (λ j → compPath-filler refl refl (j ∧ i))
-- --           ∙∙ (λ j → rUnit (α j) i) ∙ (λ j → lUnit (β j) i)
-- --           ∙∙ (λ j → compPath-filler refl refl (~ j ∧ i)))!}
-- --                ∙ (λ i → (λ j → compPath-filler {!!} {!!} (j ∧ i))
-- --                       ∙∙ (λ j → {!compPath-filler (α j) (β (i ∧ k)) (j k)!}) ∙ {!!}
-- --                       ∙∙ (λ j → compPath-filler {!!} {!!} (~ j ∧ i))))
-- --      ∙∙ (λ i → (λ j → lUnit (β (k ∧ j)) j)
-- --             ∙∙ (((λ j → α (j ∧ ~ i) ∙ β ((j ∧ i) ∨ k)) ∙ λ j → α (~ i ∨ j) ∙ β ((i ∨ k) ∨ j)))
-- --             ∙∙ sym (rUnit refl))
-- --      ∙∙ (sym (Lp₁ β α ∙ {!!}))))
-- --     ∙∙ {!!}

-- --   {-
-- -- i = i0 ⊢ (rUnit (λ _ → snd ((Ω^ n) A)) ∙∙
-- --           (λ j₁ → snd (Ω ((Ω^ n) A)) ∙ β j₁) ∙
-- --           (λ j₁ → α j₁ ∙ snd (Ω ((Ω^ n) A)))
-- --           ∙∙ (λ i₁ → rUnit (λ _ → snd ((Ω^ n) A)) (~ i₁)))
-- --          j
-- -- i = i1 ⊢ (β ∙ α) j
-- -- j = i0 ⊢ λ _ → snd ((Ω^ n) A)
-- -- j = i1 ⊢ λ _ → snd ((Ω^ n) A)
-- -- -}

isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                     → isOfHLevel (suc n) (typ A)
                     → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
    ((λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
 ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
 ∙∙ (λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , fun e (pt A))
ptdIso→comm {A = (A , a)} {B = B} e comm p q =
       sym (rightInv (congIso e) (p ∙ q))
    ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                            ∙∙ (comm (inv (congIso e) p) (inv (congIso e) q))
                            ∙∙ (sym (invCongFunct e q p))))
    ∙∙ rightInv (congIso e) (q ∙ p)

{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₂
      → ∥ typ ((Ω^ (suc n)) A) ∥₂ → ∥ typ ((Ω^ (suc n)) A) ∥₂
π-comp n = elim2 (λ _ _ → setTruncIsSet) λ p q → ∣ p ∙ q ∣₂

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
                → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π  n = elim2 (λ x y → isOfHLevelPath 2 setTruncIsSet _ _)
                             λ p q → cong ∣_∣₂ (Eckmann-Hilton n p q)


{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Bool
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

--- Some silly lemmas on S1 ---

S¹≡S1 : S₊ 1 ≡ S¹
S¹≡S1 = cong Susp (sym (ua Bool≃Susp⊥)) ∙ sym S¹≡SuspBool

isOfHLevelS1 : isOfHLevel 3 (S₊ 1)
isOfHLevelS1 = transport (λ i → isOfHLevel 3 (S¹≡S1 (~ i)))
                          λ x y → J (λ y p → (q : x ≡ y) → isProp (p ≡ q))
                                     (transport (λ i → isSet (basedΩS¹≡Int x (~ i))) isSetInt refl)

SuspBool→S1 : Susp Bool → S₊ 1
SuspBool→S1 north = north
SuspBool→S1 south = south
SuspBool→S1 (merid false i) = merid south i
SuspBool→S1 (merid true i) = merid north i

S1→SuspBool : S₊ 1 → Susp Bool
S1→SuspBool north = north
S1→SuspBool south = south
S1→SuspBool (merid north i) = merid true i
S1→SuspBool (merid south i) = merid false i

SuspBool≃S1 : Susp Bool ≃ S₊ 1
SuspBool≃S1 = isoToEquiv iso1
  where
  iso1 : Iso (Susp Bool) (S₊ 1)
  Iso.fun iso1 = SuspBool→S1
  Iso.inv iso1 = S1→SuspBool
  Iso.rightInv iso1 north = refl
  Iso.rightInv iso1 south = refl
  Iso.rightInv iso1 (merid north i) = refl
  Iso.rightInv iso1 (merid south i) = refl
  Iso.leftInv iso1 north = refl
  Iso.leftInv iso1 south = refl
  Iso.leftInv iso1 (merid false i) = refl
  Iso.leftInv iso1 (merid true i) = refl


-- map between S₊
private
  f' : {a : A} → A → S₊ 1 → Susp A
  f' {a = pt} A north = north
  f' {a = pt} A south = north
  f' {a = pt} a (merid p i) = ((merid a) ∙ sym (merid pt)) i

  proj' : {A : Pointed ℓ} {B : Pointed ℓ'} → typ A → typ B → A ⋀ B
  proj' a b = inr (a , b)

module smashS1→susp {(A , pt) : Pointed ℓ} where
  fun : (S₊ 1 , north) ⋀ (A , pt) → (Susp A)
  fun (inl tt) = north
  fun (inr (x , x₁)) = f' {a = pt} x₁ x
  fun  (push (inl north) i) = north
  fun (push (inl south) i) = north
  fun (push (inl (merid a i₁)) i) = rCancel (merid pt) (~ i) i₁
  fun (push (inr x) i) = north
  fun (push (push tt i₁) i) = north

  fun⁻ : Susp A → (S₊ 1 , north) ⋀ (A , pt)
  fun⁻ north = inl tt
  fun⁻ south = inl tt
  fun⁻ (merid a i) =
    (push (inr a) ∙∙ cong (λ x → proj' {A = S₊ 1 , north} {B = A , pt} x a) (merid south ∙ sym (merid north)) ∙∙ sym (push (inr a))) i

sphereSmashMap : (n m : ℕ) → (S₊ (suc n) , north) ⋀ (S₊ (suc m) , north) → S₊ (2 + n + m)
sphereSmashMap zero m = smashS1→susp.fun
sphereSmashMap (suc n) m =
  smashS1→susp.fun ∘
  (idfun∙ _ ⋀⃗ (sphereSmashMap n m , refl)) ∘
  ⋀-associate ∘
  ((smashS1→susp.fun⁻ , refl) ⋀⃗ idfun∙ _)

private
  f* : {a : A} → S¹ → A → Susp A
  f* base b = north
  f* {a = a} (loop i) = funExt (λ x → merid x ∙ sym (merid a)) i

  f'' : {a : A} → Susp Bool → A → Susp A
  f'' north a = north
  f'' south a = north
  f'' {a = a} (merid p i) = funExt (λ x → merid x ∙ sym (merid a)) i


proj'' : {A : Pointed ℓ} {B : Pointed ℓ'} → typ A → typ B → A ⋀ B
proj'' a b = inr (a , b)

projᵣ : {A : Pointed ℓ} {B : Pointed ℓ'} (a : typ A) → proj'' {A = A} a (pt B) ≡ inl tt
projᵣ a = sym (push (inl a))

projₗ : {A : Pointed ℓ} {B : Pointed ℓ'} (b : typ B) → proj'' {B = B} (pt A) b ≡ inl tt
projₗ b = sym (push (inr b))

projᵣₗ : {A : Pointed ℓ} {B : Pointed ℓ'} → projᵣ (pt A) ≡ projₗ (pt B)
projᵣₗ {A = A} {B = B} i j = push (push tt i) (~ j) --  cong sym (cong push (push tt))


compLrFiller : {a b c d : A} (p : a ≡ b) (q : b ≡ c) (s : c ≡ d) → PathP (λ i → p i ≡ s (~ i)) (p ∙ q ∙ s) q
compLrFiller {A = A} {a = a} {b = b} {c = c} {d = d} p q s i j = filler j i1 i
  where
  rhs-filler : I → I → I → A
  rhs-filler i j z = hfill (λ k → λ {(i = i0) → b ;
                                      (i = i1) → s (~ z ∧ k) ;
                                      (z = i1) → q i})
                           (inS (q i)) j
  filler : I → I → I → A
  filler i j z = hfill (λ k → λ {(i = i0) → p z ;
                                  (i = i1) → rhs-filler k i1 z ;
                                  (z = i1) → q (k ∧ i)})
                       (inS (p (i ∨ z)))
                       j


-- module S1-smash-Iso ((A , pt) : Pointed ℓ) where

--   funInv : Susp A → (S¹ , base) ⋀ (A , pt)
--   funInv north = inl tt
--   funInv south = inl tt
--   funInv (merid a i) = (sym (projₗ a) ∙
--                        cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop ∙
--                        projₗ a) i



--   fun : (S¹ , base) ⋀ (A , pt) → (Susp A)
--   fun (inl tt) = north
--   fun (inr (x , x₁)) = f* {a = pt} x x₁
--   fun (push (inl base) i) = north
--   fun (push (inl (loop i₁)) i) = rCancel (merid pt) (~ i) i₁ -- rCancel (merid pt) (~ i) i₁
--   fun (push (inr x) i) = north
--   fun (push (push a i₁) i) = north

--   funSect : (x : Susp A) → fun (funInv x) ≡ x
--   funSect north = refl
--   funSect south = merid pt
--   funSect (merid a i) = hcomp (λ k → λ {(i = i0) → ((λ j → rCancel refl j ∙ refl ∙ refl) ∙
--                                                      λ j → lUnit (lUnit refl (~ j)) (~ j)) k ;
--                                         (i = i1) → ((λ j → lUnit refl (~ j) ∙ sym (lUnit (rUnit (merid a ∙ sym (merid pt)) (~ j)) (~ j)) ∙ merid a) ∙
--                                                      (λ j → lUnit (symDistr (merid a) (sym (merid pt)) j ∙ merid a) (~ j)) ∙
--                                                      (sym (assoc (merid pt) (sym (merid a)) (merid a))) ∙
--                                                      (λ j → merid pt ∙ lCancel (merid a) j) ∙
--                                                      sym (rUnit (merid pt)) ) k})
--                                                                 (helper2 i ∙ filler i)
--     where

--     filler : (i : I) → (refl ∙ (merid a ∙ sym (merid pt)) ∙ refl) i ≡ merid a i
--     filler i = (λ j → (refl ∙ (merid a ∙ sym (merid pt)) ∙ refl) (i ∧ (~ j))) ∙ λ j → merid a (j ∧ i)

--     helper2 : (i : I) → fun ((sym (projₗ a) ∙
--                               cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop ∙
--                               projₗ a) i)
--                       ≡ ((λ i → fun (sym (projₗ a) i)) ∙
--                          (λ i → fun (cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop i)) ∙
--                          λ i → fun (projₗ a i)) i
--     helper2 i = (λ j → congFunct fun (sym (projₗ a)) (cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop ∙ projₗ a) j i) ∙
--                 (λ j → (cong fun (sym (projₗ a)) ∙ congFunct fun (cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop) (projₗ a) j) i)

--   retrHelper : (x : S¹) (a : A) → funInv (f* {a = pt} x a) ≡ proj'' x a
--   retrHelper base a = sym (projₗ a)
--   retrHelper (loop i) a j = hcomp (λ k → λ { (i = i0) → push (inr a) j
--                                             ; (i = i1) → push (inr a) j
--                                             ; (j = i0) → id3 (~ k) i
--                                             ; (j = i1) → proj'' (loop i) a})
--                                   (compLrFiller (push (inr a)) (λ i → proj'' (loop i) a) (sym (push (inr a))) j i)

--     module _ where

--     invCancelHelper : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q : y ≡ y) → (p ∙ q ∙ sym p) ∙ p ∙ sym q ≡ p
--     invCancelHelper p q = (p ∙ q ∙ sym p) ∙ p ∙ sym q ≡⟨ (λ i → assoc p q (sym p) i ∙ p ∙ sym q) ⟩
--                           ((p ∙ q) ∙ sym p) ∙ p ∙ sym q ≡⟨ assoc ((p ∙ q) ∙ sym p) p (sym q) ⟩
--                           (((p ∙ q) ∙ sym p) ∙ p) ∙ sym q ≡⟨ (λ i → assoc (p ∙ q) (sym p) p (~ i) ∙ sym q) ⟩
--                           ((p ∙ q) ∙ sym p ∙ p) ∙ sym q ≡⟨ (λ i → ((p ∙ q) ∙ lCancel p i) ∙ sym q) ⟩
--                           ((p ∙ q) ∙ refl) ∙ sym q ≡⟨ (λ i → rUnit (p ∙ q) (~ i) ∙ sym q) ⟩
--                           (p ∙ q) ∙ sym q ≡⟨ sym (assoc p q (sym q)) ⟩
--                           p ∙ q ∙ sym q ≡⟨ (λ i → p ∙ rCancel q i) ⟩
--                           p ∙ refl ≡⟨ sym (rUnit p) ⟩
--                           p ∎

--     filler : funInv (f* {a = pt} (loop i) a) ≡ proj'' (loop i) a
--     filler = (λ j → funInv (funExt (λ x → merid x ∙ sym (merid pt)) (i ∨ j) a)) ∙ sym (projₗ a) ∙ λ j → proj'' (loop (i ∨ (~ j))) a

--     id1 : sym (projᵣ base) ∙ cong ((λ x → proj'' {A = S¹ , base} {B = A , pt} x pt)) loop ∙ projᵣ base ≡ refl
--     id1 = (λ i → (push (inl (loop i))) ∙ (λ j → inr (loop (i ∨ j) , pt)) ∙ sym (push (inl base))) ∙
--           (λ i → push (inl base) ∙ lUnit (sym (push (inl base))) (~ i)) ∙
--           rCancel (push (inl base))

--     id2 : cong funInv (sym (merid pt)) ≡ (λ _ → inl tt)
--     id2 = (λ i j → (sym (projₗ pt) ∙ (cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x pt) loop) ∙ projₗ pt) (~ j)) ∙
--           (λ i j → (sym ((projᵣₗ (~ i))) ∙ cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x pt) loop ∙ projᵣₗ (~ i)) (~ j)) ∙
--           (λ i j → id1 i (~ j))

--     id3 : (λ i → funInv (f* {a = pt} (loop i) a)) ≡ ((sym (projₗ a) ∙ cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a)))
--     id3 = (λ j i → congFunct funInv (merid a) (sym (merid pt)) j i ) ∙
--           (λ j i → (cong funInv (merid a) ∙ id2 j) i) ∙
--           (λ j i → rUnit (cong funInv (merid a)) (~ j) i)



--     test5 : ((sym (projₗ a) ∙ cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a))) ≡ λ j → funInv (merid a j)
--     test5 = refl

--   test6 : (ia ib : I) → (x : S¹) → retrHelper (loop ia) pt ≡ {!? ∙ sym (cong (projₗ) loop) ∙ ?!}
--   test6 = {!!}
--     where
--     test7 : ((sym (projₗ pt) ∙ cong (λ x → proj'' {A = S¹ , base} {B = A , pt} x pt) loop ∙ (projₗ pt))) ≡ refl
--     test7 = (λ i j → funInv (merid pt j)) ∙ λ i → {!!}
-- {-
--   test2 : (i : I) → (retrHelper (loop i) pt) ≡ (λ j → funInv (rCancel (merid pt) j i)) ∙ sym (projᵣ (loop i))
--   test2 i = (λ z → hfill ((λ k → λ { (i = i0) → ((λ j → id3 i pt j ∙ sym (projₗ pt) ∙ λ j → proj'' (loop (~ j)) pt) ∙ invCancelHelper i pt _ _) k
--                                     ; (i = i1) → lUnit (rUnit (sym (projₗ pt)) (~ k)) (~ k) }))
--                          (inS ((λ j → funInv (funExt (λ x → merid x ∙ sym (merid pt)) (i ∨ j) pt)) ∙ sym (projₗ pt) ∙ λ j → proj'' (loop (i ∨ (~ j))) pt)) (~ z)) ∙
--             (λ z → (λ j → funInv (funExt (λ x → merid x ∙ sym (merid pt)) (i ∨ j) pt)) ∙ sym (projₗ pt) ∙ λ j → proj'' (loop (i ∨ (~ j))) pt) ∙
--             (λ z → (λ j → funInv {!funExt (λ x → merid x ∙ sym (merid pt)) (i ∨ j) pt -- rCancel (merid pt) z (i ∨ j)!}) ∙ {!!} ∙ {!!}) ∙
--             {!!}
--  -}
--   isoHelperPre : (x : S¹ × A) (v : (S¹ , base) ⋁ (A , pt)) → {!!}
--   isoHelperPre = {!!}

--   isoHelper : (x : S¹ × A) (v : (S¹ , base) ⋁ (A , pt)) (q :  inr x ≡ inl tt) (i : I) → (funInv (fun (q i)) ≡ q i) ≡ (funInv (fun ((q ∙ push v) i)) ≡ (q ∙ push v) i)
--   isoHelper x v q i j = funInv (fun (test2 j)) ≡ test2 j
--     where
--     test2 : q i ≡ (q ∙ push v) i
--     test2 = (λ j → q (i ∧ (~ j))) ∙ λ j → (q ∙ push v) (i ∧ j)

--   idIsEquiv2 : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
--   idIsEquiv2 = J (λ B p → _ ≃ B) (idEquiv _)

--   helper2 : (x : S¹ × A) → funInv (fun (inr x)) ≡ inr x
--   helper2 (x , x₁) = retrHelper x x₁
--   funRetr2 : (x : (S¹ , base) ⋀ (A , pt)) → funInv (fun x) ≡ x
--   funRetr2 (inl tt) = {!!}
--   funRetr2 (inr x) = {!!}
--   funRetr2 (push a i) = ElimR.elimL (λ b path → funInv (fun (path (~ i))) ≡ path (~ i)) (λ b path → funInv (fun ((path) (~ i))) ≡ (path)  (~ i))
--                                     (helper2 (refl i)) -- (helper2 (refl i))
--                                     (λ z q → idIsEquiv2 {!!})-- isoToEquiv (isoHelper _ a q (~ i)))
--                                     tt (sym (push a))
--     where
--     test3 : (a₁ : (S¹ , base) ⋁ (A , pt)) → (q : inr (i∧ a) ≡ inl tt) → Iso ((funInv (fun (q (~ i)))) ≡ q (~ i)) (funInv (fun ((q ∙ push a₁) (~ i))) ≡ (q ∙ push a₁) (~ i))
--     test3 (inl x) q = {!!}
--     test3 (inr x) q = {!!}
--     test3 (push a i) q = {!!}

--     test2 : (x : S¹ × A) (v : (S¹ , base) ⋁ (A , pt)) (q :  Path ((S¹ , base) ⋀ (A , pt)) (inr x) (inl tt)) →  q (~ i) ≡ (q ∙ push v) (~ i)
--     test2 x v q = (λ j → q ((~ i) ∧ (~ j))) ∙ λ j → (q ∙ push v) ((~ i) ∧ j)

--   funRetr : (x : (S¹ , base) ⋀ (A , pt)) → funInv (fun x) ≡ x
--   funRetr (inl tt) = refl
--   funRetr (inr (x , a)) = retrHelper x a
--   funRetr (push (inl base) i) j = hcomp (λ k → λ { (i = i0) → inl tt
--                                                   ; (i = i1) → sym (projᵣₗ k) j
--                                                   ; (j = i0) → inl tt
--                                                   ; (j = i1) → projᵣ base (~ i)})
--                                         (projᵣ base ((~ j) ∨ (~ i)))
--   funRetr (push (inl (loop z)) i) j = {!(projᵣ base (~ j ∨ ~ i))!}
--   {- hcomp (λ k → λ {(i₁ = i0) → ((λ l → hcomp (λ r → λ {(i = i0) → (rCancel (λ _ → inl tt)) r
--                                                                                            ; (i = i1) → (lUnit ((λ j → push (inl base) (i ∧ j))) (~ l)) })
--                                                                                  (lUnit ((λ j → push (inl base) (i ∧ j))) (~ i)))) k
--                                                     ; (i₁ = i1) → ((λ l → hcomp (λ r → λ {(i = i0) → (rCancel (λ _ → inl tt)) r
--                                                                                            ; (i = i1) → (lUnit ((λ j → push (inl base) (i ∧ j))) (~ l)) })
--                                                                                  (lUnit ((λ j → push (inl base) (i ∧ j))) (~ i)))) k
--                                                     ; (i = i0) → ({!!} ∙ {!!} ∙ {!push inl !}) k -- rCancel refl k
--                                                     ; (i = i1) → {!!}})
--                                            ((hcomp (λ k → λ {(i = i0) → (rCancel (λ _ → inl tt)) k
--                                                            ; (i = i1) → _ }) ((λ j → funInv (rCancel (merid pt) (~ i ∨ j) i₁)) ∙
--                                              λ j → push (inl (loop i₁)) (i ∧ j)))) -}
--     where

--     bottom : funInv (rCancel (merid pt) (~ i) z) ≡ push (inl (loop z)) i
--     bottom = (λ j → funInv(rCancel (merid pt) (~ i) (z ∨ j))) ∙ (λ j → push (inl (loop z)) (i ∧ j))

--     i=i1 : (λ j → funInv(rCancel (merid pt) i0 (z ∨ j))) ∙ (λ j → push (inl (loop z)) j) ≡ retrHelper (loop z) pt
--     i=i1 = {!-- rCancel (merid pt) i1!}

--     frontCubeFiller : (i j z : I) → (S¹ , base) ⋀ (A , pt) -- bottom is i j , z is height
--     frontCubeFiller i j z = hfill (λ k → λ { (i = i0) → inl tt
--                                             ; (i = i1) → sym (projᵣₗ k) j
--                                             ; (j = i0) → inl tt
--                                             ; (j = i1) → projᵣ base (~ i)}) (inS (push (inl base) (i ∧ j))) z

--     bottomCubeFiller : (i j z : I) → (S¹ , base) ⋀ (A , pt)
--     bottomCubeFiller i j z = funInv (rCancel (merid pt) (~ i) (z ∧ j))


--     theHComp : (i j z : I) → (S¹ , base) ⋀ (A , pt)
--     theHComp i j z = {!!}




--   funRetr (push (inr x) i) = λ j → (projₗ x ((~ i) ∨ (~ j)))
--   funRetr (push (push tt i₁) i) = {!

-- i₁ = i0 ⊢ hcomp
--           (λ { k (i = i0) → λ _ → inl tt
--              ; k (i = i1) → λ i₂ → projᵣₗ k (~ i₂)
--              })
--           (λ i₂ → projᵣ base (~ i₂ ∨ ~ i))
-- i₁ = i1 ⊢ hcomp
--           (λ { k (i = i0) → λ _ → inl tt
--              ; k (i = i1) → λ i₂ → projᵣₗ k (~ i₂)
--              })
--           (λ i₂ → projᵣ base (~ i₂ ∨ ~ i))
-- i = i0 ⊢ λ _ → inl tt

-- i = i1 ⊢ !}

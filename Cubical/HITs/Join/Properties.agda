{-

This file contains:

- Equivalence with the pushout definition
  Written by: Loïc Pujet, September 2019

- Associativity of the join
  Written by: Loïc Pujet, September 2019

- Ganea's theorem

-}


module Cubical.HITs.Join.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed

open import Cubical.Data.Sigma renaming (fst to proj₁; snd to proj₂)
open import Cubical.Data.Unit

open import Cubical.HITs.Join.Base
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ' : Level

-- the inclusion maps are null-homotopic
join-inl-null : {X : Pointed ℓ} {Y : Pointed ℓ'} (x : typ X)
  → Path (join (typ X) (typ Y)) (inl x) (inl (pt X))
join-inl-null {X = X} {Y} x = push x (pt Y) ∙ sym (push (pt X) (pt Y))

join-inr-null : {X : Pointed ℓ} {Y : Type ℓ'} (y : Y)
  → Path (join (typ X) Y) (inr y) (inl (pt X))
join-inr-null {X = X} y = sym (push (pt X) y)

open Iso

-- Characterisation of function type join A B → C
IsoFunSpaceJoin : ∀ {ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
               → Iso (join A B → C)
                      (Σ[ f ∈ (A → C) ] Σ[ g ∈ (B → C) ]
                        ((a : A) (b : B) → f a ≡ g b))
fun IsoFunSpaceJoin f = (f ∘ inl) , ((f ∘ inr) , (λ a b → cong f (push a b)))
inv IsoFunSpaceJoin (f , g , p) (inl x) = f x
inv IsoFunSpaceJoin (f , g , p) (inr x) = g x
inv IsoFunSpaceJoin (f , g , p) (push a b i) = p a b i
rightInv IsoFunSpaceJoin (f , g , p) = refl
leftInv IsoFunSpaceJoin f =
  funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

-- Alternative definition of the join using a pushout
joinPushout : (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
joinPushout A B = Pushout {A = A × B} proj₁ proj₂

-- Proof that it is equal
joinPushout-iso-join : (A : Type ℓ) → (B : Type ℓ') → Iso (joinPushout A B) (join A B)
joinPushout-iso-join A B = iso joinPushout→join join→joinPushout join→joinPushout→join joinPushout→join→joinPushout
  where
    joinPushout→join : joinPushout A B → join A B
    joinPushout→join (inl x) = inl x
    joinPushout→join (inr x) = inr x
    joinPushout→join (push x i) = push (proj₁ x) (proj₂ x) i

    join→joinPushout : join A B → joinPushout A B
    join→joinPushout (inl x) = inl x
    join→joinPushout (inr x) = inr x
    join→joinPushout (push a b i) = push (a , b) i

    joinPushout→join→joinPushout : ∀ x → join→joinPushout (joinPushout→join x) ≡ x
    joinPushout→join→joinPushout (inl x) = refl
    joinPushout→join→joinPushout (inr x) = refl
    joinPushout→join→joinPushout (push (a , b) j) = refl

    join→joinPushout→join : ∀ x → joinPushout→join (join→joinPushout x) ≡ x
    join→joinPushout→join (inl x) = refl
    join→joinPushout→join (inr x) = refl
    join→joinPushout→join (push a b j) = refl

-- We will need both the equivalence and path version
joinPushout≃join : (A : Type ℓ) → (B : Type ℓ') → joinPushout A B ≃ join A B
joinPushout≃join A B = isoToEquiv (joinPushout-iso-join A B)

joinPushout≡join : (A : Type ℓ) → (B : Type ℓ') → joinPushout A B ≡ join A B
joinPushout≡join A B = isoToPath (joinPushout-iso-join A B)


{-
  Proof of associativity of the join
-}
join-assoc-samelevel : (A B C : Type ℓ) → join (join A B) C ≡ join A (join B C)
join-assoc-samelevel {ℓ} A B C = (joinPushout≡join (join A B) C) ⁻¹
                   ∙ (spanEquivToPushoutPath sp3≃sp4) ⁻¹
                   ∙ (3x3-span.3x3-lemma span) ⁻¹
                   ∙ (spanEquivToPushoutPath sp1≃sp2)
                   ∙ (joinPushout≡join A (join B C))
  where
    -- the meat of the proof is handled by the 3x3 lemma applied to this diagram
    span : 3x3-span
    span = record {
      A00 = A;      A02 = A × B;      A04 = B;
      A20 = A × C;  A22 = A × B × C;  A24 = B × C;
      A40 = A × C;  A42 = A × C;      A44 = C;
      f10 = proj₁;   f12 = proj₁₂; f14 = proj₁;
      f30 = λ x → x; f32 = proj₁₃; f34 = proj₂;
      f01 = proj₁;   f21 = proj₁₃; f41 = λ x → x;
      f03 = proj₂;   f23 = proj₂;  f43 = proj₂;
      H11 = H11;    H13 = H13;    H31 = H31;    H33 = H33  }
      where
        proj₁₃ : A × B × C → A × C
        proj₁₃ (a , (b , c)) = a , c

        proj₁₂ : A × B × C → A × B
        proj₁₂ (a , (b , c)) = a , b

        H11 : (x : A × B × C) → proj₁ (proj₁₂ x) ≡ proj₁ (proj₁₃ x)
        H11 (a , (b , c)) = refl

        H13 : (x : A × B × C) → proj₂ (proj₁₂ x) ≡ proj₁ (proj₂ x)
        H13 (a , (b , c)) = refl

        H31 : (x : A × B × C) → proj₁₃ x ≡ proj₁₃ x
        H31 (a , (b , c)) = refl

        H33 : (x : A × B × C) → proj₂ (proj₁₃ x) ≡ proj₂ (proj₂ x)
        H33 (a , (b , c)) = refl

    -- the first pushout span appearing in the 3x3 lemma
    sp1 : 3-span
    sp1 = record {
      A0 = 3x3-span.A□0 span;
      A2 = 3x3-span.A□2 span;
      A4 = 3x3-span.A□4 span;
      f1 = 3x3-span.f□1 span;
      f3 = 3x3-span.f□3 span }

    -- the first span we are interested in
    sp2 : 3-span
    sp2 = record {
      A0 = A ;
      A2 = A × (join B C) ;
      A4 = join B C ;
      f1 = proj₁ ;
      f3 = proj₂ }

    -- proof that they are in fact equivalent
    sp1≃sp2 : 3-span-equiv sp1 sp2
    sp1≃sp2 = record {
      e0 = A□0≃A;
      e2 = A□2≃A×join;
      e4 = joinPushout≃join B C;
      H1 = H1;
      H3 = H2 }
      where
        A×join : Type ℓ
        A×join = A × (join B C)

        A□2→A×join : 3x3-span.A□2 span → A×join
        A□2→A×join (inl (a , b)) = a , inl b
        A□2→A×join (inr (a , c)) = a , inr c
        A□2→A×join (push (a , (b , c)) i) = a , push b c i

        A×join→A□2 : A×join → 3x3-span.A□2 span
        A×join→A□2 (a , inl b) = inl (a , b)
        A×join→A□2 (a , inr c) = inr (a , c)
        A×join→A□2 (a , push b c i) = push (a , (b , c)) i

        A×join→A□2→A×join : ∀ x → A×join→A□2 (A□2→A×join x) ≡ x
        A×join→A□2→A×join (inl (a , b)) = refl
        A×join→A□2→A×join (inr (a , c)) = refl
        A×join→A□2→A×join (push (a , (b , c)) i) = refl

        A□2→A×join→A□2 : ∀ x → A□2→A×join (A×join→A□2 x) ≡ x
        A□2→A×join→A□2 (a , inl b) = refl
        A□2→A×join→A□2 (a , inr c) = refl
        A□2→A×join→A□2 (a , push b c i) = refl

        A□2≃A×join : 3x3-span.A□2 span ≃ A×join
        A□2≃A×join = isoToEquiv (iso A□2→A×join A×join→A□2 A□2→A×join→A□2 A×join→A□2→A×join)

        A→A□0 : A → 3x3-span.A□0 span
        A→A□0 b = inl b

        A□0→A : 3x3-span.A□0 span → A
        A□0→A (inl b) = b
        A□0→A (inr a) = proj₁ a
        A□0→A (push a i) = proj₁ a

        A→A□0→A : ∀ x → A□0→A (A→A□0 x) ≡ x
        A→A□0→A x = refl

        A□0→A→A□0 : ∀ x → A→A□0 (A□0→A x) ≡ x
        A□0→A→A□0 (inl b) = refl
        A□0→A→A□0 (inr a) j = push a j
        A□0→A→A□0 (push a i) j = push a (j ∧ i)

        A□0≃A :  3x3-span.A□0 span ≃ A
        A□0≃A = isoToEquiv (iso A□0→A A→A□0 A→A□0→A A□0→A→A□0)

        H1 : (x : 3x3-span.A□2 span) → proj₁ (A□2→A×join x) ≡ A□0→A (3x3-span.f□1 span x)
        H1 (inl (a , b)) = refl
        H1 (inr (a , c)) = refl
        H1 (push (a , (b , c)) i) j = A□0→A (doubleCompPath-filler refl (λ i → push (a , c) i) refl j i)

        H2 : (x : 3x3-span.A□2 span) → proj₂ (A□2→A×join x) ≡ fst (joinPushout≃join _ _) (3x3-span.f□3 span x)
        H2 (inl (a , b)) = refl
        H2 (inr (a , c)) = refl
        H2 (push (a , (b , c)) i) j = fst (joinPushout≃join _ _) (doubleCompPath-filler refl (λ i → push (b , c) i) refl j i)

    -- the second span appearing in 3x3 lemma
    sp3 : 3-span
    sp3 = record {
      A0 = 3x3-span.A0□ span;
      A2 = 3x3-span.A2□ span;
      A4 = 3x3-span.A4□ span;
      f1 = 3x3-span.f1□ span;
      f3 = 3x3-span.f3□ span }

    -- the second span we are interested in
    sp4 : 3-span
    sp4 = record {
      A0 = join A B ;
      A2 = (join A B) × C ;
      A4 = C ;
      f1 = proj₁ ;
      f3 = proj₂ }

    -- proof that they are in fact equivalent
    sp3≃sp4 : 3-span-equiv sp3 sp4
    sp3≃sp4 = record {
      e0 = joinPushout≃join A B;
      e2 = A2□≃join×C;
      e4 = A4□≃C;
      H1 = H4;
      H3 = H3 }
      where
        join×C : Type ℓ
        join×C = (join A B) × C

        A2□→join×C : 3x3-span.A2□ span → join×C
        A2□→join×C (inl (a , c)) = (inl a) , c
        A2□→join×C (inr (b , c)) = (inr b) , c
        A2□→join×C (push (a , (b , c)) i) = push a b i , c

        join×C→A2□ : join×C → 3x3-span.A2□ span
        join×C→A2□ (inl a , c) = inl (a , c)
        join×C→A2□ (inr b , c) = inr (b , c)
        join×C→A2□ (push a b i , c) = push (a , (b , c)) i

        join×C→A2□→join×C : ∀ x → join×C→A2□ (A2□→join×C x) ≡ x
        join×C→A2□→join×C (inl (a , c)) = refl
        join×C→A2□→join×C (inr (b , c)) = refl
        join×C→A2□→join×C (push (a , (b , c)) j) = refl

        A2□→join×C→A2□ : ∀ x → A2□→join×C (join×C→A2□ x) ≡ x
        A2□→join×C→A2□ (inl a , c) = refl
        A2□→join×C→A2□ (inr b , c) = refl
        A2□→join×C→A2□ (push a b i , c) = refl

        A2□≃join×C : 3x3-span.A2□ span ≃ join×C
        A2□≃join×C = isoToEquiv (iso A2□→join×C join×C→A2□ A2□→join×C→A2□ join×C→A2□→join×C)

        C→A4□ : C → 3x3-span.A4□ span
        C→A4□ b = inr b

        A4□→C : 3x3-span.A4□ span → C
        A4□→C (inl x) = proj₂ x
        A4□→C (inr c) = c
        A4□→C (push x i) = proj₂ x

        C→A4□→C : ∀ x → A4□→C (C→A4□ x) ≡ x
        C→A4□→C x = refl

        A4□→C→A4□ : ∀ x → C→A4□ (A4□→C x) ≡ x
        A4□→C→A4□ (inl x) j = push x (~ j)
        A4□→C→A4□ (inr c) = refl
        A4□→C→A4□ (push x i) j = push x (~ j ∨ i)

        A4□≃C :  3x3-span.A4□ span ≃ C
        A4□≃C = isoToEquiv (iso A4□→C C→A4□ C→A4□→C A4□→C→A4□)

        H3 : (x : 3x3-span.A2□ span) → proj₂ (A2□→join×C x) ≡ A4□→C (3x3-span.f3□ span x)
        H3 (inl (a , c)) = refl
        H3 (inr (b , c)) = refl
        H3 (push (a , (b , c)) i) j = A4□→C (doubleCompPath-filler refl (λ i → push (a , c) i) refl j i)

        H4 : (x : 3x3-span.A2□ span) → proj₁ (A2□→join×C x) ≡ fst (joinPushout≃join _ _) (3x3-span.f1□ span x)
        H4 (inl (a , c)) = refl
        H4 (inr (b , c)) = refl
        H4 (push (a , (b , c)) i) j = fst (joinPushout≃join _ _) (doubleCompPath-filler refl (λ i → push (a , b) i) refl j i)

join-assoc : ∀ {ℓ''} (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') → join (join A B) C ≡ join A (join B C)
join-assoc {ℓ} {ℓ'} {ℓ''} A B C =
  LiftExt {ℓ' = ℓ-max (ℓ-max ℓ ℓ') ℓ''} (join-lift ⁻¹
                                        ∙ cong₂ join join-lift refl ⁻¹
                                        ∙ join-assoc-samelevel (Lift A) (Lift B) (Lift C)
                                        ∙ cong₂ join refl join-lift
                                        ∙ join-lift)
  where
    join-lift : ∀ {ℓ ℓ' ℓ-out} {A : Type ℓ} {B : Type ℓ'} →
      join (Lift {j = ℓ-out} A) (Lift {j = ℓ-out} B) ≡ Lift {j = ℓ-out} (join A B)
    join-lift {ℓ-out = ℓ-out} {A = A} {B = B} = isoToPath (iso f g fg gf)
      where
        f : join (Lift {j = ℓ-out} A) (Lift {j = ℓ-out} B) → Lift {j = ℓ-out} (join A B)
        f (inl (lift x)) = lift (inl x)
        f (inr (lift x)) = lift (inr x)
        f (push (lift a) (lift b) i) = lift (push a b i)

        g : Lift {j = ℓ-out} (join A B) → join (Lift {j = ℓ-out} A) (Lift {j = ℓ-out} B)
        g (lift (inl x)) = inl (lift x)
        g (lift (inr x)) = inr (lift x)
        g (lift (push a b i)) = push (lift a) (lift b) i

        fg : ∀ x → f (g x) ≡ x
        fg (lift (inl x)) = refl
        fg (lift (inr x)) = refl
        fg (lift (push a b i)) = refl

        gf : ∀ x → g (f x) ≡ x
        gf (inl (lift x)) = refl
        gf (inr (lift x)) = refl
        gf (push (lift a) (lift b) i) = refl

    LiftExt : ∀ {ℓ ℓ'} {A B : Type ℓ} → Lift {j = ℓ'} A ≡ Lift {j = ℓ'} B → A ≡ B
    LiftExt p = ua (LiftEquiv ∙ₑ pathToEquiv p ∙ₑ invEquiv LiftEquiv)

{-
  Direct proof of an associativity-related property. Combined with
  commutativity, this implies that the join is associative.
-}
joinSwitch : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → join (join A B) C ≃ join (join C B) A
joinSwitch = isoToEquiv (iso switch switch invol invol)
  where
  switch : ∀ {ℓ ℓ' ℓ''}  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    → join (join A B) C → join (join C B) A
  switch (inl (inl a)) = inr a
  switch (inl (inr b)) = inl (inr b)
  switch (inl (push a b i)) = push (inr b) a (~ i)
  switch (inr c) = inl (inl c)
  switch (push (inl a) c j) = push (inl c) a (~ j)
  switch (push (inr b) c j) = inl (push c b (~ j))
  switch (push (push a b i) c j) =
    hcomp
      (λ k → λ
        { (i = i0) → push (inl c) a (~ j ∨ ~ k)
        ; (i = i1) → inl (push c b (~ j))
        ; (j = i0) → push (inr b) a (~ i)
        ; (j = i1) → push (inl c) a (~ i ∧ ~ k)
        })
      (push (push c b (~ j)) a (~ i))

  invol : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    (u : join (join A B) C) → switch (switch u) ≡ u
  invol (inl (inl a)) = refl
  invol (inl (inr b)) = refl
  invol (inl (push a b i)) = refl
  invol (inr c) = refl
  invol (push (inl a) c j) = refl
  invol (push (inr b) c j) = refl
  invol {A = A} {B} {C} (push (push a b i) c j) l =
    comp
      (λ _ → join (join A B) C)
      (λ k → λ
        { (i = i0) → push (inl a) c (j ∧ (k ∨ l))
        ; (i = i1) → push (inr b) c j
        ; (j = i0) → inl (push a b i)
        ; (j = i1) → push (inl a) c (i ∨ (k ∨ l))
        ; (l = i1) → push (push a b i) c j
        })
      (hcomp
        (λ k → λ
          { (i = i0) → push (inl a) c (j ∧ (~ k ∨ l))
          ; (i = i1) → push (inr b) c j
          ; (j = i0) → inl (push a b i)
          ; (j = i1) → push (inl a) c (i ∨ (~ k ∨ l))
          ; (l = i1) → push (push a b i) c j
          })
        (push (push a b i) c j))

{-
  Direct proof of associativity.
-}
joinAssocDirect : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → join (join A B) C ≃ join A (join B C)
joinAssocDirect {A = A} {B} {C} =
  isoToEquiv (iso forward back forwardBack backForward)
  where
  forward : join (join A B) C → join A (join B C)
  forward (inl (inl a)) = inl a
  forward (inl (inr b)) = inr (inl b)
  forward (inl (push a b i)) = push a (inl b) i
  forward (inr c) = inr (inr c)
  forward (push (inl a) c j) = push a (inr c) j
  forward (push (inr b) c j) = inr (push b c j)
  forward (push (push a b i) c j) =
    hcomp
      (λ k → λ
        { (i = i0) → push a (inr c) (j ∧ k)
        ; (i = i1) → inr (push b c j)
        ; (j = i0) → push a (inl b) i
        ; (j = i1) → push a (inr c) (i ∨ k)
        })
      (push a (push b c j) i)

  back : join A (join B C) → join (join A B) C
  back (inl a) = inl (inl a)
  back (inr (inl b)) = inl (inr b)
  back (inr (inr c)) = inr c
  back (inr (push b c j)) = push (inr b) c j
  back (push a (inl b) i) = inl (push a b i)
  back (push a (inr c) i) = push (inl a) c i
  back (push a (push b c j) i) =
    hcomp
      (λ k → λ
        { (i = i0) → push (inl a) c (j ∧ ~ k)
        ; (i = i1) → push (inr b) c j
        ; (j = i0) → inl (push a b i)
        ; (j = i1) → push (inl a) c (i ∨ ~ k)
        })
      (push (push a b i) c j)

  forwardBack : ∀ u → forward (back u) ≡ u
  forwardBack (inl a) = refl
  forwardBack (inr (inl b)) = refl
  forwardBack (inr (inr c)) = refl
  forwardBack (inr (push b c j)) = refl
  forwardBack (push a (inl b) i) = refl
  forwardBack (push a (inr c) i) = refl
  forwardBack (push a (push b c j) i) l =
    comp
      (λ _ → join A (join B C))
      (λ k → λ
        { (i = i0) → push a (inr c) (j ∧ (~ k ∧ ~ l))
        ; (i = i1) → inr (push b c j)
        ; (j = i0) → push a (inl b) i
        ; (j = i1) → push a (inr c) (i ∨ (~ k ∧ ~ l))
        ; (l = i1) → push a (push b c j) i
        })
      (hcomp
        (λ k → λ
          { (i = i0) → push a (inr c) (j ∧ (k ∧ ~ l))
          ; (i = i1) → inr (push b c j)
          ; (j = i0) → push a (inl b) i
          ; (j = i1) → push a (inr c) (i ∨ (k ∧ ~ l))
          ; (l = i1) → push a (push b c j) i
          })
        (push a (push b c j) i))

  backForward : ∀ u → back (forward u) ≡ u
  backForward (inl (inl a)) = refl
  backForward (inl (inr b)) = refl
  backForward (inl (push a b i)) = refl
  backForward (inr c) = refl
  backForward (push (inl a) c j) = refl
  backForward (push (inr b) c j) = refl
  backForward (push (push a b i) c j) l =
    comp
      (λ _ → join (join A B) C)
      (λ k → λ
        { (i = i0) → push (inl a) c (j ∧ (k ∨ l))
        ; (i = i1) → push (inr b) c j
        ; (j = i0) → inl (push a b i)
        ; (j = i1) → push (inl a) c (i ∨ (k ∨ l))
        ; (l = i1) → push (push a b i) c j
        })
      (hcomp
        (λ k → λ
          { (i = i0) → push (inl a) c (j ∧ (~ k ∨ l))
          ; (i = i1) → push (inr b) c j
          ; (j = i0) → inl (push a b i)
          ; (j = i1) → push (inl a) c (i ∨ (~ k ∨ l))
          ; (l = i1) → push (push a b i) c j
          })
        (push (push a b i) c j))

-- commutativity
join-commFun : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'} → join A B → join B A
join-commFun (inl x) = inr x
join-commFun (inr x) = inl x
join-commFun (push a b i) = push b a (~ i)

join-commFun² : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : join A B)
                → join-commFun (join-commFun x) ≡ x
join-commFun² (inl x) = refl
join-commFun² (inr x) = refl
join-commFun² (push a b i) = refl

join-comm : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (join A B) (join B A)
fun join-comm = join-commFun
inv join-comm = join-commFun
rightInv join-comm = join-commFun²
leftInv join-comm = join-commFun²

join→ : ∀ {ℓ'' ℓ'''}
     {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  → (A → C) → (B → D) → join A B → join C D
join→ f g (inl x) = inl (f x)
join→ f g (inr x) = inr (g x)
join→ f g (push a b i) = push (f a) (g b) i

-- Applying Isos to joins (more efficient than transports)
Iso→joinIso : ∀ {ℓ'' ℓ'''}
     {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  → Iso A C → Iso B D → Iso (join A B) (join C D)
fun (Iso→joinIso is1 is2) x = join→ (Iso.fun is1) (Iso.fun is2) x
inv (Iso→joinIso is1 is2) x = join→ (Iso.inv is1) (Iso.inv is2) x
rightInv (Iso→joinIso is1 is2) (inl x) i = inl (rightInv is1 x i)
rightInv (Iso→joinIso is1 is2) (inr x) i = inr (rightInv is2 x i)
rightInv (Iso→joinIso is1 is2) (push a b j) i =
  push (rightInv is1 a i) (rightInv is2 b i) j
leftInv (Iso→joinIso is1 is2) (inl x) i = inl (leftInv is1 x i)
leftInv (Iso→joinIso is1 is2) (inr x) i = inr (leftInv is2 x i)
leftInv (Iso→joinIso is1 is2) (push a b i) j =
  push (leftInv is1 a j) (leftInv is2 b j) i


joinAnnihilL : {A : Type ℓ} → isContr (join (Unit* {ℓ'}) A)
fst joinAnnihilL = inl tt*
snd joinAnnihilL (inl tt*) = refl
snd joinAnnihilL (inr a) = push tt* a
snd joinAnnihilL (push tt* a i) j = push tt* a (i ∧ j)


--- Ganea's construction ---

-- preliminary lemmas
private module _ {ℓ : Level} {B : Type ℓ} where
  ganea-fill₁ : {x : B} (y : B)
    → (p : x ≡ y)
    → (z : B)
    → (q : y ≡ z)
    → (i j k : I) → B
  ganea-fill₁ y p z q i j k =
    hfill (λ k → λ {(i = i0) → p j
                   ; (i = i1) → q (~ j ∧ k)
                   ; (j = i0) → compPath-filler p q k i
                   ; (j = i1) → y})
              (inS (p (i ∨ j)))
              k

  ganea-fill₂ : (i j k : I)
    → {x : B} (y : B) (q : x ≡ y)
       (z : B) (p : q (~ i) ≡ z)
    → B
  ganea-fill₂ i j k y q z p =
    hfill (λ k
           → λ {(i = i0) → p j
              ; (i = i1) → compPath-filler' (sym q) p k j
              ; (j = i0) → q (k ∨ ~ i)
              ; (j = i1) → z})
              (inS (p j))
              k

  ganea-fill₃ : ∀ {ℓ} {A : Type ℓ} (f : A → B) (b : B)
    (i k : I)
    (a : A) (q : f a ≡ b) (p : q (~ i) ≡ b)
    → join (fiber f b) (b ≡ b)
  ganea-fill₃ f b i k a q p =
    hfill (λ k → λ {(i = i0) → inr p
                   ; (i = i1) → push (a , p) (sym q ∙ p) (~ k)})
          (inS (inr λ j → ganea-fill₂ i j i1 _ q _ p)) k


-- Proof of the main theorem
module _ {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  fib-cofib : Type _
  fib-cofib = cofib {A = fiber (fst f) (pt B)} fst

  GaneaMap : fib-cofib → fst B
  GaneaMap (inl x) = pt B
  GaneaMap (inr x) = fst f x
  GaneaMap (push a i) = a .snd (~ i)

  GaneaFib : Type _
  GaneaFib = fiber GaneaMap (pt B)

  join→GaneaFib : join (fiber (fst f) (pt B)) (Ω B .fst) → GaneaFib
  join→GaneaFib (inl x) = inr (fst x) , snd x
  join→GaneaFib (inr x) = (inl tt) , x
  proj₁ (join→GaneaFib (push a b i)) = push (fst a , snd a ∙ sym b) (~ i)
  snd (join→GaneaFib (push a b i)) j = ganea-fill₁ _ (snd a) _  (sym b) i j i1

  GaneaFib→join : GaneaFib → join (fiber (fst f) (pt B)) (Ω B .fst)
  GaneaFib→join (inl x , p) = inr p
  GaneaFib→join (inr x , p) = inl (x , p)
  GaneaFib→join (push (a , q) i , p) =
    ganea-fill₃ (fst f) (pt B) i i1 a q p

  GaneaFib→join→GaneaFib : (x : GaneaFib)
    → join→GaneaFib (GaneaFib→join x) ≡ x
  GaneaFib→join→GaneaFib (inl x , y) = refl
  GaneaFib→join→GaneaFib (inr x , y) = refl
  GaneaFib→join→GaneaFib (push (a , q) i , p) j =
    hcomp (λ k
    → λ {(i = i0) → inl tt , p
        ; (i = i1) → main p k j
        ; (j = i0) → join→GaneaFib (ganea-fill₃ (fst f) (pt B) i k a q p)
        ; (j = i1) → push (a , q) i , p})
          ((push (a , q) (i ∧ j))
         , λ k → hcomp (λ r
           → λ {(i = i0) → p k
               ; (i = i1) → compPath-filler' (sym q) p (r ∧ (~ j)) k
               ; (j = i0) → ganea-fill₂ i k r _ q _ p
               ; (j = i1) → p k
               ; (k = i0) → q ((r ∧ ~ j) ∨ ~ i)
               ; (k = i1) → snd B})
      (p k))
    where
    filler₁ : (i j k : I) (p : fst f a ≡ pt B) → fst B
    filler₁ i j k p =
      hfill (λ k
        → λ {(i = i0) → compPath-filler p (sym (sym q ∙ p)) k j
            ; (i = i1) → q (j ∨ ~ k)
            ; (j = i0) → q (~ k ∧ i)
            ; (j = i1) → ((λ i₂ → q (~ i₂)) ∙ p) (~ k ∧ ~ i)})
       (inS (compPath-filler (sym q) p j (~ i))) k

    main' : (p : fst f a ≡ pt B)
      → cong join→GaneaFib (push (a , p) (sym q ∙ p))
        ≡ λ i → (push (a , q) (~ i)) , (compPath-filler' (sym q) p i)
    proj₁ (main' p i j) = push (a , λ j → filler₁ i j i1 p) (~ j)
    snd (main' p i j) r =
      hcomp (λ k → λ {(i = i0) → ganea-fill₁ _ p _ (sym (sym q ∙ p)) j r k
                     ; (i = i1) → J-lem _ q _ p k r j
                     ; (j = i0) → compPath-filler' (sym q) p (~ k ∧ i) r
                     ; (j = i1) → (sym q ∙ p) (r ∨ ~ (k ∨ i))
                     ; (r = i0) → filler₁ i j k p
                     ; (r = i1) → snd B})
            (J-lem₂ _ q _ p r j i)
      where
      J-lem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (q : x ≡ y)
        (z : A) (p : x ≡ z)
        → PathP (λ k
          → Square (λ j → q (j ∨ ~ k)) refl
                    (compPath-filler' (λ i₂ → q (~ i₂)) p (~ k))
                    (sym q ∙ p))
                 (λ i _ → (sym q ∙ p) i)
                  λ i j → compPath-filler' (sym q) p j i
      J-lem {x = x} =
        J> (J> J-lem-refl x refl (refl ∙ refl)
                (compPath-filler' (sym refl) refl))
        where
        J-lem-refl : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A)
          (p : x ≡ y) (q : x ≡ y) (r : p ≡ q)
          → PathP (λ k → Square refl refl (r (~ k)) q)
                   (λ i _ → q i) λ i j → r j i
        J-lem-refl = J> (J> refl)

      J-lem₂ : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (q : x ≡ y) (z : A) (p : x ≡ z)
        → PathP (λ r → Square (λ i → compPath-filler' (sym q) p i r)
                                (λ i → (sym q ∙ p) (r ∨ ~ i))
                                (λ j → p (r ∨ j)) refl)
          (λ j i → compPath-filler (sym q) p j (~ i))
          refl
      J-lem₂ {x = x} =
        J> (J> λ i j k → J-lem₂-refl _ (rUnit (refl {x = x})) k i j)
        where
        J-lem₂-refl : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (r : refl ≡ q)
          → PathP (λ k
            → Square (λ j → r j (~ k)) (λ _ → x)
                      (r k) λ i → q (i ∨ ~ k))
                   refl λ i _ → q i
        J-lem₂-refl = J> refl


    main : (p : fst f a ≡ pt B)
      → PathP (λ k → join→GaneaFib (push (a , p) (sym q ∙ p) (~ k))
                    ≡ (inr a , p))
              (λ i → push (a , q) i , compPath-filler' (sym q) p (~ i))
              refl
    main p = flipSquare (cong sym (main' p)
      ◁ λ j i → push (a , q) (j ∨ i)
          , compPath-filler' (sym q) p (~ (j ∨ i)))

  join→GaneaFib→join : (x : join (fiber (fst f) (pt B)) (Ω B .fst))
    → GaneaFib→join (join→GaneaFib x) ≡ x
  join→GaneaFib→join (inl x) = refl
  join→GaneaFib→join (inr x) = refl
  join→GaneaFib→join (push (a , q) p i) j =
    main (fst f) (pt B) q p j i
    where
    main : (f : fst A → fst B) (b : fst B)
        (q : f a ≡ b) (p : b ≡ b)
      → Path (Path (join (fiber f b) (b ≡ b)) _ _)
        (λ i → ganea-fill₃ f b (~ i) i1 a (q ∙ sym p)
        λ j → ganea-fill₁ _ q _ (sym p) i j i1)
        (push (a , q) p)
    main f = J> λ q i j
      → hcomp (λ k → λ {(i = i0) → ganea-fill₃ f (f a) (~ j) i1
                                       a (lUnit (sym q) k)
                                       (side _ q k j)
                        ; (i = i1) → push (a , refl) q j
                        ; (j = i0) → inl (a , refl)
                        ; (j = i1) → inr q})
         (hcomp (λ k → λ {(i = i0) → ganea-fill₃ f (f a) (~ j) k
                                       a (sym q) λ j₂ → q (~ j ∨ j₂)
                        ; (i = i1) → push (a , refl) q (j ∨ ~ k)
                        ; (j = i0) → push (a , refl) (rUnit q (~ i)) (~ k)
                        ; (j = i1) → inr q})
                (inr λ k → btm _ q k i j))
       where
       btm : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (q : x ≡ y)
         → Cube refl refl
                 (λ k j → ganea-fill₂ (~ j) k i1
                            _ (sym q) _ (λ j₂ → q (~ j ∨ j₂)))
                 (λ k j → q k)
                 (λ k i → rUnit q (~ i) k)
                 λ k i → q k
       btm {x = x} =
         J> λ k i j → ganea-fill₂ (~ j) k (~ i) x (sym refl) x refl


       side : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
         → PathP (λ k → Square refl p (lUnit (sym p) k) refl)
                  (λ i j → p (~ i ∨ j))
                  λ j j₂ → ganea-fill₁ _ refl _ (sym p) j j₂ i1
       side {A = A} {x = x} =
         J> ((λ i j k → lUnit (refl {x = x}) (i ∧ ~ k) j)
            ▷ λ k i j → filler k j i)
         where
         filler : I → I → I → A
         filler k i j =
             hcomp (λ r → λ {(i = i0) → rUnit (refl {x = x}) r j
                            ; (i = i1) → x
                            ; (j = i0) → x
                            ; (j = i1) → x
                            ; (k = i0) → rUnit (refl {x = x}) (r ∧ ~ i) j
                            ; (k = i1) → ganea-fill₁ x refl x refl j i r})
                   x

  -- Main theorem
  GaneaIso : Iso GaneaFib (join (fiber (fst f) (pt B)) (Ω B .fst))
  fun GaneaIso = GaneaFib→join
  inv GaneaIso = join→GaneaFib
  rightInv GaneaIso = join→GaneaFib→join
  leftInv GaneaIso = GaneaFib→join→GaneaFib

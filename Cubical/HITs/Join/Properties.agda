{-

This file contains:

- Equivalence with the pushout definition
  Written by: Loïc Pujet, September 2019

- Associativity of the join
  Written by: Loïc Pujet, September 2019

-}

{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Join.Properties where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Prod

open import Cubical.HITs.Join.Base
open import Cubical.HITs.Pushout

private
  variable
    ℓ : Level
    ℓ' : Level


-- Alternative definition of the join using a pushout
joinAlt : (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
joinAlt A B = Pushout {_} {_} {_} {A × B} {A} {B} proj₁ proj₂

-- Proof that it is equal
joinAlt-iso-join : (A : Type ℓ) → (B : Type ℓ') → Iso (joinAlt A B) (join A B)
joinAlt-iso-join A B = iso (joinAlt→join A B) (join→joinAlt A B) (join→joinAlt→join A B) (joinAlt→join→joinAlt A B)
  where
    joinAlt→join : (A : Type ℓ) → (B : Type ℓ') → joinAlt A B → join A B
    joinAlt→join A B (inl x) = inl x
    joinAlt→join A B (inr x) = inr x
    joinAlt→join A B (push y i) = push (proj₁ y) (proj₂ y) i

    join→joinAlt : (A : Type ℓ) → (B : Type ℓ') → join A B → joinAlt A B
    join→joinAlt A B (inl x) = inl x
    join→joinAlt A B (inr x) = inr x
    join→joinAlt A B (push a b i) = push (a , b) i

    joinAlt→join→joinAlt : (A : Type ℓ) → (B : Type ℓ') → ∀ x → join→joinAlt A B (joinAlt→join A B x) ≡ x
    joinAlt→join→joinAlt A B (inl x) = refl
    joinAlt→join→joinAlt A B (inr x) = refl
    joinAlt→join→joinAlt A B (push (a , b) j) = refl

    join→joinAlt→join : (A : Type ℓ) → (B : Type ℓ') → ∀ x → joinAlt→join A B (join→joinAlt A B x) ≡ x
    join→joinAlt→join A B (inl x) = refl
    join→joinAlt→join A B (inr x) = refl
    join→joinAlt→join A B (push a b j) = refl

-- We will need both the equivalence and path version
joinAlt≃join : (A : Type ℓ) → (B : Type ℓ') → joinAlt A B ≃ join A B
joinAlt≃join A B = isoToEquiv (joinAlt-iso-join A B)

joinAlt≡join : (A : Type ℓ) → (B : Type ℓ') → joinAlt A B ≡ join A B
joinAlt≡join A B = isoToPath (joinAlt-iso-join A B)


{-
  Proof of associativity of the join
-}
join-assoc : (A : Type₀) → (B : Type₀) → (C : Type₀)
             → join (join A B) C ≡ join A (join B C)
join-assoc A B C = (joinAlt≡join (join A B) C) ⁻¹
                   ∙ (spanEquivToPath sp3≃sp4) ⁻¹
                   ∙ (3x3-span.3x3-lemma span) ⁻¹
                   ∙ (spanEquivToPath sp1≃sp2)
                   ∙ (joinAlt≡join A (join B C))
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
      e4 = joinAlt≃join B C;
      H1 = H1;
      H3 = H2 }
      where
        A×join : Type₀
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
        H1 (push (a , (b , c)) i) j = A□0→A (doubleCompPath-filler refl (λ i → push (a , c) i) refl i j)

        H2 : (x : 3x3-span.A□2 span) → proj₂ (A□2→A×join x) ≡ fst (joinAlt≃join _ _) (3x3-span.f□3 span x)
        H2 (inl (a , b)) = refl
        H2 (inr (a , c)) = refl
        H2 (push (a , (b , c)) i) j = fst (joinAlt≃join _ _) (doubleCompPath-filler refl (λ i → push (b , c) i) refl i j)

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
      e0 = joinAlt≃join A B;
      e2 = A2□≃join×C;
      e4 = A4□≃C;
      H1 = H4;
      H3 = H3 }
      where
        join×C : Type₀
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
        H3 (push (a , (b , c)) i) j = A4□→C (doubleCompPath-filler refl (λ i → push (a , c) i) refl i j)

        H4 : (x : 3x3-span.A2□ span) → proj₁ (A2□→join×C x) ≡ fst (joinAlt≃join _ _) (3x3-span.f1□ span x)
        H4 (inl (a , c)) = refl
        H4 (inr (b , c)) = refl
        H4 (push (a , (b , c)) i) j = fst (joinAlt≃join _ _) (doubleCompPath-filler refl (λ i → push (a , b) i) refl i j)

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group.Base

module GroupLemmas {ℓ : Level} (G : Group {ℓ}) where
  open Group G
  abstract
    simplL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a + b ≡ a + c → b ≡ c
    simplL a {b} {c} p =
      b
        ≡⟨ sym (lid b) ∙ cong (_+ b) (sym (invl a)) ∙ sym (assoc _ _ _) ⟩
      - a + (a + b)
        ≡⟨ cong (- a +_) p ⟩
      - a + (a + c)
        ≡⟨ assoc _ _ _ ∙ cong (_+ c) (invl a) ∙ lid c ⟩
      c ∎

    simplR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a + c ≡ b + c → a ≡ b
    simplR {a} {b} c p =
      a
        ≡⟨ sym (rid a) ∙ cong (a +_) (sym (invr c)) ∙ assoc _ _ _ ⟩
      (a + c) - c
        ≡⟨ cong (_- c) p ⟩
      (b + c) - c
        ≡⟨ sym (assoc _ _ _) ∙ cong (b +_) (invr c) ∙ rid b ⟩
      b ∎

  invInvo : (a : ⟨ G ⟩) → - (- a) ≡ a
  invInvo a = simplL (- a) (invr (- a) ∙ sym (invl a))

  invId : - 0g ≡ 0g
  invId = simplL 0g (invr 0g ∙ sym (lid 0g))

  idUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e + x ≡ x → e ≡ 0g
  idUniqueL {e} x p = simplR x (p ∙ sym (lid _))

  idUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x + e ≡ x → e ≡ 0g
  idUniqueR x {e} p = simplL x (p ∙ sym (rid _))

  invUniqueL : {g h : ⟨ G ⟩} → g + h ≡ 0g → g ≡ - h
  invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

  invUniqueR : {g h : ⟨ G ⟩} → g + h ≡ 0g → h ≡ - g
  invUniqueR {g} {h} p = simplL g (p ∙ sym (invr g))


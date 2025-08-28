open import PrefixStripping.Prelude hiding (_⟨_⟩_)
open Relation.Binary

import PrefixStripping.Decide.Universe

module PrefixStripping.Decide.Coinduction
    {𝕋 : Set} {END : Set}
    (_≟ᵀ_ : DecidableEquality 𝕋)
    (_≟E_ : DecidableEquality END)
    (𝒰⁰ : PrefixStripping.Decide.Universe.𝒰 _≟ᵀ_ _≟E_)
  where

import Relation.Binary.Construct.On as On

open import PrefixStripping.Syntax

module Universe = PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_
open Universe

open import PrefixStripping.Sessions.Subterm 𝕋 as ST

open Nat using (_+_; _*_)
open import Data.List as List using (List; []; _∷_)

record Hyp : Set where
  constructor mkHyp
  field
    u  : ⊢𝒰
    p⊑ : 𝒰.p 𝒰⌊ u ⌋ ⊑ 𝒰.p 𝒰⁰
    s⊑ : 𝒰.s 𝒰⌊ u ⌋ ⊑ 𝒰.s 𝒰⁰

  p = ⊢𝒰.p u
  s = ⊢𝒰.s u

⟨_⟩ : Hyp → 𝒰
⟨ h ⟩ = 𝒰⌊ Hyp.u h ⌋

⊢⟨_⟩ : Hyp → ⊢𝒰
⊢⟨ h ⟩ = Hyp.u h

⊢⟨_⟩* : List Hyp → List ⊢𝒰
⊢⟨_⟩* = List.map ⊢⟨_⟩

hypDecSetoid : DecSetoid _ _
hypDecSetoid = On.decSetoid Universe.decSetoid ⟨_⟩

hypSetoid : Setoid _ _
hypSetoid = DecSetoid.setoid hypDecSetoid

module Countdown where
  open import Data.List.Countdown hypDecSetoid as Countdown hiding (empty) public
  open DecSetoid hypDecSetoid using (_≈_)

  MAX : ℕ
  MAX = ST.count (𝒰.p 𝒰⁰) * ST.count (𝒰.s 𝒰⁰)

  indexOfᵖ : Hyp → 𝔽 (ST.count (𝒰.p 𝒰⁰))
  indexOfᵖ H = ≼-index (⊑⇒≼ (Hyp.p⊑ H))

  indexOfˢ : Hyp → 𝔽 (ST.count (𝒰.s 𝒰⁰))
  indexOfˢ H = ≼-index (⊑⇒≼ (Hyp.s⊑ H))

  indexOf : Hyp → 𝔽 MAX
  indexOf H = Fin.combine (indexOfᵖ H) (indexOfˢ H)

  indexOf-injective : (H₁ H₂ : Hyp) → indexOf H₁ ≡ indexOf H₂ → H₁ ≈ H₂
  indexOf-injective H₁ H₂ eq =
    let eq₁ , eq₂ = Fin.combine-injective (indexOfᵖ H₁) (indexOfˢ H₁)
                                          (indexOfᵖ H₂) (indexOfˢ H₂)
                                          eq
    in
    cong₂ _%_
      (≼-index-injective (⊑⇒≼ (Hyp.p⊑ H₁)) (⊑⇒≼ (Hyp.p⊑ H₂)) eq₁)
      (≼-index-injective (⊑⇒≼ (Hyp.s⊑ H₁)) (⊑⇒≼ (Hyp.s⊑ H₂)) eq₂)

  begin : [] ⊕ MAX
  begin = record
    { kind = inj₂ ∘ indexOf
    ; injective = λ {H₁} {H₂} eqˡ eqʳ →
        indexOf-injective H₁ H₂
          (trans (inj₂-injective eqˡ) (sym (inj₂-injective eqʳ)))
    }

  open import Data.List.Membership.Setoid hypSetoid

  lookupOrInsert′ : ∀ {counted : List Hyp} {m} → counted ⊕ m →
    ∀ x → x ∈ counted ⊎
          ∃ λ n → m ≡ suc n × x ∷ counted ⊕ n × x ∉ counted
  lookupOrInsert′ c x with Countdown.lookup c x
  ... | yes x∈ = inj₁ x∈
  lookupOrInsert′ {m = zero}  c x | no x∉ = contradiction (Countdown.lookup! c x) x∉
  lookupOrInsert′ {m = suc m} c x | no x∉ = inj₂ (-, refl , insert c x x∉ , x∉)

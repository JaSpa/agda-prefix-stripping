open import PrefixStripping.Prelude hiding (ℓ)
open Relation.Binary

module PrefixStripping.Decide {𝕋 END : Set} (_≟ᵀ_ : DecidableEquality 𝕋) (_≟E_ : DecidableEquality END) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Maybe using (just; nothing; Is-just; Is-nothing)
open import Data.Maybe.Relation.Unary.All as If-just using (just; nothing) renaming (All to If-just)
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.Unit using (⊤)

open import PrefixStripping.Syntax

open import PrefixStripping.Sessions.Equivalence 𝕋 as Equivalence
open import PrefixStripping.Sessions.Subterm 𝕋 as ST
open import PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_ as Universe
import PrefixStripping.Decide.Soundness _≟ᵀ_ _≟E_ as Soundness
import PrefixStripping.Decide.Coinduction _≟ᵀ_ _≟E_ as Seen

open Universe.Variables
open Nat using () renaming (suc-injective to suc⁻¹)

module Core (𝒰⁰ : 𝒰) where
  open Seen 𝒰⁰ public
  open Countdown using (_⊕_; lookupOrInsert′)
  open Hyp hiding (p; s)

  open import Data.List.Membership.Setoid hypSetoid renaming (_∈_ to _⟨∈⟩_; _∉_ to _⟨∉⟩_)
  open import Data.List.Membership.Propositional as In
  open Connected
  open Pointwise

  import Data.List.Membership.Setoid.Properties as ⟨∈⟩

  private variable ℓ : ℕ
  private variable η : List Hyp

  ⟨∈⟩⇒∈ : (H : Hyp) → H ⟨∈⟩ η → ⊢⟨ H ⟩ ∈ ⊢⟨ η ⟩*
  ⟨∈⟩⇒∈ H H∈ = ⟨∈⟩.∈-map⁺ (DecSetoid.setoid hypDecSetoid) (Eq.setoid ⊢𝒰) ⊢𝒰-irr {H} H∈

  ⟨∈⟩⇐∈ : (H : Hyp) → ⊢⟨ H ⟩ ∈ ⊢⟨ η ⟩* → H ⟨∈⟩ η
  ⟨∈⟩⇐∈ H H∈ with ⟨∈⟩.∈-map⁻ (DecSetoid.setoid hypDecSetoid) (Eq.setoid ⊢𝒰) H∈
  ... | H′ , H′∈ , eq with uH ← u H rewrite eq = H′∈

  data θ-Storable : Pred 𝒰 0ℓ where
    θ-♯ : ∀ {T₁ T₂ : 𝕋} → θ-Storable (⁉₁ ♯ T₁ ▸ p % ⁉₂ ♯ T₂ ▸ s)
    θ-⋆ : θ-Storable (⁉₁ ⟨ p₁ ⨟ p₂ ⟩ % ⁉₂ ⟨ s₁ ⨟ s₂ ⟩)

  θ-Stored* : Pred (List ⊢𝒰) _
  θ-Stored* = All (θ-Storable ∘ 𝒰⌊_⌋)

  θ-Stored⟨_⟩* : Pred (List Hyp) _
  θ-Stored⟨ η ⟩* = θ-Stored* ⊢⟨ η ⟩*

  Unique : List ⊢𝒰 → ⊢ p → ⊢ s → ⊢ℝ → Set
  Unique θ ⊢p ⊢s 𝒓 = ∀ {𝒓′} → θ ⊢ ⊢p % ⊢s ＝ 𝒓′ → 𝒓 ≃ᴿ 𝒓′

  infix 4 _⊢_≤ₚ_ _⊢_≰ₚ_ _⊢_≤?_

  _⊢_≤ₚ_ : List ⊢𝒰 → ⊢ p → ⊢ s → Set
  θ ⊢ ⊢p ≤ₚ ⊢s = ∃ λ 𝒓 →
    θ ⊢ ⊢p % ⊢s ＝ 𝒓     ×
    If-just (λ _ → ∃□ ⊢p) 𝒓 ×
    Unique θ ⊢p ⊢s 𝒓

  _⊢_≰ₚ_ : List ⊢𝒰 → ⊢ p → ⊢ s → Set
  θ ⊢ ⊢p ≰ₚ ⊢s =
    (∀ {r} {⊢r : ⊢ r} → ⊢[ ⊢p ◇ ⊢r ] ≄ ⊢s) ×
    (∀ {𝒓} → ¬ θ ⊢ ⊢p % ⊢s ＝ 𝒓)

  _⊢_≤?_ : List ⊢𝒰 → ⊢ p → ⊢ s → Set
  θ ⊢ ⊢p ≤? ⊢s = θ ⊢ ⊢p ≤ₚ ⊢s ⊎ θ ⊢ ⊢p ≰ₚ ⊢s

  %⁻¹-μˡ : ∀ {p} {⊢p : ⊢ p} {pᶜ : ⊢ᶜ p} →
    θ-Stored* θ →
    θ ⊢ ⊢μ ⊢p pᶜ % ⊢s ＝ 𝒓 →
    θ ⊢ ⊢-unfold ⊢p pᶜ % ⊢s ＝ 𝒓
  %⁻¹-μˡ θ-st (%-μˡ x) = x
  %⁻¹-μˡ θ-st (%-μʳ x) = %-μʳ (%⁻¹-μˡ θ-st x)
  %⁻¹-μˡ θ-st (hyp x)  = case All.lookup θ-st x of λ()

  %⁻¹-μʳ : ∀ {s} {⊢s : ⊢ s} {sᶜ : ⊢ᶜ s} →
    θ-Stored* θ →
    θ ⊢ ⊢p % ⊢μ ⊢s sᶜ ＝ 𝒓 →
    θ ⊢ ⊢p % ⊢-unfold ⊢s sᶜ ＝ 𝒓
  %⁻¹-μʳ θ-st (%-□  eq) = %-□ (≃-trans (≃-sym (≃-μ _ _)) eq)
  %⁻¹-μʳ θ-st (%-μˡ x)  = %-μˡ (%⁻¹-μʳ θ-st x)
  %⁻¹-μʳ θ-st (%-μʳ x)  = x
  %⁻¹-μʳ θ-st (hyp x)   = case All.lookup θ-st x of λ()

  buildHyp : ∀ (H : Hyp) → θ-Storable 𝒰⌊ u H ⌋ → H ⟨∈⟩ η → ⊢⟨ η ⟩* ⊢ Hyp.p H ≤ₚ Hyp.s H
  buildHyp H θ-H H∈ = -, hyp (⟨∈⟩⇒∈ H H∈) , nothing , λ where
    (%-♯ ∉θ _)     → contradiction (⟨∈⟩⇒∈ H H∈) ∉θ
    (%-⋆ ∉θ _ _ _) → contradiction (⟨∈⟩⇒∈ H H∈) ∉θ
    (hyp x)        → nothing

  %-⋆-uniq-⊥ˡ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    H ∉ θ →
    Unique (H ∷ θ) ⊢p₁ ⊢s₁ nothing →
    Unique (H ∷ θ) ⊢p₂ ⊢s₂ 𝒓 →
    Unique θ (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) 𝒓
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ eq)) = ≃ᴿ-trans (u₂ %₂) eq
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ (just eq))) = case u₁ %₁ of λ()
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ nothing)) = u₂ %₂
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) = case u₁ %₁ of λ()
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ (hyp H∈) = contradiction H∈ H∉

  %-⋆-uniq-⊥ʳ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    H ∉ θ →
    Unique (H ∷ θ) ⊢p₁ ⊢s₁ 𝒓 →
    Unique (H ∷ θ) ⊢p₂ ⊢s₂ nothing →
    Unique θ (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) 𝒓
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ (just x))) = case u₂ %₂ of λ()
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ nothing)) = u₁ %₁
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ eq)) = ≃ᴿ-trans (u₁ %₁) eq
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) = case u₂ %₂ of λ()
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ (hyp H∈) = contradiction H∈ H∉

  %-⋆-uniq-just :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    ∀ {r₁ r₂} →
    H ∉ θ →
    Unique (H ∷ θ) ⊢p₁ ⊢s₁ (just r₁) →
    Unique (H ∷ θ) ⊢p₂ ⊢s₂ (just r₂) →
    Unique θ (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) (just r₁)
  %-⋆-uniq-just H∉ u₁ u₂ (%-⋆ _ p%s₁ p%s₂ (⊔-⊥ˡ eq)) = case u₁ p%s₁ of λ()
  %-⋆-uniq-just H∉ u₁ u₂ (%-⋆ _ p%s₁ p%s₂ (⊔-⊥ʳ eq)) = case u₂ p%s₂ of λ()
  %-⋆-uniq-just H∉ u₁ u₂ (%-⋆ _ p%s₁ p%s₂ (⊔-≃ eq₁ eq₂)) = just (≃-trans (PW.drop-just (u₁ p%s₁)) eq₁)
  %-⋆-uniq-just H∉ u₁ u₂ (hyp H∈) = contradiction H∈ H∉

  %-⋆-r≃ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    H ∉ θ →
    Unique (H ∷ θ) ⊢p₁ ⊢s₁ (just (-, ⊢r₁)) →
    Unique (H ∷ θ) ⊢p₂ ⊢s₂ (just (-, ⊢r₂)) →
    θ ⊢ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ 𝒓 →
    ⊢r₁ ≃ ⊢r₂
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ x)) = case u₁ %₁ of λ()
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ x)) = case u₂ %₂ of λ()
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) =
    ≃-trans (PW.drop-just (u₁ %₁)) $
    ≃-trans eq₁ $
    ≃-trans eq₂ $
    ≃-sym (PW.drop-just (u₂ %₂))
  %-⋆-r≃ H∉ u₁ u₂ (hyp H∈) = contradiction H∈ H∉

  run : (𝓒 : η ⊕ ℓ) (θ-st : θ-Stored⟨ η ⟩*) (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p ⊑ 𝒰.p 𝒰⁰
    → s ⊑ 𝒰.s 𝒰⁰
    → ⊢⟨ η ⟩* ⊢ ⊢p ≤? ⊢s

  run-unfold : (𝓒 : η ⊕ ℓ) (ℓᵖ ℓˢ : ℕ)
    → .(μLeaders p ≡ ℓᵖ)
    → .(μLeaders s ≡ ℓˢ)
    → θ-Stored⟨ η ⟩*
    → (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p ⊑ 𝒰.p 𝒰⁰
    → s ⊑ 𝒰.s 𝒰⁰
    → ⊢⟨ η ⟩* ⊢ ⊢p ≤? ⊢s

  run-hnf : (𝓒 : η ⊕ ℓ)
    → .(μLeaders p ≡ 0)
    → .(μLeaders s ≡ 0)
    → θ-Stored⟨ η ⟩*
    → (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p ⊑ 𝒰.p 𝒰⁰
    → s ⊑ 𝒰.s 𝒰⁰
    → ⊢⟨ η ⟩* ⊢ ⊢p ≤? ⊢s

  run θ = run-unfold θ _ _ refl refl

  run-unfold 𝓒 0 0 eqᵖ eqˢ θ-st ⊢p ⊢s p⊑ s⊑ =
    run-hnf 𝓒 eqᵖ eqˢ θ-st ⊢p ⊢s p⊑ s⊑
  run-unfold 𝓒 0 (suc ℓˢ) eqᵖ eqˢ θ-st ⊢p (⊢μ s sᶜ) p⊑ s⊑ =
    Sum.map
      (Π.map₂ (Π.map %-μʳ (Π.map₂ λ r≃ p%s → r≃ (%⁻¹-μʳ θ-st p%s))))
      (Π.map
        (λ fail eq  → fail (≃-trans eq (≃-μ s sᶜ)))
        (λ fail p%s → fail (%⁻¹-μʳ θ-st p%s)))
      (run-unfold 𝓒 0 ℓˢ eqᵖ
        (trans (μLeaders-⋯ₛ-0↦ s sᶜ) (suc⁻¹ eqˢ))
        θ-st ⊢p (⊢-unfold s sᶜ) p⊑
        (⊑-trans (⊑-μ refl) s⊑))
  run-unfold 𝓒 (suc ℓᵖ) ℓˢ eqᵖ eqˢ θ-st (⊢μ p pᶜ) ⊢s p⊑ s⊑ =
    Sum.map
      (Π.map₂ (Π.map %-μˡ (Π.map
        (If-just.map (cong-∃□ (≃-sym (≃-μ p pᶜ))))
        (λ r≃ p%s → r≃ (%⁻¹-μˡ θ-st p%s)))))
      (Π.map
        (λ fail eq  → fail (≃-trans (≃-sym (≃-μ◇ p pᶜ)) eq))
        (λ fail p%s → fail (%⁻¹-μˡ θ-st p%s)))
      (run-unfold 𝓒 ℓᵖ ℓˢ (trans (μLeaders-⋯ₛ-0↦ p pᶜ) (suc⁻¹ eqᵖ)) eqˢ θ-st (⊢-unfold p pᶜ) ⊢s
        (⊑-trans (⊑-μ refl) p⊑)
        s⊑)

  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st ⊢□ s p⊑ s⊑ = inj₁ $ -, %-□ ≃-refl , just ∃□-□ , λ where
    (%-□ x) → just x
    (hyp x) → case All.lookup θ-st x of λ()

  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st p⁰@(⊢♯ ⁉₁ · T₁ ▸ p) s⁰@(⊢♯ ⁉₂ · T₂ ▸ s) p⊑ s⊑
    using H ← mkHyp (p⁰ % s⁰) p⊑ s⊑
    with lookupOrInsert′ 𝓒 H
  ... | inj₁ H∈ = inj₁ (buildHyp H θ-♯ H∈)
  ... | inj₂ (-, refl , 𝓒′ , H∉)
    with ⁉₁ ≟⁉ ⁉₂ ×-dec T₁ ≟ᵀ T₂
  ... | no ⁉/T≠ = inj₂ ((λ eq → case eq 1 of λ{ refl → ⁉/T≠ (refl , refl) }) , λ where
    (%-♯ H∉ p%s) → ⁉/T≠ (refl , refl)
    (hyp x)      → H∉ (⟨∈⟩⇐∈ H x))
  ... | yes (refl , refl)
    with run 𝓒′ (θ-♯ ∷ θ-st) p s (⊑-stepˡ step-♯ p⊑) (⊑-stepˡ step-♯ s⊑)
  ... | inj₁ (-, p%s , fin? , uniq) = inj₁ $ -, %-♯ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s , If-just.map (∃□-step⁻¹ step-♯) fin? , λ where
    (%-♯ H∉ p%s′) → uniq p%s′
    (hyp H∈)      → contradiction (⟨∈⟩⇐∈ H H∈) H∉
  ... | inj₂ p≰s = inj₂ (proj₁ p≰s ∘ ≃⁻¹-♯ , λ where
    (%-♯ H∉ p%s) → proj₂ p≰s p%s
    (hyp H∈)     → H∉ (⟨∈⟩⇐∈ H H∈))

  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st p⁰@(⊢ ⁉₁ ⋆⟨ p₁ ⨟ p₂ ⟩) s⁰@(⊢ ⁉₂ ⋆⟨ s₁ ⨟ s₂ ⟩) p⊑ s⊑
    using H ← mkHyp (p⁰ % s⁰) p⊑ s⊑
    with lookupOrInsert′ 𝓒 H
  ... | inj₁ H∈ = inj₁ (buildHyp H θ-⋆ H∈)
  ... | inj₂ (-, refl , 𝓒′ , H∉)
    with ⁉₁ ≟⁉ ⁉₂
  ... | no ⁉≠ = inj₂ ((λ eq → case eq 1 of λ{ refl → ⁉≠ refl }) , λ where
    (%-⋆ _ _ _ _) → ⁉≠ refl
    (hyp H∈)      → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | yes refl
    with run 𝓒′ (θ-⋆ ∷ θ-st) p₁ s₁ (⊑-stepˡ step-⋆₁ p⊑) (⊑-stepˡ step-⋆₁ s⊑)
  ... | inj₂ (¬eq , ¬%₁) = inj₂ (¬eq ∘ proj₁ ∘ ≃⁻¹-⋆ , λ where
    (%-⋆ _ %₁ _ _) → ¬%₁ %₁
    (hyp H∈)       → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | inj₁ (r₁ , %₁ , fin₁ , u₁)
    with run 𝓒′ (θ-⋆ ∷ θ-st) p₂ s₂ (⊑-stepˡ step-⋆₂ p⊑) (⊑-stepˡ step-⋆₂ s⊑)
  ... | inj₂ (¬eq , ¬%₂) = inj₂ (¬eq ∘ proj₂ ∘ ≃⁻¹-⋆ , λ where
    (%-⋆ _ _ %₂ _) → ¬%₂ %₂
    (hyp H∈)       → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | inj₁ (r₂ , %₂ , fin₂ , u₂)
    with r₁ | r₂
  ... | nothing | nothing = inj₁
    ( nothing
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) %₁ %₂ (⊔-⊥ˡ nothing)
    , nothing
    , %-⋆-uniq-⊥ˡ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂ )
  ... | nothing | just r  = inj₁
    ( just r
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) %₁ %₂ (⊔-⊥ˡ (just ≃-refl))
    , If-just.map (∃□-step⁻¹ step-⋆₂) fin₂
    , %-⋆-uniq-⊥ˡ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂ )
  ... | just r  | nothing = inj₁
    ( just r
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) %₁ %₂ (⊔-⊥ʳ (just ≃-refl))
    , If-just.map (∃□-step⁻¹ step-⋆₁) fin₁
    , %-⋆-uniq-⊥ʳ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂ )
  ... | just (-, ⊢r₁) | just (-, ⊢r₂)
    with ⊢r₁ ≃? ⊢r₂
  ... | yes r≃ = inj₁
    ( just (-, ⊢r₁)
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) %₁ %₂ (⊔-≃ ≃-refl r≃)
    , If-just.map (∃□-step⁻¹ step-⋆₁) fin₁
    , %-⋆-uniq-just (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂ )
  ... | no r≄ = inj₂
    ( remPaths-r≄ r≄ (remPaths %₁) (remPaths %₂)
    , r≄ ∘ %-⋆-r≃ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂
    )

  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st (⊢♯ p) ⊢□ p⊑ s⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (hyp x) → case All.lookup θ-st x of λ() }
    )
  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st (⊢♯ p) ⊢⋆⟨ _ ⨟ _ ⟩ p⊑ s⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (hyp x) → case All.lookup θ-st x of λ() }
    )
  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st ⊢⋆⟨ _ ⨟ _ ⟩ ⊢□ p⊑ s⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (hyp x) → case All.lookup θ-st x of λ() }
    )
  run-hnf 𝓒 ¬μᵖ ¬μˢ θ-st ⊢⋆⟨ _ ⨟ _ ⟩ (⊢♯ _) p⊑ s⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (hyp x) → case All.lookup θ-st x of λ() }
    )

module _ (⊢p : ⊢ p) (⊢s : ⊢ s) where
  open import Data.Unit using (⊤)
  open import Data.Maybe using (Maybe; just; nothing; maybe)
  open import Data.Maybe.Relation.Unary.All using (just; nothing)
  open import Data.Maybe.Relation.Unary.Any using (just)
  open Core (p % s)

  strip : Dec (∃ λ 𝒓 → [] ⊢ ⊢p % ⊢s ＝ 𝒓)
  strip with run Countdown.begin [] ⊢p ⊢s refl refl
  ... | inj₁ (-, p%s , _) = yes (-, p%s)
  ... | inj₂ (-, ¬p%s)    = no  (¬p%s ∘ proj₂)

  finite-⊥⇒¬∃□ : [] ⊢ ⊢p % ⊢s ＝ nothing → ¬ ∃□ ⊢p
  finite-⊥⇒¬∃□ p%s = Soundness.Unknown.¬∃□ p%s

  finite-¬⊥⇒∃□ : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → ∃□ ⊢p
  finite-¬⊥⇒∃□ p%s with run Countdown.begin [] ⊢p ⊢s refl refl
  ... | inj₁ (just _  , _    , fin , _)    = If-just.drop-just fin
  ... | inj₁ (nothing , p%s′ , _   , uniq) = case uniq p%s of λ()
  ... | inj₂ (_ , ¬p%s)                    = contradiction p%s ¬p%s

  finite-¬∃□⇒⊥ : [] ⊢ ⊢p % ⊢s ＝ 𝒓 → ¬ ∃□ ⊢p → Is-nothing 𝒓
  finite-¬∃□⇒⊥ p%s ¬fin with run Countdown.begin [] ⊢p ⊢s refl refl
  ... | inj₁ (just _  , _ , fin , _) = contradiction (If-just.drop-just fin) ¬fin
  ... | inj₁ (nothing , _ , _   , u) rewrite PW.nothing-inv (u p%s) = nothing
  ... | inj₂ (_ , ¬p%s)              = contradiction p%s ¬p%s

  finite-∃□⇒¬⊥ : [] ⊢ ⊢p % ⊢s ＝ 𝒓 → ∃□ ⊢p → Is-just 𝒓
  finite-∃□⇒¬⊥ p%s fin with run Countdown.begin [] ⊢p ⊢s refl refl
  ... | inj₁ (just _ , _ , _ , u) rewrite PW.just-inv (u p%s) .proj₂ .proj₁ = just _
  ... | inj₁ (nothing , p%s′ , _) = contradiction fin (finite-⊥⇒¬∃□ p%s′)
  ... | inj₂ (_ , ¬p%s)           = contradiction p%s ¬p%s

  complete : ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → ∃ λ 𝒓 → [] ⊢ ⊢p % ⊢s ＝ 𝒓
  complete eq with run Countdown.begin [] ⊢p ⊢s refl refl
  ... | inj₁ (-, p%s , _) = -, p%s
  ... | inj₂ (p≰s , _) = contradiction eq p≰s

  complete-∃□ : ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → ∃□ ⊢p → [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r)
  complete-∃□ eq fin-p with complete eq
  ... | just (-, ⊢r′) , p%s =
    let eq′ = ≃-sym $ ◇≃◇-injective fin-p $ ≃-trans eq $ ≃-sym $ Soundness.Remainder.sound p%s in
    ⊢%-subst eq′ p%s
  ... | nothing , p%s = contradiction fin-p (finite-⊥⇒¬∃□ p%s)

  complete-¬∃□ : ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → ¬ ∃□ ⊢p → [] ⊢ ⊢p % ⊢s ＝ nothing
  complete-¬∃□ eq inf-p with complete eq
  ... | just (-, ⊢r′) , p%s = contradiction (finite-¬⊥⇒∃□ p%s) inf-p
  ... | nothing       , p%s = p%s

  sound-S : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound-S p%s = Soundness.Remainder.sound p%s

  sound-⊥ : [] ⊢ ⊢p % ⊢s ＝ nothing → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound-⊥ p%s = Soundness.Unknown.sound p%s

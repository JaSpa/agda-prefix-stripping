open import PrefixStripping.Prelude hiding (_⟨_⟩_)
open Relation.Binary

module PrefixStripping.Decide.Soundness
    {𝕋 END : Set}
    (_≟ᵀ_ : DecidableEquality 𝕋)
    (_≟E_ : DecidableEquality END)
  where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing; Is-nothing)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties

open import PrefixStripping.Syntax
open import PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_ as Universe

open import PrefixStripping.Sessions.Equivalence 𝕋 as Equivalence
open Equivalence.Tree
open Equivalence.Decide _≟ᵀ_ _≟E_

open Universe.Variables

infix 3 _⊢_%⁺_＝_

data _⊢_%⁺_＝_ (θ : List ⊢𝒰) : ⊢ p → ⊢ s → ⊢ℝ → Set where
  %-♯ : let H = ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s in
    H ∷ θ ⊢ ⊢p % ⊢s ＝ 𝒓 →
    θ ⊢ ⊢♯ ⁉ · T ▸ ⊢p %⁺ ⊢♯ ⁉ · T ▸ ⊢s ＝ 𝒓
  %-⋆ : let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    H ∷ θ ⊢ ⊢p₁ % ⊢s₁ ＝ 𝒓₁ →
    H ∷ θ ⊢ ⊢p₂ % ⊢s₂ ＝ 𝒓₂ →
    𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓 →
    θ ⊢ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ %⁺ ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ 𝒓

AllT : ∀ {A : Set} (R : REL A (List A) 0ℓ) → Pred (List A) 0ℓ
AllT R []       = ⊤
AllT R (a ∷ as) = R a as × AllT R as

allT-lookup : ∀ {A a as} {R : REL A (List A) 0ℓ} → AllT R as → a ∈ as → ∃ λ as′ → R a as′ × AllT R as′
allT-lookup (r-a  , r-as) (here refl) = -, r-a , r-as
allT-lookup (r-a′ , r-as) (there a∈)  = allT-lookup r-as a∈


module Unknown where
  ⟿⊥ : ⊢𝒰 → List ⊢𝒰 → Set
  ⟿⊥ (p % s) θ = θ ⊢ p %⁺ s ＝ nothing

  sound′ : AllT ⟿⊥ θ → θ ⊢ ⊢p % ⊢s ＝ nothing → ∀ {r} {⊢r : ⊢ r} → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound′ θ p%s zero = refl
  sound′ θ (%-♯ ∉θ p%s) (suc d) = cong (_ ♯ _ ▸_) (sound′ (%-♯ p%s , θ) p%s d)
  sound′ θ (%-⋆ ∉θ %₁ %₂ 𝒓⊔) (suc d) = cong₂ (_ ⟨_⨟_⟩)
      (sound′ (%-⋆ %₁ %₂ 𝒓⊔ , θ) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₁) %₁) d)
      (sound′ (%-⋆ %₁ %₂ 𝒓⊔ , θ) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₂) %₂) d)
  sound′ θ (%-μˡ {⊢p = p} {pᶜ} p%s) (suc d) = trans (≃-μ◇ p pᶜ _) (sound′ θ p%s (suc d))
  sound′ θ (%-μʳ {⊢s = s} {sᶜ} p%s) (suc d) = trans (sound′ θ p%s (suc d)) (sym (≃-μ s sᶜ _))
  sound′ θ (hyp ∈θ) (suc d) with allT-lookup θ ∈θ
  ... | -, %-♯ p%s      , θ′ = cong (_ ♯ _ ▸_) (sound′ (%-♯ p%s , θ′) p%s d)
  ... | -, %-⋆ %₁ %₂ 𝒓⊔ , θ′ = cong₂ (_ ⟨_⨟_⟩)
    (sound′ (%-⋆ %₁ %₂ 𝒓⊔ , θ′) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₁) %₁) d)
    (sound′ (%-⋆ %₁ %₂ 𝒓⊔ , θ′) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₂) %₂) d)

  sound : [] ⊢ ⊢p % ⊢s ＝ nothing → ∀ {r} {⊢r : ⊢ r} → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound = sound′ _

  ¬∃□-here : AllT ⟿⊥ θ → θ ⊢ ⊢p % ⊢s ＝ nothing → ⊢p ≄ ⊢□
  ¬∃□-here θ p%s eq with eq 1
  ¬∃□-here θ (%-μˡ {⊢p = p} {pᶜ} p%s) eq | ≡□ =
    ¬∃□-here θ p%s (≃-trans (≃-sym (≃-μ p pᶜ)) eq)
  ¬∃□-here θ (%-μʳ {⊢s = s} {sᶜ} p%s) eq | ≡□ =
    ¬∃□-here θ p%s eq
  ¬∃□-here θ (hyp ∈θ) eq | ≡□ with allT-lookup θ ∈θ
  ¬∃□-here θ (hyp ∈θ) eq | () | -, %-♯ p%s      , _
  ¬∃□-here θ (hyp ∈θ) eq | () | -, %-⋆ %₁ %₂ ⊔ᴿ , _

  ¬∃□′ : ∀ {⊢p : ⊢ p} →
    AllT ⟿⊥ θ →
    θ ⊢ ⊢p % ⊢s ＝ nothing →
    ∀ {s*} (π : Path s* p) → ⊢p –[ π ]→ ⊢□ → ⊥
  ¬∃□′ θ p%s {[]} π π→□ = ¬∃□-here θ p%s π→□
  ¬∃□′ θ (%-♯ _ p%s) {_ ∷ _} (step-♯ , π) π→□ =
    ¬∃□′ (%-♯ p%s , θ) p%s π π→□
  ¬∃□′ θ (%-⋆ {⁉ = ⁉} _ %₁ %₂ 𝒓⊔) {_ ∷ _} (step-⋆₁ , π) π→□ =
    ¬∃□′ (%-⋆ %₁ %₂ 𝒓⊔ , θ) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₁) %₁) π π→□
  ¬∃□′ θ (%-⋆ {⁉ = ⁉} _ %₁ %₂ 𝒓⊔) {_ ∷ _} (step-⋆₂ , π) π→□ =
    ¬∃□′ (%-⋆ %₁ %₂ 𝒓⊔ , θ) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₂) %₂) π π→□
  ¬∃□′ θ (%-μˡ {⊢p = p} {pᶜ} p%s) {_ ∷ _} π@(_ , _) π→□ =
    ¬∃□′ θ p%s (≃-path (≃-μ p pᶜ) π)
      (≃-trans (≃-sym (≃-target* (≃-μ p pᶜ) π)) π→□)
  ¬∃□′ θ (%-μʳ p%s) {_ ∷ _} π@(_ , _) π→□ =
    ¬∃□′ θ p%s π π→□
  ¬∃□′ θ (hyp ∈θ) {_ ∷ _} (x , π) π→□ with allT-lookup θ ∈θ
  ¬∃□′ θ (hyp ∈θ) {_ ∷ _} (step-♯  , π) π→□ | -, %⁺@(%-♯ p%s)      , θ′ =
    ¬∃□′ (%⁺ , θ′) p%s π π→□
  ¬∃□′ θ (hyp ∈θ) {_ ∷ _} (step-⋆₁ , π) π→□ | -, %⁺@(%-⋆ %₁ %₂ 𝒓⊔) , θ′ =
    ¬∃□′ (%⁺ , θ′) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₁) %₁) π π→□
  ¬∃□′ θ (hyp ∈θ) {_ ∷ _} (step-⋆₂ , π) π→□ | -, %⁺@(%-⋆ %₁ %₂ 𝒓⊔) , θ′ =
    ¬∃□′ (%⁺ , θ′) (⊢%-substᴿ (⊔ᴿ-nothing⁻¹ 𝒓⊔ .proj₂) %₂) π π→□

  ¬∃□ : [] ⊢ ⊢p % ⊢s ＝ nothing → ¬ ∃□ ⊢p
  ¬∃□ p%s (□ π π→□) = ¬∃□′ _ p%s π π→□

module Remainder where
  open import Data.Maybe.Relation.Binary.Pointwise using (just; nothing)

  infix 4 _wk≃_

  _wk≃_ : ⊢ r → ⊢ℝ → Set
  ⊢r wk≃ just (-, ⊢r′) = ⊢r ≃ ⊢r′
  ⊢r wk≃ nothing       = ⊤

  wk≃-⊔ᴿ : ⊢r wk≃ 𝒓 → 𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓 → ⊢r wk≃ 𝒓₁ × ⊢r wk≃ 𝒓₂
  wk≃-⊔ᴿ {𝒓 = just _}  eq (⊔-⊥ˡ (just eq′)) = _ , ≃-trans eq (≃-sym eq′)
  wk≃-⊔ᴿ {𝒓 = just _}  eq (⊔-⊥ʳ (just eq′)) = ≃-trans eq (≃-sym eq′) , _
  wk≃-⊔ᴿ {𝒓 = just _}  eq (⊔-≃  eq₁ eq₂)    = ≃-trans eq (≃-sym eq₁) , ≃-trans eq eq₂
  wk≃-⊔ᴿ {𝒓 = nothing} eq 𝒓⊔ with nothing , nothing ← ⊔ᴿ-nothing⁻¹ 𝒓⊔ = _

  ⟿_ : ⊢ r → ⊢𝒰 → List ⊢𝒰 → Set
  (⟿ r) (p % s) θ = ∃ λ 𝒓 → θ ⊢ p %⁺ s ＝ 𝒓 × r wk≃ 𝒓

  sound′ : AllT (⟿ ⊢r) θ → θ ⊢ ⊢p % ⊢s ＝ 𝒓 → ⊢r wk≃ 𝒓 → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s

  sound′-⋆ : ∀ {d} →
    AllT (⟿ ⊢r) θ →
    θ ⊢ ⊢p₁ % ⊢s₁ ＝ 𝒓₁ →
    θ ⊢ ⊢p₂ % ⊢s₂ ＝ 𝒓₂ →
    𝒓₁ ⊔ᴿ 𝒓₂ ＝ 𝒓 →
    ⊢r wk≃ 𝒓 →
    ⟦ ⊢[ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ ◇ ⊢r ] ⟧ (suc d) ≡ ⟦ ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ⟧ (suc d)

  sound′ θ p%s r-eq zero = refl
  sound′ θ (%-□ eq) r-eq = ≃-trans r-eq (≃-sym eq)
  sound′ θ (%-♯ ∉θ p%s) r-eq (suc d) =
    cong (_ ♯ _ ▸_) (sound′ ((-, %-♯ p%s , r-eq) , θ) p%s r-eq d)
  sound′ θ (%-⋆ ∉θ %₁ %₂ 𝒓⊔) r-eq (suc d) =
    let H = -, %-⋆ %₁ %₂ 𝒓⊔ , r-eq in
    sound′-⋆ (H , θ) %₁ %₂ 𝒓⊔ r-eq
  sound′ θ (%-μˡ {⊢p = p} {pᶜ} p%s) r-eq (suc d) = trans (≃-μ◇ p pᶜ _) (sound′ θ p%s r-eq (suc d))
  sound′ θ (%-μʳ {⊢s = s} {sᶜ} p%s) r-eq (suc d) = trans (sound′ θ p%s r-eq (suc d)) (sym (≃-μ s sᶜ (suc d)))
  sound′ θ (hyp ∈θ) r-eq (suc d) with allT-lookup θ ∈θ
  ... | -, ⟿@(r′ , %-♯ p%s , r-eq)      , θ′ = cong (_ ♯ _ ▸_) (sound′ (⟿ , θ′) p%s r-eq d)
  ... | -, ⟿@(r′ , %-⋆ %₁ %₂ 𝒓⊔ , r-eq) , θ′ = sound′-⋆ (⟿ , θ′) %₁ %₂ 𝒓⊔ r-eq

  sound′-⋆ θ %₁ %₂ 𝒓⊔ eq = cong₂ (_ ⟨_⨟_⟩)
    (sound′ θ %₁ (wk≃-⊔ᴿ eq 𝒓⊔ .proj₁) _)
    (sound′ θ %₂ (wk≃-⊔ᴿ eq 𝒓⊔ .proj₂) _)

  sound : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound p%s = sound′ _ p%s ≃-refl

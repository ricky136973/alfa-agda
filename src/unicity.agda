open import prelude
open import core
open import statics

module unicity where
  unicity : ∀ {Γ τ τ' e} → Γ ⊢ e :: τ → Γ ⊢ e :: τ' → τ ≡ τ'
  unicity T-NumLit T-NumLit = refl
  unicity (T-Neg _) (T-Neg _) = refl
  unicity (T-Plus _ _) (T-Plus _ _) = refl
  unicity (T-Minus _ _) (T-Minus _ _) = refl
  unicity (T-Times _ _) (T-Times _ _) = refl
  unicity (T-Lt _ _) (T-Lt _ _) = refl
  unicity (T-Gt _ _) (T-Gt _ _) = refl
  unicity (T-Eq _ _) (T-Eq _ _) = refl
  unicity T-True T-True = refl
  unicity T-False T-False = refl
  unicity (T-If _ _ D) (T-If _ _ D') = unicity D D'
  unicity (T-Var here) (T-Var here) = refl
  unicity (T-Var here) (T-Var (there H' _)) = absurd (H' refl)
  unicity (T-Var (there H _)) (T-Var here) = absurd (H refl)
  unicity (T-Var (there _ D)) (T-Var (there _ D')) = unicity (T-Var D) (T-Var D')
  unicity (T-LetAnn _ D) (T-LetAnn _ D') = unicity D D'
  unicity {_} {Arrow τᵢ _} {Arrow τᵢ _} (T-Fun D) (T-Fun D') =
    cong (Arrow τᵢ) (unicity D D')
  unicity (T-Ap D₁ _) (T-Ap D₁' _) =
    cong (λ {(Arrow _ τₒ) → τₒ; x → x}) (unicity D₁ D₁')

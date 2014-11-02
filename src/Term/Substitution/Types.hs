module Term.Substitution.Types where

import           Term.Synonyms

-- | The "context morphism" interpretation, and the "do stuff to term"
--   interpretation.
--
--   A substitution σ : Δ → Γ can be seen as a list of terms Γ ⊢ vᵢ : Aᵢ
--   with Aᵢ from Δ, that can be applied to a term Δ ⊢ u : B yielding
--   Γ ⊢ uσ : Bσ by substituting the vs for the variables in u. In other
--   words, if σ : Δ → Γ then applySubst σ : Term Δ -> Term Γ.
data Substitution t
  = Id
    --
    -- --------------------------------
    --   Id : Γ → Γ

  | Weaken !Int (Substitution t)
    --   ρ : Δ → Γ
    -- --------------------------------
    --   Weaken |Ψ| ρ : Δ → Γ;Ψ

  | Strengthen !Int (Substitution t)
    --   ρ : Δ → Γ
    -- --------------------------------
    --   Strengthen |Ψ| ρ : Γ;Ψ →  Δ

  | Instantiate (Term t) (Substitution t)
    --   Γ ⊢ u : Aρ    ρ : Δ → Γ
    -- --------------------------------
    --   Instantiate u ρ : Δ;A → Γ

  | Lift !Int (Substitution t)
    --   ρ : Δ → Γ
    -- --------------------------------
    --   Lift |Ψ| ρ : Δ;Ψ → Γ;Ψρ

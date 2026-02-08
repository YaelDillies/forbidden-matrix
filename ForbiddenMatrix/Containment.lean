module

public import Mathlib.Data.Fintype.Pi

@[expose] public section

variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

-- TODO: replace StrictMono f by StrictMonoOn {a ∣ ∃ b, P a b} f, and similarly for g to ignore
-- blank rows/columns
def Contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

instance {P : α → β → Prop} {M : γ → δ → Prop} [DecidableRel P] [DecidableRel M]
    [DecidableLT α] [DecidableLT β] [DecidableLT γ] [DecidableLT δ]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] : Decidable (Contains P M) :=
  inferInstanceAs <| Decidable <|
    ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

@[refl]
lemma contains_refl (M : γ → δ → Prop) : Contains M M :=
  ⟨id, by simp [StrictMono], id, by simp [StrictMono], by aesop⟩

lemma contains_rfl {M : γ → δ → Prop} : Contains M M := by rfl

@[simp] lemma contains_of_isEmpty [IsEmpty α] [IsEmpty β] : Contains P M := by
   simp [Contains, StrictMono]

lemma not_contains_false (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) :
    ¬ Contains P fun (_ : γ) (_ : δ) ↦ False := by simp [Contains, *]

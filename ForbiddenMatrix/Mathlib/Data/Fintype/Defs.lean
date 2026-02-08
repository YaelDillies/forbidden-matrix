module

public import Mathlib.Data.Fintype.Defs

public section

variable {α β : Type*} [LinearOrder α] [LinearOrder β] [Fintype α] [DecidableLT α] [DecidableLT β]
  {f : α → β}

instance : Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))
instance : Decidable (StrictAnti f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

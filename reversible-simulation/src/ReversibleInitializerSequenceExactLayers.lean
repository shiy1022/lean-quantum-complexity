import ReversibleInitializerSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {A : Type}

/-- Exact component counts sum over the actual sequence, using its preserved source frames. -/
theorem initializerSequence_map_layers (items : List A) (component : A → InitializationComponent)
    (layers : A → Nat) (n capacity : Nat)
    (counted : ∀ item ∈ items, ∀ cs ys,
      cs (.inl 0) = n → cs (.inl 2) = capacity →
      (component item).counters n cs ys (.inr 10) = cs (.inr 10) + layers item)
    (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceCounters (items.map component) n cs ys (.inr 10) =
      cs (.inr 10) + (items.map layers).sum := by
  induction items generalizing cs ys with
  | nil => simp [initializerSequenceCounters]
  | cons item rest ih =>
    simp only [List.map_cons, initializerSequenceCounters]
    rw [ih (fun a ha => counted a (by simp [ha]))
      ((component item).counters n cs ys) ((component item).output n cs ys)
      (by simpa only [(component item).metadata] using hn)
      (by simpa only [(component item).metadata] using hcap)]
    rw [counted item (by simp) cs ys hn hcap]
    simp only [List.sum_cons]
    omega

end ShiReversibleGenerator

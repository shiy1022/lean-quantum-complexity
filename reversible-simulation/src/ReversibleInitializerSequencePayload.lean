import ReversibleInitializerSequence

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A sequence prepends component payloads in reverse execution order, retaining the caller's bytes. -/
theorem initializerSequence_map_payload {A : Type} (items : List A)
    (component : A → InitializationComponent) (payload : A → List Bool) (n capacity : Nat)
    (houtput : ∀ a ∈ items, ∀ cs ys, cs (.inl 0) = n → cs (.inl 2) = capacity →
      (component a).output n cs ys = payload a ++ ys)
    (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceOutput (items.map component) n cs ys = items.reverse.flatMap payload ++ ys := by
  induction items generalizing cs ys with
  | nil => simp [initializerSequenceOutput]
  | cons a rest ih =>
      have ha := houtput a (by simp) cs ys hn hcap
      have hr := ih (fun b hb => houtput b (by simp [hb]))
        ((component a).counters n cs ys) ((component a).output n cs ys)
        (by simpa only [(component a).metadata] using hn)
        (by simpa only [(component a).metadata] using hcap)
      simp only [List.map_cons, initializerSequenceOutput]
      rw [hr, ha]
      simp [List.reverse_cons, List.flatMap_append, List.append_assoc]

end ShiReversibleGenerator

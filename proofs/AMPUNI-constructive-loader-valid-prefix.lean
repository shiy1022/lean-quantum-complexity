import «AMPUNI-constructive-loader-to-body»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private theorem iterTwo {A : Type} (f : A → A)
    (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega,
    Function.iterate_add_apply, hxy, hyz]

/-- From a raw valid unary prefix, the one integrated machine constructs
its counter and reaches the first source-machine call. -/
theorem valid_prefix_to_first_body
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (htrue : decodeInput (encodeInput true) = true)
    (hfalse : decodeInput (encodeInput false) = false)
    (n : Nat) (code : List (G input))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (v : Option Bool) (w : W)
    (hi : S (.inl input) =
      List.replicate n (encodeInput true) ++
        encodeInput false :: code)
    (h0 : S (.inr (ShiTMRepeatController.header false)) = [])
    (h1 : S (.inr (ShiTMRepeatController.header true)) = [])
    (hs : S (.inr ShiTMRepeatController.scratch) = [])
    (hc : S (.inr ShiTMRepeatController.counter) = []) :
    ∃ parity : Bool,
    ∃ S' : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[
            2 * n + 3 +
              (ShiTMUnaryLogCost.work (n + 1) + n + 3)]
        (some ⟨some scan, (v, (true, w)), S⟩) =
      some ⟨some (controller
        (ShiTMRepeatController.body false entry)),
        (none, (parity, w)), S'⟩ ∧
      S' (.inl input) =
        (List.replicate n true).map encodeInput ++
          encodeInput false :: code ∧
      S' (.inr (ShiTMRepeatController.header true)) = [] ∧
      S' (.inr (ShiTMRepeatController.header false)) =
        List.replicate n true ∧
      S' (.inr ShiTMRepeatController.scratch) = [] ∧
      S' (.inr ShiTMRepeatController.counter) =
        List.replicate
          (ShiQMAConstructiveSchedule.rounds p n - 1) true ∧
      (∀ j : K, j ≠ input → S' (.inl j) = S (.inl j)) := by
  obtain ⟨B, hstart, hBi, hBo⟩ :=
    startup_to_framed_loader p M entry terminal input output
      decodeInput decodeOutput encodeInput htrue hfalse
      n code S v w hi h0 h1 hs hc
  obtain ⟨parity, S', hbody, hi', hh1', hh0', hs', hc', ho'⟩ :=
    loader_to_first_body p M entry terminal input output
      decodeInput decodeOutput encodeInput n
      (fun j => B (.inl j)) w
  refine ⟨parity, S', ?_, ?_, hh1', hh0', hs', hc', ?_⟩
  · exact iterTwo
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))
      _ _ _ _ _ hstart hbody
  · simpa [hBi] using hi'
  · intro j hj
    rw [ho' j hj, hBo j hj]

/-- Counter construction and entry into the first round cost linear time
in the unary input length. -/
theorem valid_prefix_cost_le (n : Nat) :
    2 * n + 3 +
      (ShiTMUnaryLogCost.work (n + 1) + n + 3) ≤
        7 * n + 14 := by
  have h := ShiTMUnaryLogCost.work_le_linear (n + 1)
  omega

end ShiTMConstructiveIntegrated

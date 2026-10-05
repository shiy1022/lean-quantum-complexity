import Definitions.Def_ShiClassQMAAmpX

set_option autoImplicit false

open ShiShallow

namespace ShiTMCircuitNormalization

/-- The layer payload of a length-prefixed circuit encoding. -/
def payload {N : Nat} (c : Layered N) : PvsNP.Str :=
  (c.map ShiBQP.encLayer).flatten

/-- The final output needs each verifier copy's payload, not its individual
circuit-depth prefix. -/
def stripCircPrefix {N : Nat} (c : Layered N) : PvsNP.Str :=
  (ShiBQP.encCirc c).drop (c.length + 1)

theorem stripCircPrefix_eq_payload {N : Nat} (c : Layered N) :
    stripCircPrefix c = payload c := by
  have hlen : (ShiBQP.encNat c.length).length = c.length + 1 := by
    simp [ShiBQP.encNat]
  unfold stripCircPrefix payload ShiBQP.encCirc ShiBQP.encStr
  rw [← hlen]
  simp

/-- Exact bit-string normalization specification for the six circuit blocks:
replace their six local depth prefixes by one global depth prefix. -/
theorem six_block_normalization {N : Nat} (a b c d e f : Layered N) :
    ShiBQP.encCirc (a ++ b ++ c ++ d ++ e ++ f) =
      ShiBQP.encNat
        (a.length + b.length + c.length + d.length + e.length + f.length) ++
      stripCircPrefix a ++ stripCircPrefix b ++ stripCircPrefix c ++
      stripCircPrefix d ++ stripCircPrefix e ++ stripCircPrefix f := by
  simp only [stripCircPrefix_eq_payload]
  simp [payload, ShiBQP.encCirc, ShiBQP.encStr, List.map_append,
    List.flatten_append, List.length_append, List.append_assoc, Nat.add_assoc]

end ShiTMCircuitNormalization

import «AMPUNI-output-entry-parser-lift»
import «AMPUNI-nested-layer»

set_option autoImplicit false

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

def baseStacks (S : ∀ k, List (TopGam k)) :
    ∀ k, List (Gam k) :=
  fun k => S (.inl (.inl k))

def counterStacks (S : ∀ k, List (TopGam k)) : Fin 2 → List Cell :=
  fun k => S (.inl (.inr k))

def headerStacks (S : ∀ k, List (TopGam k)) : Fin 4 → List Cell :=
  fun k => S (.inr k)

/-- Every top-level stack configuration is exactly the nested parser's
base/counter configuration plus the four retained unary headers. -/
theorem stack_split (S : ∀ k, List (TopGam k)) :
    topStacks (liftStacks (baseStacks S) (counterStacks S))
      (headerStacks S) = S := by
  funext k
  cases k with
  | inl k =>
      cases k <;> rfl
  | inr k => rfl

end ShiTMOutputEntry

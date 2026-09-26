/- Issue #532: 35_exact_compression. General lemma or countermodel only; see RESEARCH_LOG.md. -/
namespace Issue532.Idea35
theorem tested {X Code : Type} (encode : X → Code) (decode : Code → X)
    (roundTrip : ∀ x, decode (encode x) = x) :
    Function.Injective encode := by
  intro x y equalCode
  calc
    x = decode (encode x) := (roundTrip x).symm
    _ = decode (encode y) := congrArg decode equalCode
    _ = y := roundTrip y
end Issue532.Idea35

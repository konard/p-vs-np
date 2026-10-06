import proofs.experiments.issue624.lean.SuccessorCNF

open Complexity Issue532.Machines Issue624.SuccessorCNF

private def machine : Machine :=
  ⟨[[.move 0 .one .right, .move 0 .one .right,
     .move 0 .one .right, .halt false]]⟩
private def before : Config := ⟨0, [.blank], .zero, [.blank]⟩
private def after : Config := moveHead before 0 .one .right
private def wrongWrite : Config := moveHead before 0 .zero .right
private def assignment (d : Config) : Assignment :=
  fun v => rowAssignment 0 1 3 before v || rowAssignment 20 1 3 d v

example : evalCNF (assignment after) (successorCNF machine 0 20 3) = true := by decide
example : evalCNF (assignment wrongWrite) (rowCNF 0 1 3 ++ rowCNF 20 1 3) = true := by decide
example : evalCNF (assignment wrongWrite) (successorCNF machine 0 20 3) = false := by decide
example : evalCNF (assignment before) (successorCNF machine 0 20 3) = false := by decide
example : (encodeCNF (successorCNF machine 0 20 3)).length ≤
    successorSize machine 0 20 3 := successorCNF_encoded_size _ _ _ _

example : flatten (moveHead before 0 .one .left) = (flatten before).set before.left.length .one := by decide
example : flatten (moveHead before 0 .one .stay) = (flatten before).set before.left.length .one := by decide
example : evalCNF (assignment after) (successorCNF ⟨[[]]⟩ 0 20 3) = false := by decide

private def edge : Config := ⟨0, [], .zero, [.blank, .blank]⟩
private def leftMachine : Machine := ⟨[[.move 0 .one .left, .move 0 .one .left]]⟩
example : step leftMachine edge = Sum.inr (moveHead edge 0 .one .left) := by rfl
-- The two-way step grows beyond this represented window; it must not wrap.
example : evalCNF (fun v => rowAssignment 0 1 3 edge v || rowAssignment 20 1 3 before v)
    (successorCNF leftMachine 0 20 3) = false := by decide

private def directionMachine (dir : Direction) : Machine :=
  ⟨[[.move 0 .one dir, .move 0 .one dir, .move 0 .one dir, .move 0 .one dir]]⟩
example : evalCNF (assignment (moveHead before 0 .one .left))
    (successorCNF (directionMachine .left) 0 20 3) = true := by decide
example : evalCNF (assignment (moveHead before 0 .one .stay))
    (successorCNF (directionMachine .stay) 0 20 3) = true := by decide

private def wrongCopy : Config := ⟨0, [.one, .one], .blank, []⟩
example : evalCNF (assignment wrongCopy) (rowCNF 0 1 3 ++ rowCNF 20 1 3) = true := by decide
example : evalCNF (assignment wrongCopy) (successorCNF machine 0 20 3) = false := by decide
example : decodeRow (rowAssignment 0 1 3 before) 0 1 3 = before := by rfl
example : evalCNF (fun _ => false) (rowCNF 0 1 3) = false := by decide
example : evalCNF (fun _ => true) (rowCNF 0 1 3) = false := by decide
example : evalCNF (assignment after) (successorCNF ⟨[]⟩ 0 20 3) = false := by decide
example : evalCNF (assignment after) (successorCNF machine 0 20 0) = false := by decide
example : evalCNF (assignment after)
    (successorCNF ⟨[[.halt true, .halt true, .halt true, .halt true]]⟩ 0 20 3) = false := by decide
example : evalCNF (assignment after)
    (successorCNF ⟨[[.move 1 .one .right, .move 1 .one .right]]⟩ 0 20 3) = false := by decide

private def twoStates : Machine := ⟨[[.move 1 .one .right, .move 1 .one .right], [.halt true]]⟩
private def assignmentTwo (d : Config) : Assignment :=
  fun v => rowAssignment 0 2 3 before v || rowAssignment 20 2 3 d v
example : evalCNF (assignmentTwo (moveHead before 1 .one .right))
    (successorCNF twoStates 0 20 3) = true := by decide
example : evalCNF (assignmentTwo after) (rowCNF 0 2 3 ++ rowCNF 20 2 3) = true := by decide
example : evalCNF (assignmentTwo after) (successorCNF twoStates 0 20 3) = false := by decide

private def rightEdge : Config := ⟨0, [.blank, .blank], .zero, []⟩
example : evalCNF (fun v => rowAssignment 0 1 3 rightEdge v || rowAssignment 20 1 3 before v)
    (successorCNF machine 0 20 3) = false := by decide

#print axioms rowAssignment_represents
#print axioms rowCNF_models
#print axioms decodeRow_represents
#print axioms moveHead_matches
#print axioms transitionCNF_step
#print axioms successorCNF_models
#print axioms successorCNF_sound
#print axioms successorCNF_decoded_wrong_successor
#print axioms successorCNF_encoded_size

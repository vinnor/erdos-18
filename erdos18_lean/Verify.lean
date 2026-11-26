import Erdos18

theorem check_statement :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 5 :=
  Erdos18.erdos18_alpha5

#print axioms check_statement

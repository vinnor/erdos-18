import Erdos18

theorem check_alpha5 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 5 :=
  Erdos18.erdos18_alpha5

theorem check_alpha4 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 4 :=
  Erdos18.erdos18_alpha4

theorem check_alpha3_loglog2 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : _root_.Real) ≤
          C * (_root_.Real.log n) ^ 3 * (_root_.Real.log (_root_.Real.log ((n : _root_.Real) + 16))) ^ 2 :=
  Erdos18.erdos18_alpha3_loglog2

theorem check_alpha3_loglog1 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : _root_.Real) ≤
          C * (_root_.Real.log n) ^ 3 * _root_.Real.log (_root_.Real.log ((n : _root_.Real) + 16)) :=
  Erdos18.erdos18_alpha3_loglog1

#print axioms check_alpha5
#print axioms check_alpha4
#print axioms check_alpha3_loglog2
#print axioms check_alpha3_loglog1

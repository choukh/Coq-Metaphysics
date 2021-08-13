(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Modal.

Parameter 实体 : Type.
Definition 性质 := 泛性质 实体.

Definition 反性质 : 性质 → 性质 := λ Φ x, ¬ Φ x.
Notation "'反' P" := (反性质 P) (at level 65, right associativity) : modal_scope.

Definition 同一性 : 性质 := λ x, x = x.
Definition 反同一性 : 性质 := 反 同一性.

(* P一致，当且仅当可能存在实体具有P *)
Definition 一致 : 泛性质 性质 := λ Φ, ◇ ∃ x, Φ x.

(* P是共性，当且仅当必然任意实体具有P *)
Definition 共性 : 泛性质 性质 := λ Φ, □ ∀ x, Φ x.

Fact 同一性是共性 : ⌈共性 同一性⌋.
Proof. firstorder. Qed.

Fact 反同一性不一致 : ⌈¬ 一致 反同一性⌋.
Proof. firstorder. Qed.

(* Φ严格蕴含Ψ（Ψ是Φ的必然后果），当且仅当必然对任意实体x，x具有Φ蕴含x具有Ψ *)
Definition 严格蕴含 : 关系 性质 := λ Φ Ψ, □ (∀ x, Φ x → Ψ x).
Infix "⇒" := 严格蕴含 (at level 75).

(* Φ与Ψ严格等价，当且仅当必然对任意实体x，x具有Φ等价于x具有Ψ *)
Definition 严格等价 : 关系 性质 := λ Φ Ψ, □ (∀ x, Φ x ↔ Ψ x).
Infix "⇔" := 严格等价 (at level 70).

Theorem 爆炸原理 : ⌈∀ Φ Ψ, ¬ 一致 Φ → Φ ⇒ Ψ⌋.
Proof. firstorder. Qed.

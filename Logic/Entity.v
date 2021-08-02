(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Modal.

Parameter 实体 : Type.

Definition 性质 := 性质 实体.

Definition 恒真 : 性质 := λ x, x = x.

Definition 恒假 : 性质 := λ x, x ≠ x.

Definition 非 : 性质 → 性质 := λ P x, ¬ P x.

(* P一致，当且仅当可能存在实体具有P *)
Definition 一致 : 性质 → 命题 := λ P, ◇ ∃ x, P x.

(* P是共性，当且仅当必然任意实体具有P *)
Definition 共性 : 性质 → 命题 := λ P, □ ∀ x, P x.

Theorem 恒真是共性 : ⌜ 共性 恒真 ⌝.
Proof. firstorder. Qed.

Theorem 恒假不一致 : ⌜ ¬ 一致 恒假 ⌝.
Proof. firstorder. Qed.

(* P严格蕴含Q（Q是P的必然后果），当且仅当必然对任意实体x，x具有P蕴含x具有Q *)
Definition 严格蕴含 : 性质 → 性质 → 命题 := λ P Q, □ (∀ x, P x → Q x).
Infix "⇒" := 严格蕴含 (at level 190).

(* P与Q严格等价，当且仅当必然对任意实体x，x具有P等价于x具有Q *)
Definition 严格等价 : 性质 → 性质 → 命题 := λ P Q, □ (∀ x, P x ↔ Q x).
Infix "⇔" := 严格等价 (at level 180).

Theorem 爆炸原理 : ⌜ ∀ P Q, ¬ 一致 P → P ⇒ Q ⌝.
Proof. firstorder. Qed.

(** Coq coding by choukh, Aug 2021 **)

Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.

Parameter 在场 : 实体 → 世界 → Prop.
Notation "x ∈ w" := (  在场 x w) (at level 70).
Notation "x ∉ w" := (¬ 在场 x w) (at level 70).

Axiom 全局论域非空 : ∀ w, ∃ x, x ∈ w.

Definition 在场全称量词 : 泛性质 性质 :=
  λ Φ w, (∀ x, x ∈ w → Φ x w)%t.

Notation "∀ᴱ x .. y , Φ" :=
  (在场全称量词 (λ x, .. (在场全称量词 (λ y, Φ)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ᴱ  x .. y ']' ,  '/' Φ ']'") : modal_scope.

Definition 在场存在量词 : 泛性质 性质 :=
  λ Φ w, (∃ x, x ∈ w ∧ Φ x w)%t.

Notation "∃ᴱ x .. y , Φ" :=
  (在场存在量词 (λ x, .. (在场存在量词 (λ y, Φ)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ᴱ  x .. y ']' ,  '/' Φ ']'") : modal_scope.

(* P在场一致，当且仅当可能存在在场实体具有P *)
Definition 在场一致 : 泛性质 性质 := λ Φ, ◇ ∃ᴱ x, Φ x.

(* P是在场共性，当且仅当必然任意在场实体具有P *)
Definition 在场共性 : 泛性质 性质 := λ Φ, □ ∀ᴱ x, Φ x.

Fact 同一性是在场共性 : ⌈在场共性 同一性⌋.
Proof. firstorder. Qed.

Fact 反同一性不在场一致 : ⌈¬ 在场一致 反同一性⌋.
Proof. firstorder. Qed.

(* Φ在场严格蕴含Ψ（Ψ是Φ的在场必然后果），当且仅当必然对任意在场实体x，x具有Φ蕴含x具有Ψ *)
Definition 在场严格蕴含 : 关系 性质 := λ Φ Ψ, □ (∀ᴱ x, Φ x → Ψ x).
Infix "⟹" := 在场严格蕴含 (at level 75).

(* Φ与Ψ在场严格等价，当且仅当必然对任意在场实体x，x具有Φ等价于x具有Ψ *)
Definition 在场严格等价 : 关系 性质 := λ Φ Ψ, □ (∀ᴱ x, Φ x ↔ Ψ x).
Infix "⟺" := 在场严格等价 (at level 70).

Theorem 在场爆炸原理 : ⌈∀ Φ Ψ, ¬ 在场一致 Φ → Φ ⟹ Ψ⌋.
Proof. firstorder. Qed.

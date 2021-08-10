(** Coq coding by choukh, Aug 2021 **)

Require Export Coq.Unicode.Utf8_core.
Require Import Coq.Classes.RelationClasses.
Require Import CM.Logic.Classical.

Declare Scope modal_scope.
Delimit Scope modal_scope with m.
Delimit Scope type_scope with t.
Open Scope modal_scope.

Inductive 世界 : Type := | w₁ | w₂.
Inductive 实体 : Type := | a | b.

Inductive 在场 : 实体 → 世界 → Prop :=
  | a₁ : 在场 a w₁
  | b₁ : 在场 b w₁
  | a₂ : 在场 a w₂.

Notation "x ∈ w" := (  在场 x w) (at level 70).
Notation "x ∉ w" := (¬ 在场 x w) (at level 70).

Reserved Notation "u '𝗥' v" (at level 70).

Inductive 可及关系 : 世界 → 世界 → Prop :=
  | 自反1 : w₁ 𝗥 w₁
  | 自反2 : w₂ 𝗥 w₂
  | 对称1 : w₁ 𝗥 w₂
  | 对称2 : w₂ 𝗥 w₁
where "u '𝗥' v" := (可及关系 u v) : modal_scope.

Definition 命题 := 世界 → Prop.
Definition 泛性质 (A : Type) := A → 命题.
Definition 关系 (A : Type) := A → A → 命题.

Definition 可证 : 命题 → Prop := λ P, ∀ w, P w.
Notation "⌈ P ⌋" := (可证 P) (format "⌈ P ⌋") : modal_scope.
Ltac 证明 := match goal with [|- ⌈_⌋] => intro end.

(* “必然P”在w中为真，当且仅当在所有可及于w的世界中P为真 *)
Definition 必然 : 泛性质 命题 := λ P w, ∀ w', w 𝗥 w' → P w'.
Notation "□ P" := (必然 P) (at level 75, right associativity).

Ltac 必入 := let w := fresh "w" in let R := fresh "R" in
  (intro w at top; intro R at top).

Ltac 预必除1 H w' H' := match type of H with
  ((必然 ?p) ?w) => cut (p w');
    [intros H' | (apply (H w'); try assumption)] end.

Ltac 预必除2 H H':= match goal with
  | [|- (_ ?w) ] => 预必除1 H w H' end.

Tactic Notation "必除" ident(H) ident(w') ident(H') := 预必除1 H w' H'.
Tactic Notation "必除" ident(H) ident(H') := 预必除2 H H'.

(* “可能P”在w中为真，当且仅当在某些可及于w的世界中P为真 *)
Definition 可能 : 泛性质 命题 := λ P w, ∃ w', w 𝗥 w' ∧ P w'.
Notation "◇ P" := (可能 P) (at level 75, right associativity).

Ltac 可入 w := (exists w; split; [try assumption | idtac]).

Ltac 预可除 H := let w := fresh "w" in let R := fresh "R" in
  (destruct H as [w [R H]]; move w at top; move R at top).

Tactic Notation "可除" ident(H) := 预可除 H.
Tactic Notation "可除" ident(H) "as" simple_intropattern(L) := 预可除 H; destruct H as L.

Definition 否定 : 泛性质 命题 := λ P w, ¬ P w.
Notation "¬ P" := (否定 P) : modal_scope.

Definition 合取 : 关系 命题 := λ P Q w, P w ∧ Q w.
Infix "∧" := 合取 : modal_scope.

Definition 析取 : 关系 命题 := λ P Q w, P w ∨ Q w.
Infix "∨" := 析取 : modal_scope.

Definition 蕴含 : 关系 命题 := λ P Q w, P w → Q w.
Infix "→" := 蕴含 : modal_scope.

Definition 等价 : 关系 命题 := λ P Q w, P w ↔ Q w.
Infix "↔" := 等价 : modal_scope.

Definition 相等 {A : Type} : 关系 A := λ x y w, x = y.
Infix "=" := 相等 : modal_scope.
Notation "x ≠ y" := (¬ x = y) : modal_scope.

Definition 全称量词 {A : Type} : 泛性质 A → 命题 :=
  λ Φ w, ∀ x, Φ x w.

Notation "∀ x .. y , Φ" :=
  (全称量词 (λ x, .. (全称量词 (λ y, Φ)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀  x .. y ']' ,  '/' Φ ']'") : modal_scope.

Definition 存在量词 {A : Type} : 泛性质 A → 命题 :=
  λ Φ w, ∃ x, Φ x w.

Notation "∃ x .. y , Φ" :=
  (存在量词 (λ x, .. (存在量词 (λ y, Φ)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃  x .. y ']' ,  '/' Φ ']'") : modal_scope.

Theorem 可能性三段论 : ⌈∀ P Q, ◇ P → □ (P → Q) → ◇ Q⌋.
Proof. firstorder. Qed.

Theorem 必然即不可非 : ⌈∀ P, □ P ↔ ¬ ◇ ¬ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros H. 必入. 反证. apply H. now 可入 w0.
Qed.

Theorem 必非即不可能 : ⌈∀ P, □ ¬ P ↔ ¬ ◇ P⌋.
Proof. firstorder. Qed.

Theorem 可能即不必非 : ⌈∀ P, ◇ P ↔ ¬ □ ¬ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros. 反证. firstorder.
Qed.

Theorem 可非即不必然 : ⌈∀ P, ◇ ¬ P ↔ ¬ □ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros. 反证. apply H. 必入. 反证. apply 反设. now 可入 w0.
Qed.

Theorem 必然性规则 : ∀ P, ⌈P⌋ → ⌈□ P⌋.
Proof. firstorder. Qed.
Notation 𝗡 := 必然性规则.

Theorem 分配律公理 : ⌈∀ P Q, □ (P → Q) → (□ P → □ Q)⌋.
Proof. firstorder. Qed.
Notation 𝗞 := 分配律公理.

Theorem 可能性分配原理 : ⌈∀ P Q, □ (P → Q) → (◇ P → ◇ Q)⌋.
Proof. firstorder. Qed.
Notation 𝗞' := 可能性分配原理.

Theorem 𝗧 : ⌈∀ P, □ P → P⌋.
Proof.
  证明. intros P H.
  destruct w; 必除 H H'; auto; constructor.
Qed.

Theorem 𝗗 : ⌈∀ P, □ P → ◇ P⌋.
Proof.
  证明. intros P H.
  destruct w; 必除 H H'; try constructor;
  [可入 w₁|可入 w₂]; auto; constructor.
Qed.

Theorem 𝗕 : ⌈∀ P, P → □ ◇ P⌋.
Proof.
  证明. intros P H. 必入.
  destruct w; destruct w0.
  - 可入 w₁; auto.
  - 可入 w₁; auto. constructor.
  - 可入 w₂; auto. constructor.
  - 可入 w₂; auto.
Qed.

Theorem 布劳威尔归结 : ⌈∀ P, ◇ □ P → P⌋.
Proof.
  证明. intros P H. 可除 H.
  destruct w; destruct w0;
  apply H; constructor.
Qed.
Notation 𝗕归结 := 布劳威尔归结.

Definition 性质 := 泛性质 实体.
Definition 反性质 : 性质 → 性质 := λ Φ x, ¬ Φ x.
Notation "'反' P" := (反性质 P) (at level 65, right associativity) : modal_scope.

Definition 同一性 : 性质 := λ x, x = x.
Definition 反同一性 : 性质 := 反 同一性.

(* P一致，当且仅当可能存在实体具有P *)
Definition 一致 : 泛性质 性质 := λ Φ, ◇ ∃ x, Φ x.

(* P是共性，当且仅当必然任意实体具有P *)
Definition 共性 : 泛性质 性质 := λ Φ, □ ∀ x, Φ x.

(* Φ严格蕴含Ψ（Ψ是Φ的必然后果），当且仅当必然对任意实体x，x具有Φ蕴含x具有Ψ *)
Definition 严格蕴含 : 关系 性质 := λ Φ Ψ, □ (∀ x, Φ x → Ψ x).
Infix "⇒" := 严格蕴含 (at level 75).

(* Φ与Ψ严格等价，当且仅当必然对任意实体x，x具有Φ等价于x具有Ψ *)
Definition 严格等价 : 关系 性质 := λ Φ Ψ, □ (∀ x, Φ x ↔ Ψ x).
Infix "⇔" := 严格等价 (at level 70).

Theorem 爆炸原理 : ⌈∀ Φ Ψ, ¬ 一致 Φ → Φ ⇒ Ψ⌋.
Proof. firstorder. Qed.

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

(* Φ在场严格蕴含Ψ（Ψ是Φ的在场必然后果），当且仅当必然对任意在场实体x，x具有Φ蕴含x具有Ψ *)
Definition 在场严格蕴含 : 关系 性质 := λ Φ Ψ, □ (∀ᴱ x, Φ x → Ψ x).
Infix "⟹" := 在场严格蕴含 (at level 75).

(* Φ与Ψ在场严格等价，当且仅当必然对任意在场实体x，x具有Φ等价于x具有Ψ *)
Definition 在场严格等价 : 关系 性质 := λ Φ Ψ, □ (∀ᴱ x, Φ x ↔ Ψ x).
Infix "⟺" := 在场严格等价 (at level 70).

Theorem 在场爆炸原理 : ⌈∀ Φ Ψ, ¬ 在场一致 Φ → Φ ⟹ Ψ⌋.
Proof. firstorder. Qed.

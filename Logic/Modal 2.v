(** Coq coding by choukh, July 2021 **)

Require Export Coq.Unicode.Utf8_core.
Require Import Coq.Classes.RelationClasses.
Require CM.Logic.Classical.

Declare Scope modal_scope.
Delimit Scope modal_scope with m.
Delimit Scope type_scope with t.
Open Scope modal_scope.

Parameter 世界 : Type.
Axiom 存在世界 : inhabited 世界.

Parameter 可及关系 : 世界 → 世界 → Prop.
Infix "𝗥" := 可及关系 (at level 70) : modal_scope.

Definition 命题 := 世界 → Prop.
Definition 泛性质 (A : Type) := A → 命题.
Definition 关系 (A : Type) := A → A → 命题.

Definition 可证 : 命题 → Prop := λ P, ∀ w, P w.
Notation "⌈ P ⌋" := (可证 P) (format "⌈ P ⌋") : modal_scope.
Ltac 证明 := match goal with [|- ⌈_⌋] => intro end.

Definition 恒真 : 命题 := λ _, True.
Definition 恒假 : 命题 := λ _, False.

Fact 恒真同构 : ⌈恒真⌋ ↔ True.
Proof. firstorder. Qed.

Fact 恒假同构 : ⌈恒假⌋ ↔ False.
Proof. destruct 存在世界 as [w]. firstorder. Qed.

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

Theorem 必然性规则 : ∀ P, ⌈P⌋ → ⌈□ P⌋.
Proof. firstorder. Qed.
Notation 𝗡 := 必然性规则.

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

Fact 否定投射 : ∀ P : 命题, ⌈¬ P⌋ → ¬ ⌈P⌋.
Proof. destruct 存在世界 as [w]. firstorder. Qed.

Fact 合取同构 : ∀ P Q : 命题, ⌈P ∧ Q⌋ ↔ ⌈P⌋ ∧ ⌈Q⌋.
Proof. firstorder. Qed.

Fact 析取嵌入 : ∀ P Q : 命题, ⌈P⌋ ∨ ⌈Q⌋ → ⌈P ∨ Q⌋.
Proof. firstorder. Qed.

Fact 蕴含投射 : ∀ P Q : 命题, ⌈P → Q⌋ → ⌈P⌋ → ⌈Q⌋.
Proof. firstorder. Qed.

Fact 等价投射 : ∀ P Q : 命题, ⌈P ↔ Q⌋ → ⌈P⌋ ↔ ⌈Q⌋.
Proof. firstorder. Qed.

Fact 相等同构 {A : Type} : ∀ x y : A, ⌈x = y⌋ ↔ x = y.
Proof. destruct 存在世界 as [w]. firstorder. Qed.

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

Fact 全称量词同构 {A : Type} : ∀ Φ : 泛性质 A,
  ⌈∀ x, Φ x⌋ ↔ ∀ x, ⌈Φ x⌋.
Proof. firstorder. Qed.

Fact 存在量词嵌入 {A : Type} : ∀ Φ : 泛性质 A,
  (∃ x, ⌈Φ x⌋) → ⌈∃ x, Φ x⌋.
Proof. firstorder. Qed.

Fact 必然则不可非 : ⌈∀ P, □ P → ¬ ◇ ¬ P⌋.
Proof. firstorder. Qed.

Fact 必非即不可能 : ⌈∀ P, □ ¬ P ↔ ¬ ◇ P⌋.
Proof. firstorder. Qed.

Fact 可能则不必非 : ⌈∀ P, ◇ P → ¬ □ ¬ P⌋.
Proof. firstorder. Qed.

Fact 可非则不必然 : ⌈∀ P, ◇ ¬ P → ¬ □ P⌋.
Proof. firstorder. Qed.

Module Classical.
Import CM.Logic.Classical.

Fact 必然即不可非 : ⌈∀ P, □ P ↔ ¬ ◇ ¬ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros H. 必入. 反证. apply H. now 可入 w0.
Qed.

Fact 可能即不必非 : ⌈∀ P, ◇ P ↔ ¬ □ ¬ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros. 反证. firstorder.
Qed.

Fact 可非即不必然 : ⌈∀ P, ◇ ¬ P ↔ ¬ □ P⌋.
Proof.
  证明. intros P. split. firstorder.
  intros. 反证. apply H. 必入. 反证. apply 反设. now 可入 w0.
Qed.

End Classical.

(** 框架条件与层级系统 **)

Module Export K.
  (* 无框架条件 *)
  
  Theorem 必然性分配律 : ⌈∀ P Q, □ (P → Q) → (□ P → □ Q)⌋.
  Proof. firstorder. Qed.
  Notation 𝗞 := 必然性分配律.

  Theorem 可能性分配律 : ⌈∀ P Q, □ (P → Q) → (◇ P → ◇ Q)⌋.
  Proof. firstorder. Qed.
  Notation 𝗞' := 可能性分配律.

  Theorem 必然性三段论 : ⌈∀ P Q, □ P → □ (P → Q) → □ Q⌋.
  Proof. firstorder. Qed.

  Theorem 可能性三段论 : ⌈∀ P Q, ◇ P → □ (P → Q) → ◇ Q⌋.
  Proof. firstorder. Qed.
End K.

Module KT.
  Axiom 自反框架 : Reflexive 可及关系.

  Theorem 𝗧 : ⌈∀ P, □ P → P⌋.
  Proof. firstorder using 自反框架. Qed.

  Theorem 𝗗 : ⌈∀ P, □ P → ◇ P⌋.
  Proof. firstorder using 自反框架. Qed.
End KT.

Module KB.
  Axiom 对称框架 : Symmetric 可及关系.

  Theorem 𝗕 : ⌈∀ P, P → □ ◇ P⌋.
  Proof. firstorder using 对称框架. Qed.

  Theorem 布劳威尔归结 : ⌈∀ P, ◇ □ P → P⌋.
  Proof. firstorder using 对称框架. Qed.
  Notation 𝗕归结 := 布劳威尔归结.
End KB.

Module K4.
  Axiom 传递框架 : Transitive 可及关系.

  Theorem 四 : ⌈∀ P, □ P → □ □ P⌋.
  Proof. firstorder using 传递框架. Qed.
  Notation "𝟰" := 四.
End K4.

Module B.
  Export KT.
  Export KB.
End B.

Module K4B.
  Export K4.
  Export KB.

  Fact 部分等价关系框架 : PER 可及关系.
  Proof. firstorder using 对称框架, 传递框架. Qed.

  Theorem 迭代原理 : ⌈∀ P, ◇ □ P → □ P⌋.
  Proof. firstorder using 部分等价关系框架. Qed.
  Notation "𝟰𝗕" := 迭代原理.
End K4B.

Module S4.
  Export KT.
  Export K4.

  Fact 预序框架 : PreOrder 可及关系.
  Proof. firstorder using 自反框架, 传递框架. Qed.
End S4.

Module S5.
  Export KB.
  Export K4B.
  Export S4.

  Fact 等价关系框架 : Equivalence 可及关系.
  Proof. firstorder using 自反框架, 对称框架, 传递框架. Qed.
  Existing Instance 等价关系框架.

  Theorem 五 : ⌈∀ P, ◇ P → □ ◇ P⌋.
  Proof. firstorder using 等价关系框架. Qed.
  Notation "𝟱" := 五.
End S5.

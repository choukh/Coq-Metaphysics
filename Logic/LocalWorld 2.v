(** Coq coding by choukh, Aug 2021 **)

Require Import CM.Logic.Modal.

Parameter 本地 : 世界.
Notation w₀ := 本地.

Definition 本地可证 : 命题 → Prop := λ P, P w₀.
Notation "⌜ P ⌟" := (本地可证 P) (format "⌜ P ⌟") : modal_scope.

Fact 本地恒真同构 : ⌜恒真⌟ ↔ True.
Proof. firstorder. Qed.

Fact 本地恒假同构 : ⌜恒假⌟ ↔ False.
Proof. firstorder. Qed.

Fact 本地否定同构 : ∀ P : 命题, ⌜¬ P⌟ ↔ ¬ ⌜P⌟.
Proof. firstorder. Qed.

Fact 本地合取同构 : ∀ P Q : 命题, ⌜P ∧ Q⌟ ↔ ⌜P⌟ ∧ ⌜Q⌟.
Proof. firstorder. Qed.

Fact 本地析取同构 : ∀ P Q : 命题, ⌜P⌟ ∨ ⌜Q⌟ ↔ ⌜P ∨ Q⌟.
Proof. firstorder. Qed.

Fact 本地蕴含同构 : ∀ P Q : 命题, ⌜P → Q⌟ ↔ (⌜P⌟ → ⌜Q⌟).
Proof. firstorder. Qed.

Fact 本地等价同构 : ∀ P Q : 命题, ⌜P ↔ Q⌟ ↔ (⌜P⌟ ↔ ⌜Q⌟).
Proof. firstorder. Qed.

Fact 本地相等同构 {A : Type} : ∀ x y : A, ⌜x = y⌟ ↔ x = y.
Proof. firstorder. Qed.

Fact 本地全称量词同构 {A : Type} : ∀ Φ : 泛性质 A,
  ⌜∀ x, Φ x⌟ ↔ ∀ x, ⌜Φ x⌟.
Proof. firstorder. Qed.

Fact 本地存在量词同构 {A : Type} : ∀ Φ : 泛性质 A,
  (∃ x, ⌜Φ x⌟) ↔ ⌜∃ x, Φ x⌟.
Proof. firstorder. Qed.

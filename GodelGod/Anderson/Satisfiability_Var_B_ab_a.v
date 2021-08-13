(** Coq coding by choukh, Aug 2021 **)

(* 基于安德森[2]第4节对可满足性的讨论 *)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Model.Var_B_ab_a.

Definition 缺陷性 : 性质 := λ x, x = b.

Definition 积极 : 泛性质 性质 := λ Φ, 反 Φ ⇒ 缺陷性.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Theorem 积极性质的反面消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.
Proof.
  证明. intros Φ HP HN. destruct w.
  - 排中 ((Φ a) w₁).
    + assert (((反 反 Φ) a) w₁). firstorder.
      apply 𝗧 in HN. apply HN in H0. discriminate.
    + apply 𝗧 in HP. apply HP in H. discriminate.
  - 排中 ((Φ a) w₂).
    + assert (((反 反 Φ) a) w₂). firstorder.
      apply 𝗧 in HN. apply HN in H0. discriminate.
    + apply 𝗧 in HP. apply HP in H. discriminate.
Qed.

Theorem 积极的必然后果也积极 : ⌈∀ Φ Ψ : 性质, 积极 Φ → (Φ ⟹ Ψ) → 积极 Ψ⌋.
Proof.
  证明. intros Φ Ψ HP H. 必入. intros x HΨ.
  排中 ((Φ a) w0) as [HΦ|HΦ].
  - pose proof (H w0 R) as H'.
      apply H' in HΦ; [|destruct w0; constructor].
      destruct x. exfalso; auto. reflexivity.
  - pose proof (HP w0 R) as HP'.
    apply HP' in HΦ. discriminate.
Qed.

(* x具有神性，当且仅当x必然有且仅必然有积极性质 *)
Definition 神性 : 性质 := λ x, ∀ Φ, □ Φ x ↔ 积极 Φ.

Theorem 神性积极 : ⌈积极 神性⌋.
Proof.
  证明. 必入. intros x Hng.
  destruct x; [exfalso|reflexivity].
  apply Hng. intros Φ. split; intros H.
  - 必入. intros y Hy. destruct y; firstorder.
  - 必入. 反证. apply H in 反设. discriminate. apply R0.
Qed.

Theorem 积极性质必然积极 : ⌈∀ Φ, 积极 Φ → □ 积极 Φ⌋.
Proof.
  证明. intros Φ HP. 必入. 必入. intros x H.
  destruct x; [exfalso|reflexivity].
  apply H. 反证. apply HP in 反设. discriminate.
  destruct w; destruct w0; destruct w1; constructor.
Qed.

(* P是x的本性，当且仅当x必然有且仅必然有P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ Φ x, ∀ Ψ, □ Ψ x ↔ Φ ⇒ Ψ.

(* 实体实在，当且仅当该实体的任意本性都必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ Φ, 本性 Φ x → □ ∃ x, Φ x.

Theorem 实在性积极 : ⌈积极 实在性⌋.
Proof.
  证明. 必入. intros x H.
  destruct x; [exfalso|reflexivity].
  apply H. intros Φ HE. 必入.
  exists a. firstorder.
Qed.

Lemma 存在偶然命题 : ⌈∃ P, P ∧ ◇ ¬ P⌋.
Proof.
  证明. destruct w.
  - set (∃ᴱ x y, x ≠ y) as P. exists P. split.
    + exists a. split. constructor.
      exists b. split. constructor. discriminate.
    + 可入 w₂. constructor.
      intros [x [Hx [y [Hy Hnq]]]].
      inversion Hx. inversion Hy. congruence.
  - set (∀ᴱ x y, x = y) as P. exists P. split.
    + intros x Hx y Hy.
      inversion Hx. inversion Hy. reflexivity.
    + 可入 w₁. constructor.
      intros H. pose proof (H a a₁ b b₁). discriminate.
Qed.

Theorem 反模态坍塌 : ⌈¬ ∀ P, P → □ P⌋.
Proof. 证明. pose proof 存在偶然命题. firstorder. Qed.

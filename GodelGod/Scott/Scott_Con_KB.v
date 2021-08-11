(** Coq coding by choukh, July 2021 **)

(* 基于斯科特[1] *)
(* 消除了哥德尔原始版本中公理不一致的问题 *)
(* 斯科特本人的版本[1]基于S5系统，但最近的研究[5]显示只需更弱的KB系统 *)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.

Parameter 积极 : 泛性质 性质.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极的否定消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.
Axiom 消极的否定积极 : ⌈∀ Φ, 消极 Φ → 积极 (反 Φ)⌋.

Axiom 积极的必然后果也积极 : ⌈∀ Φ Ψ : 性质, 积极 Φ → (Φ ⇒ Ψ) → 积极 Ψ⌋.

(* 基于[5]第5节的改进证法 *)
Theorem 积极性质可能存在实例 : ⌈∀ Φ, 积极 Φ → 一致 Φ⌋.
Proof.
  证明. intros Φ H. 反证.
  apply (爆炸原理 w Φ (反 Φ)) in 反设.
  apply (积极的否定消极 w Φ). apply H.
  now apply (积极的必然后果也积极 w Φ).
Qed.

(* x具有神性，当且仅当任意积极性质都被x所具有 *)
Definition 神性 : 性质 := λ x, ∀ Φ, 积极 Φ → Φ x.

Axiom 神性积极 : ⌈积极 神性⌋.

Theorem 可能存在神 : ⌈一致 神性⌋.
Proof. 证明. apply 积极性质可能存在实例. apply 神性积极. Qed.

Lemma 神的任意性质积极 : ⌈∀ x Φ, 神性 x → Φ x → 积极 Φ⌋.
Proof.
  证明. intros g Φ HG HΦ. 反证.
  assert (积极 (反 Φ) w). firstorder using 消极的否定积极.
  now apply HG in H.
Qed.

Module 一神论.

Theorem 神唯一 : ⌈∀ x y, 神性 x → 神性 y → x = y⌋.
Proof.
  证明. intros a b Ha Hb.
  set (λ x, x = a) as Φ.
  assert (积极 Φ w). now apply (神的任意性质积极 w a).
  now apply Hb in H.
Qed.

Theorem 必然神唯一 : ⌈□ ∀ x y, 神性 x → 神性 y → x = y⌋.
Proof. apply 𝗡. apply 神唯一. Qed.

End 一神论.

(* 对本性定义的修改消除了公理不一致的问题 *)
(* P是x的本性，当且仅当P是x的性质且x的任意性质都是P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ Φ x, Φ x ∧ ∀ Ψ, Ψ x → Φ ⇒ Ψ.

Axiom 积极性质必然积极 : ⌈∀ Φ, 积极 Φ → □ 积极 Φ⌋.

Theorem 神性是神之本性 : ⌈∀ x, 神性 x → 本性 神性 x⌋.
Proof.
  证明. intros g HG. split. apply HG.
  intros Φ HΦ. apply 神的任意性质积极 in HΦ; auto.
  eapply 必然性三段论. apply 积极性质必然积极.
  apply HΦ. firstorder.
Qed.

(* 实体实在，当且仅当该实体的任意本性都必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ Φ, 本性 Φ x → □ ∃ x, Φ x.

Axiom 实在性积极 : ⌈积极 实在性⌋.

Lemma 神具有实在性 : ⌈∀ x, 神性 x → 实在性 x⌋.
Proof. firstorder using 实在性积极. Qed.

Lemma 存在神则必然存在神 : ⌈(∃ x, 神性 x) → □ ∃ x, 神性 x⌋.
Proof.
  证明. intros [g HG].
  apply (神具有实在性 w g HG).
  now apply 神性是神之本性.
Qed.

Module 原始版. (* 基于[1] *)
Import Modal.S5.

Lemma 可能存在神则必然存在神 : ⌈一致 神性 → □ ∃ x, 神性 x⌋.
Proof.
  证明. intros H. apply 𝟰𝗕.
  eapply 可能性三段论. apply H.
  必入. apply 存在神则必然存在神.
Qed.

Theorem 必然存在神 : ⌈□ ∃ x, 神性 x⌋.
Proof. 证明. apply 可能存在神则必然存在神. apply 可能存在神. Qed.

Theorem 存在神 : ⌈∃ x, 神性 x⌋.
Proof. 证明. apply 𝗧. apply 必然存在神. Qed.

End 原始版.

Module Import 改进版. (* 基于[5]第5节 *)
Import Modal.KB.

Lemma 可能必然存在神 : ⌈◇ □ ∃ x, 神性 x⌋.
Proof.
  证明. eapply 可能性三段论. apply 可能存在神.
  apply 𝗡. apply 存在神则必然存在神.
Qed.

Theorem 存在神 : ⌈∃ x, 神性 x⌋.
Proof. 证明. apply 𝗕归结. apply 可能必然存在神. Qed.

Theorem 必然存在神 : ⌈□ ∃ x, 神性 x⌋.
Proof. apply 𝗡. apply 存在神. Qed.

End 改进版.

Module 反驳1. (* 基于[5]第6节 *)

Lemma 神的任意性质都是神性的必然后果 : ⌈∀ x Φ, 神性 x → Φ x → 神性 ⇒ Φ⌋.
Proof. 证明. intros g Φ HG. apply 神性是神之本性. apply HG. Qed.

Fact 模态坍塌 : ⌈∀ P, P → □ P⌋.
Proof.
  证明. intros P HP.
  set (λ _ : 实体, P) as Φ.
  cut ((□ ∃ x, Φ x) w). firstorder.
  destruct (存在神 w) as [g HG].
  pose proof (神的任意性质都是神性的必然后果 w g Φ HG HP).
  eapply 必然性三段论. apply H. 必入. intros H'.
  destruct (存在神 w0) as [g' HG'].
  apply H' in HG'. now exists g'.
Qed.

End 反驳1.

Module 反驳2. (* 基于[1] *)

Fact 积极性质必然存在实例 : ⌈∀ Φ, 积极 Φ → □ ∃ x, Φ x⌋.
Proof.
  证明. intros Φ H. apply 积极性质必然积极 in H.
  eapply 必然性三段论. apply 必然存在神. firstorder.
Qed.

Fact 无本性的实体具有实在性 : ⌈∀ x, (∀ Φ, ¬ 本性 Φ x) → 实在性 x⌋.
Proof. firstorder. Qed.

Fact 任意实体具有实在性 : ⌈∀ x, 实在性 x⌋.
Proof.
  证明. intros x Φ H.
  set (λ _ : 实体, ∃ y, 本性 Φ y) as Ψ.
  cut ((□ ∃ y, Ψ y) w). firstorder.
  apply 积极性质必然存在实例.
  destruct (存在神 w) as [g HG].
  apply (神的任意性质积极 w g); firstorder.
Qed.

End 反驳2.

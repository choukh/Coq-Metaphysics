(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.

Parameter 积极 : 性质 → 命题.
Definition 消极 := λ P, ¬ 积极 P.

Axiom 积极的否定消极 : ⌜ ∀ P, 积极 P ↔ 消极 (非 P) ⌝.

Axiom 积极的必然后果也积极 : ⌜ ∀ P Q : 性质, 积极 P → (P ⇒ Q) → 积极 Q ⌝.

Theorem 积极性质可能存在实例 : ⌜ ∀ P, 积极 P → 一致 P ⌝.
Proof.
  投射. intros P H.
  assert (恒真积极: 积极 恒真 w). {
    apply (积极的必然后果也积极 w P). apply H. firstorder.
  }
  assert (恒假消极: 消极 恒假 w). {
    apply 积极的否定消极. apply 恒真积极.
  }
  反证. apply 恒假消极. apply (积极的必然后果也积极 w P).
  apply H. now apply 爆炸原理.
Qed.

(* x具有神性，当且仅当任意积极性质都被x所具有 *)
Definition 神性 : 性质 := λ x, ∀ P, 积极 P → P x.

Axiom 神性积极 : ⌜ 积极 神性 ⌝.

Theorem 可能存在神 : ⌜ 一致 神性 ⌝.
Proof. 投射. apply 积极性质可能存在实例. apply 神性积极. Qed.

Lemma 神的任意性质积极 : ⌜ ∀ x P, 神性 x → P x → 积极 P ⌝.
Proof.
  投射. intros x P HG HP. 反证.
  assert (积极 (非 P) w). firstorder using 积极的否定消极.
  now apply HG in H.
Qed.

Section 唯一性证明.

Theorem 神唯一 : ⌜ ∀ x y, 神性 x → 神性 y → x = y ⌝.
Proof.
  投射. intros a b Ha Hb.
  set (λ x, x = a) as 同一性.
  assert (积极 同一性 w). now apply (神的任意性质积极 w a).
  now apply Hb in H.
Qed.

Theorem 必然神唯一 : ⌜ □ ∀ x y, 神性 x → 神性 y → x = y ⌝.
Proof. apply 必然性规则. apply 神唯一. Qed.

End 唯一性证明.

(* P是x的本性，当且仅当P是x的性质且x的任意性质都是P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ P x, P x ∧ ∀ Q, Q x → P ⇒ Q.

Axiom 积极性质必然积极 : ⌜ ∀ P, 积极 P → □ 积极 P ⌝.

Theorem 神性是神之本性 : ⌜ ∀ x, 神性 x → 本性 神性 x ⌝.
Proof.
  投射. intros x HG. split. apply HG.
  intros Q HQ. apply 神的任意性质积极 in HQ; auto.
  assert ⌜ □ (积极 Q → ∀ x, 神性 x → Q x) ⌝. firstorder.
  apply (𝗞 w) in H. apply H. now apply 积极性质必然积极.
Qed.

(* 实体实在，当且仅当该实体的任意本性都必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ P, 本性 P x → □ ∃ x, P x.

Axiom 实在性积极 : ⌜ 积极 实在性 ⌝.

Lemma 神具有实在性 : ⌜ ∀ x, 神性 x → 实在性 x ⌝.
Proof. firstorder using 实在性积极. Qed.

Lemma 存在神则必然存在神 : ⌜ (∃ x, 神性 x) → □ ∃ x, 神性 x ⌝.
Proof.
  投射. intros [x HG].
  apply 神具有实在性 in HG as HR.
  apply HR. now apply 神性是神之本性.
Qed.

Import Modal.KB4.

Lemma 可能存在神则必然存在神 : ⌜ 一致 神性 → □ ∃ x, 神性 x ⌝.
Proof.
  投射. intros H. apply 𝗕𝟰.
  eapply 可能性三段论. apply H.
  必入. apply 存在神则必然存在神.
Qed.

Theorem 必然存在神 : ⌜ □ ∃ x, 神性 x ⌝.
Proof. 投射. apply 可能存在神则必然存在神. apply 可能存在神. Qed.

Import Modal.KT.

Theorem 存在神 : ⌜ ∃ x, 神性 x ⌝.
Proof. 投射. apply 𝗧. apply 必然存在神. Qed.

Section 反驳1.

Lemma 神的任意性质都是神性的必然后果 : ⌜ ∀ x P, 神性 x → P x → 神性 ⇒ P ⌝.
Proof.
  投射. intros g P Hg HP.
  eapply 神性是神之本性; eauto.
Qed.

Fact 模态坍塌 : ⌜ ∀ P, P → □ P ⌝.
Proof.
  投射. intros p Hp.
  set (λ _ : 实体, p) as P.
  cut ((□ ∃ x, P x) w). firstorder.
  destruct (存在神 w) as [g Hg].
  pose proof (神的任意性质都是神性的必然后果 w g P Hg Hp).
  eapply 𝗞; [|apply H]. 必入. intros H'.
  destruct (存在神 w0) as [g' Hg'].
  apply H' in Hg'. now exists g'.
Qed.

End 反驳1.

Section 反驳2.

Fact 积极性质必然存在实例 : ⌜ ∀ P, 积极 P → □ ∃ x, P x ⌝.
Proof.
  投射. intros P HP. apply 积极性质必然积极 in HP.
  eapply 𝗞; [|apply 必然存在神]. firstorder.
Qed.

Fact 无本性的实体具有实在性 : ⌜ ∀ x, (∀ P, ¬ 本性 P x) → 实在性 x ⌝.
Proof. firstorder. Qed.

Fact 任意实体具有实在性 : ⌜ ∀ x, 实在性 x ⌝.
Proof.
  投射. intros x ϕ HEϕ.
  set (λ _ : 实体, ∃ y, 本性 ϕ y) as P.
  cut ((□ ∃ y, P y) w). firstorder.
  apply 积极性质必然存在实例.
  destruct (存在神 w) as [g Hg].
  apply (神的任意性质积极 w g); firstorder.
Qed.

End 反驳2.

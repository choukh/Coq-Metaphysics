(** Coq coding by choukh, Aug 2021 **)

(* 基于近期研究[7]第7节 *)
(* 在安德森[2]的基础上删除了多余的公理4和5 *)
(* 验证了哈耶克[3]关于安德森公理可简化主张的正确性 *)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.
Import Modal.KB.

Parameter 积极 : 泛性质 性质.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极性质的反面消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.

Axiom 积极的必然后果也积极 : ⌈∀ Φ Ψ : 性质, 积极 Φ → (Φ ⇒ Ψ) → 积极 Ψ⌋.

Theorem 积极性质可能存在实例 : ⌈∀ Φ, 积极 Φ → 一致 Φ⌋.
Proof.
  证明. intros Φ H. 反证.
  apply (爆炸原理 w Φ (反 Φ)) in 反设.
  apply (积极性质的反面消极 w Φ). apply H.
  now apply (积极的必然后果也积极 w Φ).
Qed.

(* x具有神性，当且仅当x必然有且仅必然有积极性质 *)
Definition 神性 : 性质 := λ x, ∀ Φ, □ Φ x ↔ 积极 Φ.

Axiom 神性积极 : ⌈积极 神性⌋.

Corollary 可能存在神 : ⌈一致 神性⌋.
Proof. 证明. apply 积极性质可能存在实例. apply 神性积极. Qed.

Lemma 存在神则必然存在神 : ⌈(∃ x, 神性 x) → □ ∃ x, 神性 x⌋.
Proof.
  证明. intros [g Hg].
  cut ((□ 神性 g) w). firstorder.
  apply Hg. apply 神性积极.
Qed.

Lemma 可能必然存在神 : ⌈◇ □ ∃ x, 神性 x⌋.
Proof.
  证明. eapply 可能性三段论1. apply 可能存在神.
  apply 𝗡. apply 存在神则必然存在神.
Qed.

Theorem 存在神 : ⌈∃ x, 神性 x⌋.
Proof. 证明. apply 𝗕归结. apply 可能必然存在神. Qed.

Corollary 必然存在神 : ⌈□ ∃ x, 神性 x⌋.
Proof. apply 𝗡. apply 存在神. Qed.

Module 一神论.
Import Modal.B.

Theorem 神唯一 : ⌈∀ x y, 神性 x → 神性 y → x = y⌋.
Proof.
  证明. intros a b Ha Hb.
  set (λ x, x = b) as Φ.
  assert (积极 Φ w). apply Hb. firstorder.
  apply Ha in H. now apply 𝗧 in H.
Qed.

Corollary 必然神唯一 : ⌈□ ∀ x y, 神性 x → 神性 y → x = y⌋.
Proof. apply 𝗡. apply 神唯一. Qed.

End 一神论.

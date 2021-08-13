(** Coq coding by choukh, Aug 2021 **)

(* 基于Bjørdal[5] *)
(* 使用与安德森不同的方法消除了模态坍塌，且简化了公理系统 *)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.
Import Modal.KB.

Parameter 神性 : 性质.

(* 性质Φ积极，当且仅当Φ是神性的必然后果 *)
Definition 积极 : 泛性质 性质 := λ Φ, 神性 ⇒ Φ.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极性质的反面消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.

Theorem 神性积极 : ⌈积极 神性⌋.
Proof. firstorder. Qed.

Theorem 可能存在神 : ⌈一致 神性⌋.
Proof.
  证明. 反证. eapply 积极性质的反面消极. apply 神性积极.
  eapply 爆炸原理. apply 反设.
Qed.

(* Φ是x的集大成，当且仅当Φ是x的积极性质且x的任意积极性质都是Φ的必然后果 *)
Definition 集大成 : 性质 → 实体 → 命题 := λ Φ x,
  Φ x ∧ 积极 Φ ∧ ∀ Ψ, Ψ x → 积极 Ψ → Φ ⇒ Ψ.

(* 实体实在，当且仅当该实体的集大成必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ Φ, 集大成 Φ x → □ ∃ x, Φ x.

Axiom 实在性积极 : ⌈积极 实在性⌋.

Lemma 存在神则必然存在神 : ⌈(∃ x, 神性 x) → □ ∃ x, 神性 x⌋.
Proof.
  证明. intros [g Hg].
  eapply 必然性三段论. apply 𝗡. apply 实在性积极.
  apply 必然性蕴含式推理. intros H. eapply H; eauto. firstorder.
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

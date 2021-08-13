(** Coq coding by choukh, Aug 2021 **)

(* 哥德尔本体论公理的本地版本在固定论域KB系统中不一致 *)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.
Require Import CM.Logic.LocalWorld.
Import Modal.KB.

Parameter 积极 : 泛性质 性质.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极性质的反面消极 : ⌜∀ Φ, 积极 Φ → 消极 (反 Φ)⌟.

Axiom 积极的必然后果也积极 : ⌜∀ Φ Ψ : 性质, 积极 Φ → (Φ ⇒ Ψ) → 积极 Ψ⌟.

Theorem 积极性质可能存在实例 : ⌜∀ Φ, 积极 Φ → 一致 Φ⌟.
Proof.
  intros Φ H. 反证.
  apply (爆炸原理 w₀ Φ (反 Φ)) in 反设.
  apply (积极性质的反面消极 Φ). apply H.
  now apply (积极的必然后果也积极 Φ).
Qed.

(* P是x的本性，当且仅当x的任意性质都是P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ Φ x, ∀ Ψ, Ψ x → Φ ⇒ Ψ.

(* 实体实在，当且仅当该实体的任意本性都必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ Φ, 本性 Φ x → □ ∃ x, Φ x.

Axiom 实在性积极 : ⌜积极 实在性⌟.

Lemma 实在性可能存在实例 : ⌜一致 实在性⌟.
Proof. apply 积极性质可能存在实例. apply 实在性积极. Qed.

Lemma 可能必然存在反同一性实体 : ⌜◇ □ ∃ x, 反同一性 x⌟.
Proof.
  eapply 可能性三段论1. apply 实在性可能存在实例.
  apply 𝗡. 证明. intros []. apply H. firstorder.
Qed.

Fact 公理不一致 : False.
Proof.
  pose proof 可能必然存在反同一性实体.
  firstorder using 对称框架.
Qed.

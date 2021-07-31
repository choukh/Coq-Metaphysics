(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.

Parameter 积极 : 性质 → 命题.
Definition 消极 := λ P, ¬ 积极 P.

Axiom 积极的否定消极 : ⌜ ∀ P, 积极 P ↔ 消极 (非 P) ⌝.

Axiom 积极的必然后果也积极 : ⌜ ∀ P Q : 性质, 积极 P → (P ⇒ Q) → 积极 Q ⌝.

Theorem 积极性质一致 : ⌜ ∀ P, 积极 P → 一致 P ⌝.
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

(* 神是具有所有积极性质的实体 *)
Definition 神性 : 性质 := λ x, ∀ P, 积极 P → P x.

Axiom 神性积极 : ⌜ 积极 神性 ⌝.

Theorem 可能存在神 : ⌜ 一致 神性 ⌝.
Proof. 投射. apply 积极性质一致. apply 神性积极. Qed.

(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.
Import Modal.S5.

Parameter 积极 : 性质 → 命题.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极的否定消极 : ⌜ ∀ Φ, 积极 Φ → 消极 (非 Φ) ⌝.

Axiom 积极的必然后果也积极 : ⌜ ∀ Φ Ψ : 性质, 积极 Φ → (Φ ⇒ Ψ) → 积极 Ψ ⌝.

Theorem 积极性质可能存在实例 : ⌜ ∀ Φ, 积极 Φ → 一致 Φ ⌝.
Proof.
  投射. intros Φ H.
  assert (恒真积极: 积极 恒真 w). {
    apply (积极的必然后果也积极 w Φ). apply H. firstorder.
  }
  assert (恒假消极: 消极 恒假 w). {
    apply 积极的否定消极. apply 恒真积极.
  }
  反证. apply 恒假消极. apply (积极的必然后果也积极 w Φ).
  apply H. now apply 爆炸原理.
Qed.

(* x具有神性，当且仅当x必然有且仅必然有积极性质 *)
Definition 神性 : 性质 := λ x, ∀ Φ, □ Φ x ↔ 积极 Φ.

Axiom 神性积极 : ⌜ 积极 神性 ⌝.

Theorem 可能存在神 : ⌜ 一致 神性 ⌝.
Proof. 投射. apply 积极性质可能存在实例. apply 神性积极. Qed.

Section 唯一性证明.

Theorem 神唯一 : ⌜ ∀ x y, 神性 x → 神性 y → x = y ⌝.
Proof.
  投射. intros a b Ha Hb.
  set (λ x, x = b) as Φ.
  assert (积极 Φ w). apply Hb. firstorder.
  apply Ha in H. now apply 𝗧 in H.
Qed.

Theorem 必然神唯一 : ⌜ □ ∀ x y, 神性 x → 神性 y → x = y ⌝.
Proof. apply 必然性规则. apply 神唯一. Qed.

End 唯一性证明.

(* P是x的本性，当且仅当x必然有且仅必然有P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ Φ x, ∀ Ψ, □ Ψ x ↔ Φ ⇒ Ψ.

Axiom 积极性质必然积极 : ⌜ ∀ Φ, 积极 Φ → □ 积极 Φ ⌝.

Theorem 神性是神之本性 : ⌜ ∀ x, 神性 x → 本性 神性 x ⌝.
Proof.
  投射. intros g HG Φ. split; intros H.
  - apply HG in H. apply 积极性质必然积极 in H.
    eapply 𝗞; [|apply H]. 必入. intros H' x HG'.
    apply HG' in H'. now apply 𝗧 in H'.
  - apply HG. eapply 积极的必然后果也积极.
    apply 神性积极. apply H.
Qed.

(* 实体实在，当且仅当该实体的任意本性都必然存在实例 *)
Definition 实在性 : 性质 := λ x, ∀ P, 本性 P x → □ ∃ x, P x.

Axiom 实在性积极 : ⌜ 积极 实在性 ⌝.

Lemma 神具有实在性 : ⌜ ∀ x, 神性 x → 实在性 x ⌝.
Proof. firstorder using 实在性积极. Qed.

Lemma 存在神则必然存在神 : ⌜ (∃ x, 神性 x) → □ ∃ x, 神性 x ⌝.
Proof.
  投射. intros [g HG].
  apply (神具有实在性 w g HG).
  now apply 神性是神之本性.
Qed.

Lemma 可能存在神则必然存在神 : ⌜ 一致 神性 → □ ∃ x, 神性 x ⌝.
Proof.
  投射. intros H. apply 𝗕𝟰.
  eapply 可能性三段论. apply H.
  必入. apply 存在神则必然存在神.
Qed.

Theorem 必然存在神 : ⌜ □ ∃ x, 神性 x ⌝.
Proof. 投射. apply 可能存在神则必然存在神. apply 可能存在神. Qed.

Theorem 存在神 : ⌜ ∃ x, 神性 x ⌝.
Proof. 投射. apply 𝗧. apply 必然存在神. Qed.

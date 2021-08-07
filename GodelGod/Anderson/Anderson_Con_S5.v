(** Coq coding by choukh, July 2021 **)

Require Import CM.Logic.Classical.
Require Import CM.Logic.Modal.
Require Import CM.Logic.Entity.
Import Modal.S5.

Parameter 积极 : 泛性质 性质.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Axiom 积极的否定消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.

Axiom 积极的必然后果也积极 : ⌈∀ Φ Ψ : 性质, 积极 Φ → (Φ ⇒ Ψ) → 积极 Ψ⌋.

Theorem 积极性质可能存在实例 : ⌈∀ Φ, 积极 Φ → 一致 Φ⌋.
Proof.
  证明. intros Φ H. 反证.
  apply (爆炸原理 w Φ (反 Φ)) in 反设.
  apply (积极的否定消极 w Φ). apply H.
  now apply (积极的必然后果也积极 w Φ).
Qed.

(* x具有神性，当且仅当x必然有且仅必然有积极性质 *)
Definition 神性 : 性质 := λ x, ∀ Φ, □ Φ x ↔ 积极 Φ.

Axiom 神性积极 : ⌈积极 神性⌋.

Theorem 可能存在神 : ⌈一致 神性⌋.
Proof. 证明. apply 积极性质可能存在实例. apply 神性积极. Qed.

Module 唯一性证明.

Theorem 神唯一 : ⌈∀ x y, 神性 x → 神性 y → x = y⌋.
Proof.
  证明. intros a b Ha Hb.
  set (λ x, x = b) as Φ.
  assert (积极 Φ w). apply Hb. firstorder.
  apply Ha in H. now apply 𝗧 in H.
Qed.

Theorem 必然神唯一 : ⌈□ ∀ x y, 神性 x → 神性 y → x = y⌋.
Proof. apply 𝗡. apply 神唯一. Qed.

End 唯一性证明.

(* P是x的本性，当且仅当x必然有且仅必然有P的必然后果 *)
Definition 本性 : 性质 → 实体 → 命题 :=
  λ Φ x, ∀ Ψ, □ Ψ x ↔ Φ ⇒ Ψ.

Module 对本性定义的辩护.

Fact 本性是必然被单一实体所必然具有的特性 :
  ∀ Φ x, ⌈本性 Φ x⌋ ↔ ⌈□ Φ x ∧ □ ∀ y, Φ y → x = y⌋.
Proof.
  intros Φ a. split; intros H; 证明.
  - split. firstorder.
    必入. intros b HΦb.
    set (λ x, a = x) as Ψ.
    assert (HΨa: (□ Ψ a) w0). firstorder.
    apply H in HΨa. apply 𝗧 in HΨa. apply HΨa. apply HΦb.
  - intros Ψ. split; [|firstorder].
    intros HΨa. 必入. intros x HΦa. 必除 HΨa HΨa'.
    destruct (H w0)as [_ H0]. apply 𝗧 in H0.
    now rewrite (H0 x) in HΨa'.
Qed.

End 对本性定义的辩护.

Axiom 积极性质必然积极 : ⌈∀ Φ, 积极 Φ → □ 积极 Φ⌋.

Theorem 神性是神之本性 : ⌈∀ x, 神性 x → 本性 神性 x⌋.
Proof.
  证明. intros g HG Φ. split; intros H.
  - apply HG in H. apply 积极性质必然积极 in H.
    必入. 必除 H H'. intros x HG'.
    apply HG' in H'. now apply 𝗧 in H'.
  - apply HG. eapply 积极的必然后果也积极.
    apply 神性积极. apply H.
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

Lemma 可能存在神则必然存在神 : ⌈一致 神性 → □ ∃ x, 神性 x⌋.
Proof.
  证明. intros H. apply 𝗕𝟰.
  eapply 可能性三段论. apply H.
  必入. apply 存在神则必然存在神.
Qed.

Theorem 必然存在神 : ⌈□ ∃ x, 神性 x⌋.
Proof. 证明. apply 可能存在神则必然存在神. apply 可能存在神. Qed.

Theorem 存在神 : ⌈∃ x, 神性 x⌋.
Proof. 证明. apply 𝗧. apply 必然存在神. Qed.

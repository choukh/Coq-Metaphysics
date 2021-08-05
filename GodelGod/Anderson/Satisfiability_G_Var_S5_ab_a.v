(** Coq coding by choukh, Aug 2021 **)

Require Import CM.Logic.Model.G_Var_S5_ab_a.

Definition 缺陷性 : 性质 := λ x, x = b.

Definition 积极 : 泛性质 性质 := λ Φ, 反 Φ ⇒ 缺陷性.
Definition 消极 := λ Φ, ¬ 积极 Φ.

Theorem 积极的否定消极 : ⌈∀ Φ, 积极 Φ → 消极 (反 Φ)⌋.
Proof.
Admitted.

(* TODO *)

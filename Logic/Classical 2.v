(** Coq coding by choukh, July 2021 **)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Logic.Classical.

Tactic Notation "排中" constr(P) :=
  destruct (classic P).
Tactic Notation "排中" constr(P) "as" simple_intropattern(L) :=
  destruct (classic P) as L.

Ltac 反证 := match goal with
  |- ?G => destruct (classic G) as [正设|?反设]; [apply 正设|exfalso]
end.

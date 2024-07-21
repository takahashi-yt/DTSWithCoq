From elpi Require Import elpi.
Require Import DTSTactics.

Parameter human man : entity -> Type.


(* some experimental tactics to search for certain entities such as
   non-human entities and man

   We implement the tactics by using Coq-Elpi *)

Elpi Tactic acc_check_it.
Elpi Accumulate lp:{{

  solve (goal Ctx _ _ _ _) _ :-
    std.mem Ctx (decl Var Name1 {{entity}}),
      std.mem Ctx (decl _ _ {{human lp:Var -> False}}),
        coq.say Name1 "is not a human", fail.

  solve _ _ :- coq.say "the accessibility check was completed!".

}}.
Elpi Typecheck.

(* test example *)
Goal forall (x y z : entity), (human x -> False) -> human z -> (human y -> False) -> True.
Proof.
  intros.
  elpi acc_check_it.
  auto.
Qed.


Elpi Tactic acc_check_he.
Elpi Accumulate lp:{{

  solve (goal Ctx _ _ _ _) _ :-
    std.mem Ctx (decl Var Name1 {{entity}}),
      std.mem Ctx (decl _ _ {{man lp:Var}}),
        coq.say Name1 "is a man", fail.

  solve _ _ :- coq.say "the accessibility check was completed!".

}}.
Elpi Typecheck.

(* test example *)
Goal forall (x y z : entity), (man x -> False) -> man z -> (man y -> False) -> True.
Proof.
  intros.
  elpi acc_check_he.
  auto.
Qed.
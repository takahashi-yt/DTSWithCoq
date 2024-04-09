Parameter entity : Type.

Definition a_nom : forall n v : entity -> Type, Type :=
  fun n v => {x : entity & {_ : n x & v x}}.

Definition a_acc : forall (n : entity -> Type) (v: entity -> entity -> Type) (x : entity), Type :=
  fun n v x =>  {y: entity & {_ : n y &  v y x}}.

Definition some_nom : forall n v : entity -> Type, Type :=
  fun n v => {x : entity & {_ : n x & v x}}.

Definition every_nom : forall n v : entity -> Type, Type :=
  fun n v => forall u : {x : entity & n x}, v (projT1 u).

Definition every_subj : (entity -> Type) -> (entity -> Type) -> Type :=
  fun (n : entity -> Type) (v : entity -> Type) => forall u : {x : entity & n x}, v (projT1 u). 

Definition every_obj : (entity -> Type) -> (entity -> entity -> Type) -> entity -> Type :=
  fun (n : entity -> Type) (p : entity -> entity -> Type) (x : entity) => forall u : {x : entity & n x}, p x (projT1 u). 

Definition no_nom : forall n v : entity -> Type, Type :=
    fun n v => {x : entity & {_ : n x & v x}} -> False.

Definition any_nom : forall n v : entity -> Type, Type :=
    fun n v => {x : entity & {_ : n x & v x}}.

Definition all_nom : forall n v : entity -> Type, Type :=
    fun n v => forall u : {x : entity & n x}, v (projT1 u).

Definition just_one_nom : forall n v : entity -> Type, Type :=
    fun n v => ({x : entity & {_ :  n x & v x}} * (forall y z : entity, {_ : {_ : {_: n y & v y} & n z} & v z} -> y = z))%type.

Definition who : forall (n v : entity -> Type) (x : entity), Type :=
    fun n v x => {_ : n x & v x}.

Definition if1 : Type -> Type -> Type :=
    fun p q => p -> q.

Definition prog_conj (A B : Type) : Type.
Proof.
  exact {_ : A & B}.
Defined.


(* In DTSWithCoq, underspecified types are defined as inductive types which are called aspT

   The expression aspT A a B is intended to represent a result of anaphora resolution:
   let B be a sentence including an anaphoric expression of type A,
   then aspT A a B corresponds to the sentence obtained by replacing the anaphoric expression in B
   with an antecedent a of type A *)
  
Inductive aspT (A : Type) (a : A) (B : Type) : Type :=
    resolve : B -> aspT A a B.


(* The type resolution_record enables to store both a result A : Type of anaphora resolution and
   a proof of A
   It is useful for natural language inference using a result of anaphora resolution

   see Anaphora.v for some examples *)

Definition resolution_record : Type := {A : Type & A}.  

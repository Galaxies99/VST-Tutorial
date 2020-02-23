(** This file is heavily annotated for a tutorial introduction to VST. We
    assume that our readers have already had some experience in Coq. *)

(** First, import the entire Floyd proof automation system, which includes
    the VeriC program logic and the MSL theory of separation logic. *)
Require Import VST.floyd.proofauto.
(** This file is auxiliary tactics that we will use in this tutorial. *)
Require Import EV.AuxiliaryTac.

(** These are the C programs that we will verify. *)
Require EV.add EV.abs EV.append EV.max3 EV.swap EV.tri EV.gcd EV.fact EV.test_null EV.reverse.

Module Verif_uadd.

(** Here is the first C function that we are going to verify. It is a super
    simple one (you can also find it in [add.c]:

      unsigned int uadd(unsigned int x, unsigned int y) {
        unsigned int z;
        z = x + y;
        return z;
      }

    Now, import the [add.v] file, produced by CompCert's clightgen from
    [add.c]. The file [add.v] defines abbreviations for identifiers (variable
    names, etc.) of the C program, such as _x, _add. It also defines "prog",
    which is the entire abstract syntax tree of the C program. *)
Import EV.add.

(** Always copy the following two lines before verification. They are used to
    set up global environment. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Before proving a program correct, we first need to state what does 
    "correct" mean. Here is [uadd]'s specification: *)
Definition uadd_spec :=
 DECLARE _uadd
  WITH x: Z, y: Z
  PRE  [ _x OF tuint, _y OF tuint ]
     PROP  ()
     LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (x + y))))
     SEP   ().

(** It characterizes the precondition required for calling the function, and
    the postcondition guaranteed by the function. It says: for any integers
    [x] and [y], if the program variable [_x] has value [x] and the program
    variable [_y] has value [y], the the return value is [x+y]. **)

Check Int.repr.
  (* Int.repr : Z -> int *)
Check Vint.
  (* Vint : int -> val *)

(** [Int.repr] is a function turning an integer into a 32-bit integer. In VST,
    32-bit integers have type [int]. [Vint] turns a 32-bit integer into a C
    value. In VST, C values have type [val], which can be a 32-bit integer,
    a 64-bit integer, a floating point number or an address. *)

Check _x.
Print ident.
(** In VST, we always use names like [_x] to represent program variables and
    use Coq variables like [x] to represent logical variables. Program
    variables are represented by their indices, which are positive integers.

    If we review this specification, its main structure is:

        DECLARE _function_name_
          WITH _logical_variable_list_
          PRE  [ _function_argument_list_ ]
            _precondition_
          POST [ _return_type_ ]
            _postcondition_

    In the argument list of [uadd_spec], we use [tuint] to represent the C
    type of unsigned int. VST uses CompCert's type definitions. Usually, type
    definitions use names starting with "t", e.g. [tint], [tuint], [tchar],
    [tvoid] etc.

    VST requires users to write precondition in a [PROP-LOCAL-SEP] form.
    Postconditions and other assertions must be written in a [PROP-LOCAL-SEP]
    or existential [PROP-LOCAL-SEP] form. The [LOCAL] part describes the values
    of program variables. For example, [temp _x E] says the value of [_x] is
    [E]. We will see how to use the [PROP] part and the [SEP] part later.

    The following line defines the global function spec, characterizing the
    preconditions and postconditions of all the functions that your will verify
    and the functions that your proved-correct program may call. Here we
    include only one. *)

Definition Gprog : funspecs := ltac:(with_library prog [ uadd_spec ]).

(** For each function definition in the C program, we prove that the
    function-body (in this case, [f_uadd]) satisfies its specification (in
    this case, [uadd_spec]). *)
Lemma body_uadd: semax_body Vprog Gprog f_uadd uadd_spec.
Proof.
  (** The start_function tactic "opens up" a semax_body proof goal
      into a Hoare triple. *)
  start_function.
  (** The current proof goal is a Hoare triple. It is indeed

          semax Delta Precondition Command Postcondition.

      [semax] mainly means what follows is a Hoare triple. [Delta] is the
      C program's context which you can usually ignore. For convenience,
      VST chooses to only demonstrate the precondition and the first C
      command. Later commands and the postcondition is hidden.

      You can use [unfold] to reveal this hidden information. *)
  unfold MORE_COMMANDS, abbreviate.
  (** Usually you do not need to do this. *)
Abort.

(** Let's redo this proof without unfolding those hidden parts. *)
Lemma body_uadd: semax_body Vprog Gprog f_uadd uadd_spec.
Proof.
  start_function.
  (** For each assignment statement, "symbolically execute" it
      using the [forward] tactic. The backend of [forward] is a
      combination of Hoare logic's sequence rule and forward
      assignment rule. *)
  forward. (* z = x + y; *)
  (** If you compare the current proof goal with the original one, you
      will find that the first command is eaten. The precondition is
      replaced by the strongest postcondition of the original precondition
      and that eaten assignment command. *)
  rewrite add_repr.
  forward. (* return z; *)
Qed.

End Verif_uadd.

Module Verif_add_first_try.

(** Now we try to verify the second function [add]:

      int add(int x, int y) {
        int z;
        z = x + y;
        return z;
      }
*)
Import EV.add.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** You may intend to write exactly the same specification as [uadd]'s. Let's
    try and see whether it works or not. *)
Definition add_spec :=
 DECLARE _add
  WITH x: Z, y: Z
  PRE  [ _x OF tint, _y OF tint ]
     PROP  ()
     LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (x + y))))
     SEP   ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ add_spec ]).

Lemma body_add: semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward. (* z = x + y; *)
  (** Oops! VST generates an unexpected proof goal. In this proof goal,
      [tc_expr] says that expressions evaluating is legal. Specifically,
      VST asks whether evaluating [_x + _y] is safe, if the precondition
      holds. *)
  hint.
  (** [hint] is a VST's tactic. You can always use it when you do not
      know what to do. *)
  entailer!.
  (** [entailer!] is a VST's tactic to simplify (and solve, if possible)
      assertion derivations. Here, we need to prove that [x] and [y] is
      in the signed 32-bit range. This is reasonable -- C standard says
      arithmetic overflow is undefined behavior (unless their type is
      unsigned). We have to prove that our program is always safe to execute.

      In more details, [Int.signed] turns a 32-bit integer back to an integer
      using signed encoding.

      At this position, this goal is not provable. If we go back and review
      our proof. The proof itself has nothing wrong. What's wrong is the
      specification. *)
Abort.

End Verif_add_first_try.

Module Verif_add.

Import EV.add.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Now we try to redefine the specification [add_spec]. *)
Definition add_spec :=
 DECLARE _add
  WITH x: Z, y: Z
  PRE  [ _x OF tint, _y OF tint ]
     PROP  (0 <= x < 100; 0 <= y < 100)  (* <-- new *)
     LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (x + y))))
     SEP   ().

(** We add a line in the precondition. It requires [x], [y] to be small. In
    general, the [PROP] clauses are a list of Coq [Prop]s which describes
    logical variables' properties. *)

Definition Gprog : funspecs :=
         ltac:(with_library prog [ add_spec ]).

Lemma body_add: semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward. (* z = x + y; *)
  (** Symbolic execution works well this time. It does not generate any
      side condition because VST automatically understand that [x+y] is
      in signed 32-bit range due to the assumptions [H] and [H0]. *)
  rewrite add_repr.
  forward. (* return z; *)
Qed.

End Verif_add.

Module Verif_slow_add.

Import EV.add.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [slow_add]: 

      int slow_add(int x, int y) {
        while (x > 0) {
          x = x - 1;
          y = y + 1;
        }
        return y;
      }

    We grab this example from Benjamin Pierce's Software Foundation. While
    he explains this example in a toy language, we write it in a real languge
    C and verify this C function. *)

Definition slow_add_spec :=
 DECLARE _slow_add
  WITH x: Z, y: Z
  PRE  [ _x OF tint, _y OF tint ]
     PROP  (0 <= x < 100; 0 <= y < 100)
     LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (x + y))))
     SEP   ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ slow_add_spec ]).

Lemma body_slow_add: semax_body Vprog Gprog f_slow_add slow_add_spec.
Proof.
  start_function.
  (** This time we need to reason about a while-loop. We can use the tactic
      [forward-while] provided by VST. BTW, if you forget its name, you can
      always use [hint] for help.

      You must supply a loop invariant when you use [forward_while], in
      this case [EX x', EX y' PROP(...)LOCAL(...)(SEP(...)]. [EX] is the
      existential quantifier in VST's assertion language. *)
  forward_while
    (EX x': Z, EX y': Z,
      (PROP  ((x' + y' = x + y)%Z; 0 <= x' < 100; 0 <= y' < 200)
       LOCAL (temp _x (Vint (Int.repr x'));
              temp _y (Vint (Int.repr y')))
       SEP ())).
  (** The forward_while tactic leaves four subgoals. *)
  { (* Precondition implies loop invariant *)
    Exists x.
    Exists y.
    (** The [Exists] tacitc is used to instantiate the existential
        quantifiers on the right hand side. *)
    entailer!.
  }
  { (* Loop invariant implies typechecking of loop condition *)
    entailer!.
  }
  { (* Loop body preserves loop invariant. *)
    forward. (* x = x - 1; *)
    forward. (* y = y + 1; *)
    Exists (x' - 1, y' + 1).
    unfold fst, snd.
    entailer!.
  }
  (* After loop *)
  assert (x' = 0).
  { omega. }
  assert (y' = x + y).
  { omega. }
  subst.
  forward. (* return y; *)
Qed.

End Verif_slow_add.

Module Verif_abs.

Import EV.abs.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The following example explains how to verify if-commands. Her is a C
    function:

      int abs(int x) {
        if (x < 0)
          return -x;
        else
          return x;
      }

    This function will work well as long as the input value is not [- 2^31]. *)

Definition abs_spec :=
 DECLARE _abs
  WITH x: Z
  PRE  [ _x OF tint ]
     PROP  (- Int.max_signed <= x <= Int.max_signed)
     LOCAL (temp _x (Vint (Int.repr x)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.abs x))))
     SEP   ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ abs_spec ]).

Lemma body_slow_add: semax_body Vprog Gprog f_abs abs_spec.
Proof.
  start_function.
  (** In order to verify an if-command, we can use [forward_if]. Sometimes,
      VST requires your to offer a postcondtion for the whole if-command. At
      this position, it is not necessary because the postcondition of this
      if-command must be the postcondition in function specification.*)
  forward_if.
  {
    forward. (* return - x; *)
    + (* Prove that evaluating [-x] is safe. *)
      (* On the right hand side, [!! _] maps a Coq proposition to an Hoare
         logic assertion. *)
      entailer!.
      change (Int.signed Int.zero) with 0.
      rep_omega.
    + entailer!.
      (* Prove that [Z.abs] is [-x]. *)
      f_equal.
      f_equal.
      rewrite Z.abs_neq.
      - reflexivity.
      - omega.
  }
  {
    forward. (* return x; *)
    entailer!.
    (* Prove that [Z.abs] is [x]. *)
    f_equal.
    f_equal.
    rewrite Z.abs_eq.
    - reflexivity.
    - omega.
  }
Qed.

End Verif_abs.

Module Verif_fact.

Import EV.fact.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The following two C functions calculate the factorial function in two
    different implementations. We will use them to demonstrate how to verify
    function calls and for loops in VST.

      unsigned int fact(unsigned int n) {
        if (n == 0)
          return 1;
        else
          return n * fact(n - 1);
      }

      unsigned int fact_loop (unsigned int n) {
        unsigned int i;
        unsigned int r;
        r = 1;
        for (i = 0; i < n; ++ i)
          r = (i+1) * r;
        return r;
      }

    Specification: *)

Definition fact_spec :=
 DECLARE _fact
  WITH n: nat
  PRE  [ _n OF tuint ]
     PROP  (Z.of_nat n <= Int.max_unsigned)
     LOCAL (temp _n (Vint (Int.repr (Z.of_nat n))))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat (fact n)))))
     SEP   ().

Definition fact_loop_spec :=
 DECLARE _fact_loop
  WITH n: nat
  PRE  [ _n OF tuint ]
     PROP  (Z.of_nat n <= Int.max_unsigned)
     LOCAL (temp _n (Vint (Int.repr (Z.of_nat n))))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat (fact n)))))
     SEP   ().

Print fact.
Check Z.of_nat.
(** The Coq function [fact] has type [nat -> nat] and represents the factorial
    function. Moreover, [Z.of_nat] maps natural numbers to integers. *)

Lemma Nat2Z_nonzero: forall n,
  Z.of_nat n <> 0 ->
  exists n', Z.of_nat n = Z.of_nat n' + 1 /\ n = S n'.
Proof.
  intros.
  destruct n as [| n'].
  + simpl in H.
    omega.
  + exists n'.
    rewrite Nat2Z.inj_succ.
    omega.
Qed.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ fact_spec; fact_loop_spec ]).

Lemma body_fact: semax_body Vprog Gprog f_fact fact_spec.
Proof.
  start_function.
  forward_if.
  { (* If then *)
    assert (n = O). { omega. }
    subst n; clear H0.
    forward. (* return 1; *)
  }
  { (* If else *)
    apply Nat2Z_nonzero in H0.
    destruct H0 as [n' [? ?]].
    rewrite H0.
    (** The original C command is

            return n * fact(n-1);

        Clightgen will automatically split it into two commands. The new
        program has one auxiliary variable [_t'1]:

            _t'1 = fact(n-1);
            return n * _t'1;

        In order to symbolic execute a function call, we should use
        [forward_call]. The parameter of [forward_call] corresponds to the
        logical variable list in the function specification. *)
    forward_call n'. (* _t'1 = fact(n-1); *)
    (** Why do we write [n'] here? Let's take a look at [fact]'s spec.

          DECLARE _fact
            WITH n: nat
            PRE  [ _n OF tuint ]
               PROP  (Z.of_nat n <= Int.max_unsigned)
               LOCAL (temp _n (Vint (Int.repr (Z.of_nat n))))
               SEP   ()
            POST [ tuint ]
               PROP  ()
               LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat (fact n)))))
               SEP   ().

        It says: for any natural number [n], if the program variable [_n]
        has value [n], then the return value is [fact n]. Here, we use [n]
        as a parameter in order to state a family of Hoare triples. Thus,
        when this [fact] function is called, when we want to use this
        assumption, we need to instantiate this parameter. *)
    { (* [LOCAL] clauses of callee's precondition. *)
      entailer!.
      f_equal.
      f_equal.
      f_equal.
      omega.
    }
    { (* [PROP] clauses of callee's precondition *)
      omega.
    }
    forward. (* return n * _t'1; *)
    entailer!.
    f_equal.
    f_equal.
    rewrite <- H0.
    rewrite <- Nat2Z.inj_mul.
    reflexivity.
  }
Qed.

(** Remark 1. This proof is about a recursive function. In the proof,
    we use the assumption that the recursive call obeys the behavior
    described by [fact_spec]. Is this a circlic proof? No. VST proves
    its backend Hoare logic proof rule sound by induction over the steps
    involved in execution. BTW, its soundness can also be proved by induction
    over the number of function calls happened in execution.

    Remark 2. We put a simple restriction on [n]:

        Z.of_nat n <= Int.max_unsigned.

    On one hand, it is necessary. If n is a natural number larger than
    [Int.max_unsigned] (the largest number represented by unsigned 32-bit
    integer), the its 32-bit representation does not represent itself.
    On the other hand, the restriction does not need to be too strong. It is
    true that when [n >= 15], [fact n] is not in the range of unsigned 32-bit
    numbers. However, we can still prove that the return value of our C
    function [fact] is the last 32 bits of [fact n]. Also, the arithmetic
    overflow will not cause run time error since we use [unsigned int] as its
    C type. *)

Lemma body_fact_loop: semax_body Vprog Gprog f_fact_loop fact_loop_spec.
Proof.
  start_function.
  forward. (* r = 1; *)
  (** VST provides [forward_for_simple_bound] for loops with form:

          for (i = lo; i < hi; ++ i) ...

      We can use [hint] to see what argument does this tactic need. *)
  hint.
  (** VST automatically generates lower bounds but requires its users to
      provide upper bounds. *)
  forward_for_simple_bound
    (Z.of_nat n)
    (EX i: Z, EX i': nat,
      PROP (i = Z.of_nat i')
      LOCAL (temp _r (Vint (Int.repr (Z.of_nat (fact i'))));
             temp _n (Vint (Int.repr (Z.of_nat n))))
      SEP   ()).
  { (* Precondition implies the loop invariant. *)
    Exists O.
    entailer!.
  }
  { (* Loop body preserves the loop invariant. *)
    rename i'0 into i'.
    forward. (* r = (i+1) * r; *)
    Exists (S i').
    entailer!.
    split.
    + rewrite Nat2Z.inj_succ.
      omega.
    + f_equal.
      f_equal.
      assert (Z.of_nat i' + 1 = Z.of_nat (S i')).
      { rewrite Nat2Z.inj_succ. omega. }
      rewrite H1.
      rewrite <- Nat2Z.inj_mul.
      reflexivity.
  }
  Intros i'.
  (** This VST tactic [Intros] is similar to Coq's built-in [intros]. It
      extracts existentially quantified variables in preconditions and
      [PROP] clauses in preconditions into Coq assumptions. *)
  apply Nat2Z.inj in H0.
  subst i'.
  forward. (* return r; *)
Qed.

End Verif_fact.

Module Verif_swap.

Import EV.swap.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** In the rest part of this tutorial, we demonstrate verify C programs that
    manipulate memory explicitely using pointers.

      struct int_pair {
        int a;
        int b;
      };

      void int_swap (int * px, int * py) {
        int t;
        t = * px;
        * px = * py;
        * py = t;
      }

      void int_pair_swap (struct int_pair * p) {
        int t;
        t = p -> a;
        p -> a = p -> b;
        p -> b = t;
      }

      void int_pair_swap2 (struct int_pair * p) {
        int_swap (& (p -> a), & (p -> b));
      }
*)

(** In the specification, we need to describe C pointer type. In CompCert,
    [tptr t] represents the pointers to type [t]. Moreover, we need to talk
    about data which is not stored as a program variable but stored in an
    address. Specifically, this [int_swap] function swaps the number stored
    in address [px] and address [py]. For describing data stored in
    addresses, we use [SEP] clauses. For example,

        data_at Tsh tint (Vint x) px

    says [Vint x] is stored at [px]. The second argument [Tsh] reads "top
    share". It says owns full permissions of this unit of memory. We can
    read from it, write to it and even deallocate it. Users can put other
    restrictions on read/write permissions. For convenience, we only use
    [Tsh] in this tutorial. The third argument [tint] describes the type of
    this address.

    Why using this name [SEP]? Because VST uses them to talk about data
    stored in disjoint pieces of memory. In other words,

         SEP   (data_at Tsh tint (Vint x) px;
                data_at Tsh tint (Vint y) py)

    implies that [px] and [py] are different. *)

Definition int_swap_spec :=
 DECLARE _int_swap
  WITH x: int, y: int, px: val, py: val
  PRE  [ _px OF (tptr tint), _py OF (tptr tint) ]
     PROP  ()
     LOCAL (temp _px px; temp _py py)
     SEP   (data_at Tsh tint (Vint x) px;
            data_at Tsh tint (Vint y) py)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tint (Vint x) py;
            data_at Tsh tint (Vint y) px).

(** This is a convenience definition for [struct int_pair]. *)

Definition tpair: type := Tstruct _int_pair noattr.

(** The value of a [int_pair] type is a pair of integers. VST allows users
    to write pairs as [data_at]'s argument when the C type is a struct with
    two fields. *)
Definition int_pair_swap_spec :=
 DECLARE _int_pair_swap
  WITH x: int, y: int, p: val
  PRE  [ _p OF (tptr tpair) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (data_at Tsh tpair (Vint x, Vint y) p)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tpair (Vint y, Vint x) p).

Definition int_pair_swap2_spec :=
 DECLARE _int_pair_swap2
  WITH x: int, y: int, p: val
  PRE  [ _p OF (tptr tpair) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (data_at Tsh tpair (Vint x, Vint y) p)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tpair (Vint y, Vint x) p).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ int_swap_spec; int_pair_swap_spec; int_pair_swap2_spec ]).

Lemma body_int_swap: semax_body Vprog Gprog
                            f_int_swap int_swap_spec.
Proof.
  start_function.
  (** Originally, the C program is only three lines:

        t = * px;
        * px = * py;
        * py = t;

      Clightgen split the second line into two so that every assignment
      command performs at most one read or write operation on data stored
      in memory (in other words, stored at explicitly at addresses). *)
  forward. (* t = * px; *)
  forward. (* _t'1 = * py; *)
  forward. (* * px = _t'1; *)
  forward. (* * py = t; *)
  (** The star operator "*" between two [data_at] is called separating
      conjunction. Specifically, [P * Q] means that [P] and [Q] hold on two
      disjoint pieces of memory. Of course, "*" has commutativity and
      associativity. *)
  entailer!.
Qed.

(** Verifying [int_pair_swap] is easy. Just remember that [data_at] can
    describe complicated C data types. *)
Lemma body_int_pair_swap: semax_body Vprog Gprog
                            f_int_pair_swap int_pair_swap_spec.
Proof.
  start_function.
  forward. (* t = p -> a; *)
  forward. (* _t'1 = p -> b; *)
  forward. (* p -> a = _t'1; *)
  forward. (* p -> b = t; *)
  entailer!.
Qed.

(** Here, we want to redo this proof and introduce more VST's tactics in this
    process. We will demonstrate [unfold_data_at], [gather_SEP], and
    [replace_SEP]. *)
Lemma body2_int_pair_swap: semax_body Vprog Gprog
                            f_int_pair_swap int_pair_swap_spec.
Proof.
  start_function.
  unfold_data_at (data_at Tsh tpair _ _).
  (** Besides [data_at], VST provides [field_at] which can be treated as
      a generalized version of [data_at]. For example,

          field_at Tsh tpair [StructField _a] (Vint x) p

      says [x] is store at field [_a] of a struct [tpair] at address [p].
      The tactic [unfold_data_at] can turn a [data_at] clause with a
      complicated C data type into smaller pieces.If you want to destruct
      [field_at] into even smallest pieces, use [unfold_field_at]. *)
  forward. (* t = p -> a; *)
  (** VST's forward symbolic execution can recognize bot [data_at] and
      [field_at]. But it cannot understand other user defined predicates in
      [SEP] clauses. We will see such examples later. *)
  forward. (* _t'1 = p -> b; *)
  forward. (* p -> a = _t'1; *)
  (** At some position, you might want to gather two [SEP] clauses together,
      or replace one [SEP] clause with an equivalent form. Here are
      examples: *)
  gather_SEP
    (field_at _ _ [StructField _a] _ _)
    (field_at _ _ [StructField _b] _ _).
  replace_SEP 0
    (data_at Tsh tpair (Vint y, Vint y) p).
  (** VST requires us to prove that this replacement is sound. *)
  {
    unfold_data_at (data_at _ _ _ _).
    entailer!.
  }
  forward. (* p -> b = t; *)
  entailer!.
Qed.

(** [int_pair_swap2] is another implementation of [int_pair_swap]; it uses
    [int_swap]. In this proof, we need to mention the address of a struct
    field --- it is called [field_address]. *)
Lemma body_int_pair_swap2: semax_body Vprog Gprog
                            f_int_pair_swap2 int_pair_swap2_spec.
Proof.
  start_function.
  unfold_data_at (data_at Tsh tpair _ _).
  (** Here, [field_address tpair [StructField _a] p] means, [p] is a pointer
      of type [tpair], [_a] is a field of [_a], and this [field_address] is
      the address of [_a] field. *)
  forward_call (x,
                y,
                field_address tpair [StructField _a] p,
                field_address tpair [StructField _b] p).
    (* swap ( & (p -> a), & (p -> b) ); *)
  {
    entailer!.
    (** [offset n p] means [ ( void * ) p + n ] intuitively.
        [field_address_solver] is a tactic to solve equations like [offset_val
        _ p = field_address _ _ p]. *)
    split; f_equal; field_address_solver.
  }
  unfold_data_at (data_at _ tpair _ _).
  entailer!.
Qed.

End Verif_swap.

Module Verif_test_null_first_try.

Import EV.test_null.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Here is a simple function to test whether a pointer is null or not:

      int test_null (int * p) {
        if (p)
          return 1;
        else
          return 0;
      }
*)

(** Specification: *)
Definition test_null_spec :=
 DECLARE _test_null
  WITH p: val
  PRE  [ _p OF (tptr tint) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   ()
  POST [ (tint) ]
    EX b: bool,
     PROP  (b = true <-> p = nullval)
     LOCAL (temp ret_temp (Vint (Int.repr (if b then 0 else 1))))
     SEP   ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ test_null_spec ]).

Lemma body_test_null: semax_body Vprog Gprog
                                    f_test_null test_null_spec.

Proof.
  start_function.
  forward_if.
  (** Here, you see this side-condition:
        [emp |-- denote_tc_test_eq p (Vint Int.zero)]
      It asks whether it is legal to test whether [p] is [zero]. In fact, it is
      UB if [p] is a dangling pointer. However, we don't know whether [p] is
      dangling or not. *)
Abort.

End Verif_test_null_first_try.

Module Verif_test_null_second_try.

Import EV.test_null.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Now, let's try again. This time, we only prove [test_null]'s correctness on
    cases that we own the R/W permission of [p]. *)

Definition test_null_spec :=
 DECLARE _test_null
  WITH p: val, x: val
  PRE  [ _p OF (tptr tint) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (data_at Tsh tint x p)
  POST [ (tint) ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr 1)))
     SEP   (data_at Tsh tint x p).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ test_null_spec ]).

Lemma body_test_null: semax_body Vprog Gprog
                                    f_test_null test_null_spec.

Proof.
  start_function.
  forward_if.
  (** This time, we know [p] cannot be a dangling pointer. *)
  {
    forward. (* return 1 *)
  }
  {
    forward. (* return 0 *)
    (** Why forward directly solve the goal? Because the precondition is already
        a contradiction. It is impossible that [data_at _ _ _ nullval]. *)
  }
Qed.

End Verif_test_null_second_try.

Module Verif_test_null.

Import EV.test_null.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* What if [p] might be [NULL]? We use the following predicate for demonstration. *)

Definition FooPred (p: val): mpred :=
  !! (p = nullval) && emp || EX x: val, data_at Tsh tint x p.

Definition test_null_spec :=
 DECLARE _test_null
  WITH p: val, x: val
  PRE  [ _p OF (tptr tint) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (FooPred p)
  POST [ (tint) ]
    EX b: bool,
     PROP  (b = true <-> p = nullval)
     LOCAL (temp ret_temp (Vint (Int.repr (if b then 0 else 1))))
     SEP   (FooPred p).

(** The following lemma is for VST proof automation. [valid_pointer p] means [p]
    is not a dangling pointer. *)

Lemma FooPred_valid: forall p,
  FooPred p |-- valid_pointer p.
Proof.
  intros.
  unfold FooPred.
  apply orp_left.
  + entailer!.
  + Intros x.
    entailer!.
Qed.

(** The following line add [FooPred_valid] to VST's automation system. *)

Hint Resolve FooPred_valid : valid_pointer.

Definition Gprog : funspecs :=
         ltac:(with_library prog [ test_null_spec ]).

Lemma body_test_null: semax_body Vprog Gprog
                                    f_test_null test_null_spec.

Proof.
  start_function.
  forward_if.
  {
    forward. (* return 1 *)
    Exists false; simpl.
    entailer!.
    assert (p <> nullval) by (intro; subst; auto).
    split; intros; congruence.
  }
  {
    forward. (* return 0 *)
    Exists true; simpl.
    entailer!.
    split; auto.
  }
Qed.

End Verif_test_null.

Module Verif_reverse.

(** The last C program that we verify in this tutorial is the following one.

      struct list {unsigned head; struct list *tail;};

      struct list *reverse (struct list *p) {
        struct list *w, *t, *v;
        w = NULL;
        v = p;
        while (v) {
          t = v->tail;
          v->tail = w;
          w = v;
          v = t;
        }
        return w;
      }
*)

Import EV.reverse.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

(** Inductive definition of linked lists *)
Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h), y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

(** Specification: *)
Definition reverse_spec :=
 DECLARE _reverse
  WITH sigma : list Z, p: val
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep sigma p)
  POST [ (tptr t_struct_list) ]
    EX q:val,
     PROP ()
     LOCAL (temp ret_temp q)
     SEP (listrep (rev sigma) q).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ reverse_spec ]).

(** Whenever you define a new spatial operator, such as [listrep], it is
    useful to populate two hint databases. The [saturate_local] hint is a
    lemma that extracts pure propositional facts from a spatial fact. The
    [valid_pointer] hint is a lemma that extracts a valid-pointer fact from
    a spatial lemma. A pointer is valid if "we" own at least an empty share
    of that piece of memory. C standard says comparison with a dangling
    pointer is undefined behavior. The [valid_pointer] database is used for
    excluding such possibilities. *)

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
  destruct sigma; unfold listrep; fold listrep.
  + entailer!.
  + intros y.
    entailer!.
    entailer!.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma body_reverse: semax_body Vprog Gprog
                                    f_reverse reverse_spec.
Proof.
  start_function.
  forward.  (* w = NULL; *)
  forward.  (* v = p; *)
  forward_while
   (EX s1: list Z, EX s2 : list Z,
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 v)).
  { (* Prove that precondition implies loop invariant *)
    Exists (@nil Z) sigma nullval p.
    entailer!.
    unfold listrep.
    entailer!.
  }
  { (* Prove that loop invariant implies typechecking of loop condition *)
    entailer!.
  }
  {
    assert_PROP (s2 <> nil).
    (** [assert_PROP] tactic adds a proposition to Coq's assumption list.
        This proposition should be derivable from the precondition. *)
    {
      entailer!.
      pose proof proj2 H1 eq_refl.
      subst.
      apply HRE.
    }
    destruct s2 as [ | s2a s2b]; [congruence | clear H0].
    (** We cannot do "forward" directly here because it only recognizes
       [data_at] and [field_at]. *)
    Fail forward.
    (** We can unfold the definition of [listrep] first. *)
    unfold listrep at 2; fold listrep.
    Intros y.
    forward. (* t = v->tail *)
    forward. (* v->tail = w; *)
    forward. (* w = v; *)
    forward. (* v = t; *)
    entailer!.
    Exists (s2a::s1,s2b,v,y).
    entailer!.
    + simpl. rewrite app_ass. auto.
    + unfold listrep at 3; fold listrep.
      Exists w. entailer!.
  }
  forward.  (* return w; *)
  Exists w; entailer!.
  rewrite (proj1 H1) by auto.
  unfold listrep at 2; fold listrep.
  entailer!.
  rewrite <- app_nil_end, rev_involutive.
  auto.
Qed.

End Verif_reverse.

(** Here is a cheat sheet of VST's tactic library (some other tactics are not
    listed):

      - hint:
            finding out what to do when you do not know what to do

      - forward:
            forward symbolic execution for assignments, break, continue, and
            return

      - forward_if:
            for if commands

      - forward_whie:
            for while commands

      - forward_for_simple_bound:
            for "for" commands

      - forward_call
            forward symbolic execution of function calls

      - Intros
            extracting existential variables and propositions in preconditions
            and left-hand-side assertions

      - Exists
            instantiating existential variables right-hand-side assertions

      - entailer!
            simplifying or solving assertion derivations

      - unfold_data_at
            unfolding data_at

      - unfold_field_at
            unfolding field_at

      - gather_SEP
            gather multiple [SEP] clauses

      - replace_SEP
            replacing a [SEP] clause with an equivalent one
*)
(* Mon May 13 04:52:44 UTC 2019 *)

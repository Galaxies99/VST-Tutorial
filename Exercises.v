Require Import VST.floyd.proofauto.
Require EV.max3 EV.swap EV.tri EV.gcd EV.append.

(* ################################################################# *)
(** * Task 1: The Max of Three *)

Module Verif_max3.

Import EV.max3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [max3]:

      int max3(int x, int y, int z)
      {
        if (x < y)
          if (y < z)
            return z;
          else
            return y;
        else
          if (x < z)
            return z;
          else
            return x;
      }

    Specification:
*)

Definition max3_spec :=
 DECLARE _max3
  WITH x: Z, y: Z, z: Z
  PRE  [ _x OF tint, _y OF tint, _z OF tint ]
     PROP  (Int.min_signed <= x <= Int.max_signed;
            Int.min_signed <= y <= Int.max_signed;
            Int.min_signed <= z <= Int.max_signed)
     LOCAL (temp _x (Vint (Int.repr x));
            temp _y (Vint (Int.repr y));
            temp _z (Vint (Int.repr z)))
     SEP   ()
  POST [ tint ]
    EX r: Z, 
     PROP  (r = x \/ r = y \/ r = z;
            r >= x;
            r >= y;
            r >= z)
     LOCAL (temp ret_temp (Vint (Int.repr r)))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ max3_spec ]).

Lemma body_max3: semax_body Vprog Gprog f_max3 max3_spec.
Proof.
  start_function.
  forward_if.
  {
    forward_if.
    {
      forward.
      Exists z.
      entailer!.
    }
    {
      forward.
      Exists y.
      entailer!.
    }
  }
  {
    forward_if.
    {
      forward.
      Exists z.
      entailer!.
    }
    {
      forward.
      Exists x.
      entailer!.
    }
  }
Qed.

End Verif_max3.
(** [] *)

(* ################################################################# *)
(** * Task 2: Swap by Arith *)

Module Verif_swap.

Import EV.swap.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [uint_swap_arith]:

      void uint_swap_arith (unsigned int * px, unsigned int * py) {
        * px = * px + * py;
        * py = * px - * py;
        * px = * px - * py;
      }

    Specification:
*)

Definition uint_swap_arith_spec :=
 DECLARE _uint_swap_arith
  WITH x: Z, y: Z, px: val, py: val
  PRE  [ _px OF (tptr tuint), _py OF (tptr tuint) ]
     PROP  ()
     LOCAL (temp _px px; temp _py py)
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) px;
            data_at Tsh tuint (Vint (Int.repr y)) py)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) py;
            data_at Tsh tuint (Vint (Int.repr y)) px).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ uint_swap_arith_spec ]).

Lemma body_uint_swap_arith: semax_body Vprog Gprog
                              f_uint_swap_arith uint_swap_arith_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
  autorewrite with sublist. 
  entailer!.
Qed.

End Verif_swap.
(** [] *)

(* ################################################################# *)
(** * Task 3: Tri *)

Module Verif_tri.

Import EV.tri.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C program:

      unsigned int tri_for (int n) {
        unsigned int s;
        int i;
        s = 0;
        for (i = 0; i < n; ++ i)
          s = s + i;
        return s;
      }

      unsigned int tri_while (int n) {
        unsigned int s;
        s = 0;
        while (n > 0) {
          n = n - 1;
          s = s + n;
        }
        return s;
      }

    Specification:
*)

Definition tri_spec (_tri_name: ident) :=
 DECLARE _tri_name
  WITH n: Z
  PRE  [ _n OF tint ]
     PROP  (0 <= n <=Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n)))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (n * (n-1)/2))))
     SEP   ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [ tri_spec _tri_for; tri_spec _tri_while ]).

(** Hint: in your proof, lemma [Z_div_plus_full] and tactic [ring] might be
    helpful. (Ring is just a fancier version of omega which can also handle
    multiplication. *)
Lemma body_tri_for: semax_body Vprog Gprog
                            f_tri_for (tri_spec _tri_for).
Proof.
  start_function.
  forward.
  forward_for_simple_bound n
    (EX i: Z, EX i': nat,
      PROP (i = Z.of_nat i')
      LOCAL (temp _s (Vint (Int.repr (i * (i - 1) / 2)));
             temp _n (Vint (Int.repr n)))
      SEP ()).
  {
    Exists O.
    entailer!.    
  }
  {
    rename i'0 into i'.
    forward.
    Exists (S i').
    entailer!.
    split.
    - rewrite Nat2Z.inj_succ; auto.
    - f_equal.
      f_equal.
      replace (Z.of_nat i' + 1 - 1) with (Z.of_nat i'); [ | ring].
      assert (forall z: Z, (z * (z - 1) / 2 + z = (z + 1) * z / 2)%Z). 
      {
        intro. rewrite <- Z_div_plus; [ | omega].
        assert (z * (z - 1) + z * 2 = (z + 1) * z)%Z; [ring | ].
        rewrite <- H1; auto.
      }
      symmetry. auto.
  }
  Intros i'.
  subst.
  forward.
Qed.

Lemma body_tri_while: semax_body Vprog Gprog
                            f_tri_while (tri_spec _tri_while).
Proof.
  start_function.
  forward.
  forward_while 
    (EX n': Z, EX s': Z,
      (PROP ((n' * (n' - 1) / 2 + s' = n * (n - 1) / 2)%Z; 0 <= n' <= Int.max_signed)
       LOCAL (temp _n (Vint (Int.repr n'));
              temp _s (Vint (Int.repr s')))
       SEP ())).
  {
    Exists n.
    Exists 0.
    entailer!.
  }
  { 
    entailer!.
  }
  {
    forward. (* n = n - 1 *)
    forward. (* s = s + n *) 
    Exists (n' - 1 , s' + (n' - 1)).
    entailer!.
    split.
    - rewrite <- H0.
      rewrite Z.add_assoc, Z.add_shuffle0.
      apply Z.add_cancel_r.
      rewrite <- Z_div_plus; [ | omega].
      assert ((n' - 1) * (n' - 1 - 1) + (n' - 1) * 2 = n' * (n' - 1))%Z; [ring | ].
      rewrite H2; auto.
    - split; [omega | f_equal; f_equal; omega].
  }
  assert (n' = 0); [omega | ].
  subst.
  replace (0 * (0 - 1) / 2 + s') with s' in H0; auto.
  subst.
  forward.
Qed.

End Verif_tri.
(** [] *)

(* ################################################################# *)
(** * Task 4: Greatst Common Divisor *)

Module Verif_gcd.

Import EV.gcd.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [gcd]:

      int gcd(int n, int m) {
        int r = m % n;
        if (r == 0)
          return n;
        else
          return gcd(r, n);
      }

    This function calculates the greatest common divisor of two integers.
    [Z.gcd] is defined as part of Coq's standard library. Using this definition,
    we can write specification as follows:
*)

Definition gcd_spec :=
 DECLARE _gcd
  WITH n: Z, m: Z
  PRE  [ _n OF tint, _m OF tint ]
     PROP  (0 < n <= Int.max_signed;
            0 <= m <= Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n));
            temp _m (Vint (Int.repr m)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.gcd n m))))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ gcd_spec ]).

(** We first provide three useful lemmas. You may use it in your proofs. *)

Lemma aux1: forall n, 0 < n <= Int.max_signed -> Int.repr n <> Int.zero.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + omega.
  + rep_omega.
    (* This VST tactic is used to handle linear programming with 32-bit bounds.
       You can use it in your own proofs. *)
  + rep_omega.
Qed.

Lemma aux2: forall m, 0 <= m <= Int.max_signed -> Int.repr m <> Int.repr Int.min_signed.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + rep_omega.
    (* [rep_omega] can also solve normal linear proof goals. The proof goal
       does not need to be [repable_signed]. *)
  + rep_omega.
  + rep_omega.
Qed.

Lemma mods_repr: forall n m,
  Int.min_signed <= n <= Int.max_signed ->
  Int.min_signed <= m <= Int.max_signed ->
  Int.mods (Int.repr m) (Int.repr n) = Int.repr (Z.rem m n).
(* Here [Z.rem] is the remainder of [m divides n]. *)
Proof.
  intros.
  unfold Int.mods.
  rewrite Int.signed_repr by rep_omega.
  rewrite Int.signed_repr by rep_omega.
  reflexivity.
Qed.

(** Now, fill in the holes in the following proof. *)
Lemma body_gcd: semax_body Vprog Gprog f_gcd gcd_spec.
Proof.
  start_function.
  forward.
  {
    (* Hint: remember that you can use [aux1] and [aux2]. *)
    entailer!.
    split; [apply aux1; auto | ].
    intro.
    assert (Int.repr m <> Int.repr Int.min_signed) by (apply aux2; auto).
    tauto.
  }
  rewrite mods_repr by rep_omega.
  forward_if.
  {
    (* Hint: you can always use [Search] to find useful theorems in Coq's
       standard library and VST's library. For example, [Z.gcd_rem] may be
       useful. *)
    forward.
    entailer!.
    f_equal.
    f_equal.
    replace (Z.gcd n m) with (Z.gcd (Z.rem m n) n); [ | apply Z.gcd_rem; omega].
    apply repr_inj_signed in H1.
    replace (Z.rem m n) with 0.
    rewrite Z.gcd_0_l.
    symmetry. apply Z.abs_eq.
    omega.
    assert (Z.rem m n <= m); [apply Zquot.Zrem_le; omega | ].
    assert (0 <= Z.rem m n); [apply Z.rem_nonneg; omega | ].
    rep_omega.
    rep_omega.
  }
  {
    assert (Z.rem m n <> 0).
    { 
      unfold not; intro.
      rewrite H2 in H1.
      apply H1; reflexivity.
    }
    forward_call (Z.rem m n, n).
    {
      split; [ | omega].
      assert (0 <= Z.rem m n); [apply Z.rem_nonneg; omega | ].
      assert (Z.rem m n <= m); [apply Zquot.Zrem_le; omega | ].
      rep_omega.
    }
    forward.
    entailer!.
    f_equal.
    f_equal.
    apply Z.gcd_rem.
    omega.
  }
Qed.

End Verif_gcd.

Module List_seg.

(* ################################################################# *)
(** * Task 5. List Segments *)

Import EV.append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** In this part, we will verify two C functions:

      struct list {
        unsigned int head;
        struct list * tail;
      };

      unsigned sumlist (struct list *p) {
        unsigned s = 0;
        struct list * t = p;
        unsigned h;
        while (t) {
           h = t->head;
           t = t->tail;
           s = s + h;
        }
        return s;
      }

      struct list *append (struct list *x, struct list *y) {
        struct list *t, *u;
        if (x==NULL)
          return y;
        else {
          t = x;
          u = t->tail;
          while (u!=NULL) {
            t = u;
            u = t->tail;
          }
          t->tail = y;
          return x;
        }
      }

    Using [listrep], we can state their specification.
*)

Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

Definition sum_int (sigma: list Z): Z :=
  fold_right Z.add 0 sigma.

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sigma : list Z, p: val
  PRE [ _p OF (tptr t_struct_list) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (sum_int sigma))))
     SEP   (listrep sigma p).

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r).

(** Both C functions traverse a linked list using a while loop. Thus, the
    keypoint of verifying them is to write down the correct loop invariant.
    The following diagram demonstrates an intermediate state in traversing.

        +---+---+            +---+---+   +---+---+   +---+---+   
  x ==> |   |  ===> ... ===> |   | y ==> |   | z ==> |   |  ===> ... 
        +---+---+            +---+---+   +---+---+   +---+---+

      | <==== Part 1 of sigma =====> |            | <== Part 2 ==> |

      | <========================== sigma =======================> |

    To properly describe loop invariants, we need a predicate to describe
    the partial linked list from address [x] to address [y]. We provide its
    definition for you. But it is your task to prove its important properties.
*)

Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.

Arguments lseg sigma x y : simpl never.

Lemma singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x |-- lseg [a] x y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  entailer!.
Qed.
(** [] *)

(** In the next lemma, try to understand how to use [sep_apply]. *)
Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval |-- listrep sigma x.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!. 
  + unfold lseg; fold lseg. 
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    (** The following tactic "apply" [IHsigma] on the left side of derivation. *)
    sep_apply (IHsigma u).
    entailer!.
Qed.

Lemma lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros.
  revert x; induction s1; intros.
  - unfold lseg; fold lseg.
    entailer!.
    rewrite app_nil_l.
    entailer!.
  - replace ((a :: s1) ++ s2) with (a :: s1 ++ s2); [ | apply app_comm_cons].
    unfold lseg; fold lseg.
    Intros u.
    Exists u.
    sep_apply (IHs1 u).
    entailer!.
Qed.
(** [] *)

Lemma lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros.
  revert x; induction s1; intros.
  - unfold listrep; fold listrep.
    unfold lseg; fold lseg.
    rewrite app_nil_l.
    entailer!.
  - replace ((a :: s1) ++ s2) with (a :: s1 ++ s2); [ | apply app_comm_cons].
    unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply (IHs1 u).
    entailer!.
Qed.
(** [] *)

(** Try to use prove the following assertion derivation use the lemmas above.
    The first step is done for you. *)
Example lseg_ex: forall s1 s2 s3 x y z,
  lseg s1 x y * lseg s2 y z * lseg s3 z nullval |-- listrep (s1 ++ s2 ++ s3) x.
Proof.
  intros.
  sep_apply lseg_lseg.
  sep_apply lseg_nullval.
  sep_apply lseg_list.
  rewrite app_assoc.
  entailer!.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 6. Sum of a List *)

(** Now, you are going to prove [sumlist] correct. The following lemmas are
    copied from [verif_reverse2] for proof automation. *)

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
  destruct sigma; unfold listrep; fold listrep;
  intros; normalize.
  auto with valid_pointer.
  apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; auto.
  simpl; computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Module sumlist.

(** Another auxiliary lemma. Hint: use [Search] when you need to find a
    lemma. *)
Lemma sum_int_snoc:
  forall a b, sum_int (a++b :: nil) = (sum_int a) + b.
Proof.
  induction a; intros; [simpl; omega | ].
  simpl. 
  rewrite <- Z.add_assoc.
  apply Z.add_cancel_l.
  apply IHa.
Qed.
(** [] *)

Definition Gprog : funspecs :=
  ltac:(with_library prog [ sumlist_spec ]).

(** Hint: take a look at Verif_reverse and learn its proof strategy. *)
Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while
    (EX s1: list Z, EX s2: list Z,
     EX t: val, EX s: Z,
        PROP (sigma = s1 ++ s2; s = sum_int s1)
        LOCAL (temp _t t; temp _p p; temp _s (Vint (Int.repr s)))
        SEP (lseg s1 p t; listrep s2 t)).
  {
    Exists (@nil Z) sigma p 0.
    unfold lseg; fold lseg.
    entailer!.
  }
  {
    entailer!.
  }
  {
    assert_PROP(s2 <> nil). {
      entailer!.
      assert(t = nullval); [apply H1; auto | subst].
      apply HRE.
    }
    destruct s2 as [ | s2a s2b]; [congruence | clear H1].
    unfold listrep.
    Intros y. 
    forward.
    forward.
    forward.
    entailer!.
    Exists ((s1 ++ [s2a]), s2b, y, sum_int (s1 ++ [s2a])).
    entailer!.
    - split.
      + induction s1; auto; simpl.
        apply cons_congr; auto.
      + f_equal. f_equal. unfold sum_int.
        apply sum_int_snoc.
    - fold listrep. 
      sep_apply singleton_lseg.
      entailer!.
      sep_apply pull_left_special0.
      sep_apply lseg_lseg.
      entailer!.
  }
  forward.
  entailer!.
  f_equal.
  f_equal.
  assert(s2 = []); [apply H1; auto | subst].
  rewrite app_nil_r; auto.
  apply lseg_list.
Qed.
(** [] *)

End sumlist.

(* ################################################################# *)
(** * Task 7: Append *)

Module append.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append_spec ]).

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function.
  forward_if.
  {
    forward.
    Exists y.
    assert (s1 = []); [apply H0; auto | subst].
    unfold listrep; fold listrep.
    simpl. entailer!.
  }
  forward.
  assert_PROP (exists s1a s1b, s1 = s1a :: s1b);
    [entailer!; destruct s1; [tauto | eauto] | ].
  destruct H0 as [s1a [s1b ?]].
  subst s1.
  unfold listrep at 1; fold listrep.
  Intros u'.
  forward.
  forward_while
    (EX (s11: list Z) (s12: list Z) (t: val) (u: val) (mid: Z),
        PROP (s1a :: s1b = s11 ++ mid :: s12)
        LOCAL (temp _t t; temp _u u; temp _x x; temp _y y)
        SEP (lseg s11 x t; listrep s12 u; listrep s2 y;
        data_at Tsh t_struct_list (Vint (Int.repr mid), u) t))%assert. 
  {
    Exists (@nil Z) s1b x u' s1a.
    unfold lseg. 
    entailer!.
  }
  {
    entailer!.
  }
  {
    forward.
    assert_PROP(s12 <> nil); [entailer!; apply HRE, H1; auto | ].
    destruct s12 as [ | s12a s12b]; [tauto | clear H1].
    unfold listrep at 1; fold listrep.
    Intros y0. 
    forward.
    entailer!.
    Exists (s11 ++ [mid], s12b, u, y0, s12a).
    entailer!.
    - rewrite H0.
      rewrite <- app_assoc.
      induction s11; auto.
    - entailer!.
      sep_apply singleton_lseg.
      sep_apply pull_left_special0.
      sep_apply lseg_lseg.
      entailer!.
  } 
  forward.
  forward.
  Exists x.
  assert(s12 = []); [apply H1; auto | subst].
  sep_apply singleton_lseg.
  unfold listrep at 1; fold listrep.
  sep_apply pull_left_special0.
  sep_apply lseg_lseg.
  sep_apply lseg_list.
  rewrite H0.
  entailer!.
Qed.
(** [] *)

End append.

(* ################################################################# *)
(** * Task 8: List box segments *)

(** Now, consider this alternative implementation of append:

      void append2(struct list * * x, struct list * y) {
        struct list * h;
        h = * x;
        while (h != NULL) {
          x = & (h -> tail);
          h = * x;
        }
        * x = y;
      }

    You should prove:
*)

Module append2.

Definition append2_spec :=
 DECLARE _append2
  WITH x: val, y: val, s1: list Z, s2: list Z, p :val
  PRE [ _x OF (tptr (tptr t_struct_list)) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (data_at Tsh (tptr t_struct_list) p x;
          listrep s1 p;
          listrep s2 y)
  POST [ tvoid ]
     EX q: val,
     PROP()
     LOCAL()
     SEP (data_at Tsh (tptr t_struct_list) q x;
          listrep (s1 ++ s2) q).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append2_spec ]).

(** You may find it inconvenient to complete this proof directly using [listrep]
    and [lseg]. You may need another predicate for [list box segment].

         +---+---+            +---+---+   +---+---+   +---+---+   
   p ==> |   |  ===> ... ===> |   |   ==> |   |   ==> |   |  ===> ... 
         +---+---+            +---+---+   +---+---+   +---+---+

       | <====            list segment      =====> |

 | <====           list box segment     =====> |

    Try to define this predicate by yourself and prove [lbseg_lseg].
*)

Fixpoint lbseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX (u: val), data_at Tsh (tptr t_struct_list) u x *
                          field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr h)) u *
                          lbseg hs (field_address t_struct_list [StructField _tail] u) y
  end.
(** [] *)

Lemma lbseg_lseg: forall s3 x y z,
  lbseg s3 x y * data_at Tsh (tptr t_struct_list) z y |--
  EX y', data_at Tsh (tptr t_struct_list) y' x * lseg s3 y' z.
Proof.
  intros s3.
  induction s3; intros.
  - unfold lbseg; fold lbseg.
    unfold lseg; fold lseg.
    Exists z.
    entailer!.
  - unfold lbseg; fold lbseg.
    unfold lseg; fold lseg.
    Intros u. Exists u.
    sep_apply IHs3.
    Intros y'. Exists y'. 
    unfold_data_at (data_at Tsh t_struct_list _ _).
    entailer!.
Qed.
(** [] *)

Lemma lbseg_app_r: forall s v x x' h,
  lbseg s x x' *
  field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr v)) h *
  data_at Tsh (tptr t_struct_list) h x'
  |-- lbseg (s ++ [v]) x
      (field_address t_struct_list [StructField _tail] h).
Proof.
  intros s.
  induction s; intros.
  - rewrite app_nil_l.
    unfold lbseg; fold lbseg.
    Exists h.
    entailer!.
  - unfold lseg; fold lseg.
    rewrite <- app_comm_cons.
    unfold lbseg; fold lbseg.
    Intro u. Exists u.
    entailer!.
    sep_apply IHs.
    entailer!.
Qed.

(** Hint: adding more lemmas for [lbseg] may be useful. *)
Lemma body_append2: semax_body Vprog Gprog f_append2 append2_spec.
  start_function.
  forward.
  forward_while
    (EX (s11 s12: list Z) (h: val) (x': val),
        PROP (s1 = s11 ++ s12)
        LOCAL (temp _h h; temp _x x'; temp _y y)
        SEP (lbseg s11 x x'; listrep s12 h; 
             listrep s2 y; data_at Tsh (tptr t_struct_list) h x'))%assert.
  {
    Exists (@nil Z) s1 p x.
    unfold lbseg; fold lbseg.
    entailer!.
  }
  {
    entailer!.
  }
  {
    assert_PROP (s12 <> []); [entailer!; apply HRE, H0; auto | ].
    destruct s12 as [ | s12a s12b]; [exfalso; auto | subst].
    unfold listrep; fold listrep.
    forward.
    - entailer!. unfold is_pointer_or_null in PNh.
      unfold nullval in HRE.
      destruct h; auto.
      destruct (Archi.ptr64) eqn: HArchi; auto.
      rewrite PNh in HRE; exfalso; auto.
    - clear H0. simpl.
      Intros y0.
      unfold_data_at (data_at Tsh t_struct_list _ _).
      Fail forward.
      assert_PROP (offset_val 4 h = field_address t_struct_list [StructField _tail] h). {
        entailer!.
        rewrite field_address_offset; auto.
      }
      forward.
      entailer!.
      Exists (s11 ++ [s12a], s12b, y0, field_address t_struct_list [StructField _tail] h).
      entailer!.
      + rewrite <- app_assoc. induction s11; auto.
      + entailer!. sep_apply lbseg_app_r. entailer!.
  }
  forward.
  sep_apply lbseg_lseg.
  Intro y'.
  Exists y'.
  entailer!.
  assert (s12 = []); [apply H2; auto | subst].
  unfold listrep; fold listrep.
  rewrite app_nil_r.
  entailer!.
  sep_apply lseg_list.
  entailer!.
Qed.
(** [] *)

End append2.

End List_seg.

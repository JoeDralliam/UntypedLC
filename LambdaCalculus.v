Require Import Arith.

Inductive scoped_term {scope : nat} : Set :=
| TVar : nat -> @scoped_term scope
| TApp : @scoped_term scope -> @scoped_term scope -> @scoped_term scope
| TAbstr : @scoped_term (S scope) -> @scoped_term scope.

(*
Inductive appears_free_in (x : identifier) : term -> Prop :=
| afi_var : appears_free_in x (TVar x)
| afi_app1 : forall (t1 t2 : term),
               appears_free_in x t1 -> appears_free_in x (TApp t1 t2)
| afi_app2 : forall (t1 t2 : term),
               appears_free_in x t2 -> appears_free_in x (TApp t1 t2)
| afi_abstr : forall (y : identifier) (t : term),
                x <> y -> appears_free_in x t -> appears_free_in x (TAbstr y t).

Inductive appears_bound_in (x : identifier) : term -> Prop :=
| abi_app1 : forall (t1 t2 : term),
               appears_bound_in x t1 -> appears_bound_in x (TApp t1 t2)
| abi_app2 : forall (t1 t2 : term),
               appears_bound_in x t2 -> appears_bound_in x (TApp t1 t2)
| abi_abstr : forall (y : identifier) (t : term),
                x <> y -> appears_bound_in x t -> appears_bound_in x (TAbstr y t)
| abi_capture : forall (t : term),
                  appears_free_in x t -> appears_bound_in x (TAbstr x t).

 *)


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint rescope {scope : nat} (s : @scoped_term scope) (deep: nat) : @scoped_term (S scope) :=
  match s with
    | TVar k =>
      if le_lt_dec deep k
      then TVar (S k)
      else TVar k
    | TApp t1 t2 => TApp (rescope t1 deep) (rescope t2 deep)
    | TAbstr t => TAbstr (rescope t (S deep))
  end.

Fixpoint subst {scope : nat}
         (var : nat) (s : @scoped_term scope) (t : @scoped_term (S scope)) :=
  match t with
    | TApp t1 t2 => TApp (subst var s t1) (subst var s t2)
    | TVar v =>
      match nat_compare var v with
        | Lt => TVar (pred v)
        | Eq => s
        | Gt => TVar v
      end
    | TAbstr t1 => TAbstr (subst (S var) (rescope s 0) t1)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "u '==>' v" (at level 20).

Inductive beta_reduction {s : nat} : @scoped_term s -> @scoped_term s -> Prop :=
| BApp1 : forall (t1 t1' t2 : @scoped_term s),
            beta_reduction t1 t1' ->
            beta_reduction (TApp t1 t2) (TApp t1' t2)
| BApp2 : forall (t1 t2 t2' : @scoped_term s),
            beta_reduction t2 t2' ->
            beta_reduction (TApp t1 t2) (TApp t1 t2')
| BRed : forall (u : @scoped_term (S s)) (v : @scoped_term s),
           beta_reduction (TApp (TAbstr u) v) ([0 := v]u).

Module Confluence.
  Require Import Relation_Definitions.
  Require Import Operators_Properties.
  Require Import Relation_Operators.

  Variable A : Type.
  Variable R : relation A.
  Definition RStar := clos_refl_trans_1n A R.

  Inductive RRefl : relation A :=
  | r_refl : forall (x : A), RRefl x x
  | r_step : forall (x y : A),  R x y -> RRefl x y.

  Definition confluent_from (x : A) : Prop :=
    forall (y z : A),
      RStar x y -> RStar x z ->
      exists (w : A), RStar y w /\ RStar z w.


  Definition confluent : Prop :=
    forall (x : A), confluent_from x.

  Definition locally_confluent : Prop :=
    forall (x y z : A),
      R x y -> R x z ->
      exists (w : A), RStar y w /\ RStar z w.

  Definition strongly_confluent : Prop :=
    forall (x y z : A),
      R x y -> R x z ->
      exists (w : A), RRefl y w /\ RRefl z w.

  Definition church_rosser : Prop :=
    forall (x y : A),
      (clos_refl_sym_trans_1n A R) x y
      <-> exists (w : A), RStar x w /\ RStar y w.


  Inductive terminating_from (x : A) :=
  | tf_imm : (forall (y : A),  ~(R x y)) -> terminating_from x
  | tf_step : (forall (y : A),  R x y -> terminating_from y) -> terminating_from x.

  Definition terminating := forall (x : A), terminating_from x.

  Lemma confluence_implies_locally :
    confluent -> locally_confluent.
  Proof. unfold confluent, locally_confluent.
         intros H x y z H1 H2.
         apply (clos_rt1n_step A R x y) in H1.
         apply (clos_rt1n_step A R x z) in H2.
         apply (H x y z H1 H2).
  Qed.

  Lemma end_of : forall (x : A),
                   (forall (y : A),  ~(R x y)) -> forall (y : A),  RStar x y -> x = y.
  Proof. intros x H y G.
         induction G.
         - reflexivity.
         - contradict (H y H0).
  Qed.

  Lemma rstar_trans : forall x y z, RStar x y -> RStar y z -> RStar x z.
  Proof. intros x y z Hxy Hyz.
         unfold RStar. rewrite <- clos_rt_rt1n_iff.
         apply rt_trans with y ; apply clos_rt_rt1n_iff ; assumption.
  Qed.

  Lemma confluence_trans :
    forall (x y : A), RStar x y -> confluent_from x -> confluent_from y.
  Proof. intros x y HR Hc z1 z2 HR1 HR2.
         apply Hc ; apply rstar_trans with y ; auto.
  Qed.


  Lemma loc_confl_termination :
    locally_confluent ->
    forall (x : A),
      (forall (y : A), R x y -> confluent_from y) -> confluent_from x.
  Proof. unfold locally_confluent.
    intros lc x Hi y z Hy Hz.
    destruct Hy ; destruct Hz.
    - exists x. split ; apply rt1n_refl.
    - exists z. split ; [apply rt1n_trans with y ; assumption | apply rt1n_refl].
    - exists z0. split ; [apply rt1n_refl | apply rt1n_trans with y ; assumption].
    - elim (lc x y y0 H H0). intros t [s0 s].
      elim (Hi y H z0 t). elim (Hi y0 H0 z t).
      intros x0 [Hzx0 Ht0] x1 [Hzx1 Htx1].
      assert (confluent_from t). apply confluence_trans with y. assumption. auto.
      elim (H1 x0 x1). intros x2 [Hx0x2 Hx1x2].
      exists x2.
      split.
      apply rstar_trans with x1 ; assumption.
      apply rstar_trans with x0 ; assumption.
      assumption. assumption. assumption. assumption. assumption. assumption.
  Qed.

  Theorem newmann :
    terminating -> locally_confluent -> confluent.
  Proof. unfold terminating, locally_confluent, confluent.
         intros term lc x.
         induction (term x) ; apply loc_confl_termination ; try assumption.
         - intros y Hr. contradict (n y Hr).
  Qed.

  Lemma rt_implies_srt : forall (x y : A),
                           RStar x y -> (clos_refl_sym_trans_1n A R x y).
  Proof. intros x y H. induction H.
         - apply rst1n_refl.
         - apply rst1n_trans with y ; [left | idtac] ; assumption.
  Qed.

  Theorem cr :
    church_rosser <-> confluent.
  Proof. unfold church_rosser, confluent.
    split.
    - intros cr. intros x y z Hy Hz. apply cr.
      apply clos_rst1n_trans with x ; [apply clos_rst1n_sym | idtac] ; apply rt_implies_srt ; assumption.
    - intros conf x y. split.
      + intros rst. induction rst.
        * exists x. split ; apply rt1n_refl.
        * inversion IHrst as [w [Hyw Hzw]]. elim H.
          intros Hxy.
          exists w. split ; [apply rt1n_trans with y | idtac] ; assumption.
          intros Hyx. apply (clos_rt1n_step A R y x) in Hyx.
          elim (conf y x w Hyx Hyw). intros s [Hxs Hws].
          exists s. split ; [idtac | apply rstar_trans with w] ; assumption.
      + intros H. inversion H as [w [Hxw Hyw]].
        apply clos_rst1n_trans with w ; [ idtac | apply clos_rst1n_sym] ; apply rt_implies_srt ; assumption.
  Qed.

  Lemma refl_implies_rt :
    forall (x y : A),  RRefl x y -> RStar x y.
  Proof.
    intros x y H. induction H. apply rt1n_refl. apply clos_rt1n_step. assumption.
  Qed.

  Inductive path_of_length : nat -> A -> A -> Prop :=
  | pl_refl : forall (x : A),  path_of_length 0 x x
  | pl_trans : forall (x y z : A) (n : nat),
                 R x y ->
                 path_of_length n y z ->
                 path_of_length (S n) x z.

  Lemma exists_length :
    forall (x y : A),  RStar x y -> exists n, path_of_length n x y.
  Proof.
    intros x y H. induction H.
    - exists 0. apply pl_refl.
    - inversion IHclos_refl_trans_1n as [n Hn].
      exists (S n). apply pl_trans with y ; assumption.
  Qed.

  Lemma length_relates :
    forall (n : nat) (x y : A),  path_of_length n x y -> RStar x y.
  Proof.
    intros n x y Hn. induction Hn.
    - apply rt1n_refl.
    - apply rt1n_trans with y ; assumption.
  Qed.

  Lemma strongly_one_sided :
    strongly_confluent ->
    forall (x y z : A),
      R x y -> RStar x z ->
      exists w,  RStar y w /\ RStar z w.
  Proof.
    intros sc x y z Hxy Hxz. generalize dependent y.
    induction Hxz as [| x z0 z ].
    - intros y Hxy.
      exists y. split. apply rt1n_refl. apply clos_rt1n_step. assumption.
    - intros y Hxy.
      elim (sc x y z0 Hxy H).
      intros w [Hyw Hz0w].
      inversion Hz0w ; subst.
      + exists z. split.
       * apply rstar_trans with w ;
           [apply refl_implies_rt | idtac] ; assumption.
       * apply rt1n_refl.
      + apply IHHxz in H0. elim H0.
        intros t [Hwt Hzt]. exists t.
        split.
        apply rstar_trans with w ; [apply refl_implies_rt | idtac] ; assumption.
        assumption.
  Qed.

Lemma strongly_length :
    strongly_confluent ->
    forall (n : nat) (x y z : A),
      path_of_length n x y -> RStar x z ->
      exists w, RStar y w /\ RStar z w.
  Proof.
    intros sc n. induction n.
    - intros x y z Hxy Hxz.
      inversion Hxy ; subst ; clear Hxy.
      exists z. split. assumption. apply rt1n_refl.
    - intros x y z Hxy Hxz.
      inversion Hxy ; subst ; clear Hxy.
      elim (strongly_one_sided sc x y0 z H0 Hxz).
      intros u [Hy0u Hzu].
      elim (IHn y0 y u H1 Hy0u).
      intros v [Hyv Huv].
      exists v. split. assumption. apply rstar_trans with u ; assumption.
  Qed.

  Theorem strongly_confluent_confluent :
    strongly_confluent -> confluent.
  Proof.
    unfold strongly_confluent, confluent.
    intros sc x y z Hy Hz.
    elim (exists_length x y Hy).
    intros n Hnxy.
    apply strongly_length with (n:=n) (x:=x) ; assumption.
  Qed.
End Confluence.

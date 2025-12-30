From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.
From Tutorial Require Import Imp FiniteSimulation.

Require Import Lia.

Set Implicit Arguments.

Section DEMO.
  (** We will prove that src refines tgt, using the finite simulation. *)

  Definition src0 : com :=
    <{ ret 0 }>.

  Definition tgt0 : com :=
    <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (Imp_Program_Mem src0) (Imp_Program_Mem tgt0).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src0, tgt0, Imp_init. ss.
    (* Same as 'econstructor 4.' or 'eapply sim_silentT.' *)
    econs 4.
    { ss. }
    ss. i. inv H.
    (* We have two cases: 1. normal step, 2. step is not defined. 
       Step is defined for this case, so the second case is trivially solved. 
     *)
    2:{ exfalso. eapply UNDEF. repeat econs. }
    inv STEP. ss. split; auto.
    econs 4.
    { ss. }
    ss. i. inv H.
    2:{ exfalso. eapply UNDEF. repeat econs. }
    inv STEP. ss. split; auto.
    (* As you can see, simulation proofs can get very length.
       Thus one usually defines a tactic that automatically takes care of trivial steps.
       So let us define some simple tactics first.
     *)
  Abort.

  (** Note that a tactic defined inside a section can only be used in that section, in general. *)

  (* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub := 
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0 | solve_tgt_ub]
        ]).

  Goal refines (Imp_Program_Mem src0) (Imp_Program_Mem tgt0).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src0, tgt0, Imp_init. ss.
    step_tgt_silent.
    step_tgt_silent.
    inv H6. inv H4. inv H5. ss.
    (* We can take multiple steps like this: *)
    do 3 step_tgt_silent.
    inv H6. inv H4. inv H5. inv H6. inv H7. inv H1. ss.
    step_tgt_silent.
    (* Now evaluate return commands. 
       When both src and tgt needs to progress, usually taking tgt step first is better;
       we are usually proving 'forall tgt event, exists src event'.
     *)
    step_tgt_silent.
    inv H5. inv H1.
    (* Now take src step. *)
    econs 3.
    { ss. }
    ss. exists (inr LInternal). eexists. split.
    { econs. econs. econs.
      (* Coq detects correct constructors for this case.
         Same as 'eapply Step_normal. eapply E_Ret. eapply E_ANum.'. *)
    }
    ss. split; auto.
    (* There is only one possible constructor for this: 'sim_term'. *)
    econs.
    { simpl. eauto. }
    { simpl. eauto. }
    { auto. }
  Qed.

End DEMO.

Ltac solve_tgt_ub := 
  exfalso;
  match goal with
  | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
  end;
  repeat econs.

(* Makes a tgt step. *)
Ltac step_tgt_silent0 :=
  match goal with
  | [STEP: ceval _ _ _ |- _] => inv STEP
  end;
  ss; split; auto.

(* Combines above two tactics. *)
Ltac step_tgt_silent :=
  try (econs 4;
        [ss
        | ss; intros ev st_tgt1 STEP0; inv STEP0;
          [step_tgt_silent0 | solve_tgt_ub]
      ]).
Ltac step_src_silent := 
  try (econs 3;
      [ss 
      | eexists; eexists; split; 
      [
        repeat econs
        | split; [ss|idtac]
      ]
      ]).
Ltac step_obs :=
  try (econs 2;ss;intros ev st_tgt1 STEP0; inv STEP0; 
  [step_tgt_silent0
  |solve_tgt_ub]).

Ltac inv_eval := 
  repeat progress (match goal with 
  | [MEM: [_, _] ==> _ |- _] => inv MEM
  | [FORALL: Forall2 _ _ _ |- _] => inv FORALL
  | [SOME: _= Some _ |- _] => inv SOME
  end).

Ltac inv_eval_nosome := 
  repeat progress (match goal with 
  | [MEM: [_, _] ==> _ |- _] => inv MEM
  | [FORALL: Forall2 _ _ _ |- _] => inv FORALL
  end).

Ltac term := 
  try (econs 1;simpl;eauto).

Ltac step_obs_eval := 
  try (
    step_obs;inv_eval; eexists; split; 
    [ repeat econs
      | idtac
    ]
  ).

Ltac step_src_silent_whileTrue := 
  try (econs 3;
      [ss 
      | eexists; eexists; split; 
      [
        econs;econs 7;[econs|];eauto
        | split; [ss|idtac]
      ]
      ]).
Section EX.
  (* Solves tgt undef case if tgt is not undef. *)
  (** Prove the following refinements. Develop tactics to simplify proofs. *)

  (* Ex1. Interactions with the external world is observable, so should be preserved. *)
  Definition src1 : com :=
    <{ "a" :=@ "print" <[0 : aexp]>; ret "a" }>.

  Definition tgt1 : com :=
    <{ "x" := 0; "y" :=@ "print" <["x" : aexp]>; ret "y" }>.

  Goal refines (Imp_Program_Mem src1) (Imp_Program_Mem tgt1).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src1, tgt1, Imp_init. ss.
    step_tgt_silent.
    step_tgt_silent.
    inv_eval.
    step_tgt_silent.
    step_tgt_silent.
    step_src_silent.
    step_obs_eval.
    step_tgt_silent.
    step_src_silent.
    step_tgt_silent.
    inv_eval. 
    step_src_silent.
    term.
    Unshelve.
    econs.
  Qed.


  (* Ex2. If semantics is given by Imp_STS_Mem, memory accesses are also observable. *)
  Definition src2 : com :=
    <{ &<1> := 5; "a" := &<1>; ret "a" }>.

  Definition tgt2 : com :=
    <{ "x" := 2; &<1> := ("x" + 3); "y" := &<1>; ret "y" }>.

  Goal refines (Imp_Program_Mem src2) (Imp_Program_Mem tgt2).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src2, tgt2, Imp_init. ss.
    step_tgt_silent.
    step_src_silent.
    step_tgt_silent.
    inv_eval.
    step_tgt_silent. 
    step_tgt_silent.
    step_obs_eval.
    ss. step_tgt_silent. step_src_silent.
    step_tgt_silent. step_src_silent.
    step_obs_eval.
    step_tgt_silent. step_src_silent.
    step_tgt_silent. inv_eval. 
    step_src_silent. 
    term.
  Qed.

  (* But, if we want to reason about compiler optimizations, for example, we do not want to keep memory accesses.
     Imp_STS_Ext is the right semantics for this. 
   *)
  Definition src2' : com :=
    <{ ret 5 }>.

  Goal refines (Imp_Program_Ext src2') (Imp_Program_Ext tgt2).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Mem, src2', tgt2, Imp_init. ss.
    do 5 step_tgt_silent. inv_eval.
    step_tgt_silent.  
    step_tgt_silent.  
    step_tgt_silent.  
    inv_eval.
    do 2 step_tgt_silent. 
    inv_eval. 
    step_src_silent.
    term.
  Qed.


  (* Ex3. If the source program can exhibit UB, refinement always holds. *)
  Definition src3 : com :=
    <{ ret "a" }>.

  Goal forall tgt, refines (Imp_Program_Mem src3) (Imp_Program_Mem tgt).
  Proof.
    intros. 
    apply adequacy. unfold simulation, Imp_Program_Mem, Imp_STS_Mem, src3, Imp_init. ss.
    econs 3;ss.
    eexists. eexists. split.
    {
      econs 2. ii. inv H. inv_eval.
    }
    split;ss.
    econs 5. ss.
  Qed.

  (* Ex4. If a loop always terminates, we can prove it by induction. *)
  Definition src4 : com :=
    <{ ret 0 }>.

  Definition tgt4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (Imp_Program_Mem src4) (Imp_Program_Mem tgt4).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Mem, src4, tgt4, Imp_init. ss.
    step_tgt_silent.
    step_tgt_silent.
    inv_eval.
    step_tgt_silent. 
    step_tgt_silent.
    assert (
      forall (n : nat) (r : Reg.t) 
      (VAL: (r "x") = Some n ),
      (@sim  _ ekind_memory _ step Imp_sort
      (Imp_init <{ ret 0 }>)
      (Mem.init,
       Normal r <{ while "x" do "x" := "x" - 1 end }>
     (Kseq <{ ret "x" }> Kstop)))
    ).
    {
      induction n. 
      {
        intros. step_tgt_silent;eauto.
        {
          inv_eval_nosome. ss.
          clear H1. 
          step_tgt_silent. step_tgt_silent;inv_eval_nosome;eauto.
          rewrite VAL in H1. inv H1. step_src_silent. term.
        }
        {
          inv H6. rewrite VAL in H1. inv H1. exfalso. eauto. 
        }
      }
      {
        ii. step_tgt_silent;eauto;inv_eval_nosome.
        {
          rewrite H1 in VAL. inv VAL.
        }
        {
          step_tgt_silent;inv_eval_nosome;eauto.
          ss. step_tgt_silent. eapply IHn.
          unfold Reg.write. simpl.  
          f_equal. rewrite VAL in H2. inv H2. lia.
        }
        {
          exfalso. eapply UNDEF. 
          apply E_WhileTrue with (n := (S n));eauto.
          econs. eauto.
        }
      }
    }
    eapply H. 
    ss.
  Qed.
End EX.

Section DIV.
  (** Simulation in current form can't prove refinement between possibly diverging programs. *)

  (* DIV1. We can prove the following refinement, which always terminates. *)
  Definition src5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Definition tgt5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (Imp_Program_Ext src5) (Imp_Program_Ext tgt5).
  Proof.
    apply adequacy. unfold simulation, Imp_Program_Ext, Imp_STS_Mem, src5, tgt5, Imp_init. ss.
    do 4 step_src_silent.
    do 4 step_tgt_silent.
    inv_eval. 
    assert (
      forall (n : nat) (r : Reg.t) 
      (VAL: (r "x") = Some n ),
      @sim  _ ekind_external _ step Imp_sort
      (Mem.init,
   Normal r
     <{
     while "x"
     do "a" :=@ "print" < [AId "x"] >;
        "x" := "x" - 1 end }>
     (Kseq <{ ret "x" }> Kstop))
      (Mem.init,
   Normal r
     <{
     while "x"
     do "a" :=@ "print" < [AId "x"] >;
        "x" := "x" - 1 end }>
     (Kseq <{ ret "x" }> Kstop))
    ).
    {
      induction n; ii; ss. 
      {
        step_tgt_silent;inv_eval_nosome;ss; eauto. 
        2: {
          rewrite VAL in H1. inv H1. contradiction.
        }
        clear H1. 
        step_tgt_silent. step_tgt_silent;inv_eval_nosome;eauto. 
        rewrite VAL in H1. inv H1.
        step_src_silent;eauto. step_src_silent. 
        step_src_silent;eauto. term. 
      }
      {
        step_tgt_silent;inv_eval_nosome;ss; eauto.
        {
          rewrite VAL in H1. inv H1.
        }
        2: {
          exfalso. eapply UNDEF.
          apply E_WhileTrue with (n := (S n));eauto.
          econs. eauto.
        }
        step_tgt_silent.
        rewrite VAL in H1. inv H1. clear H7.
        step_src_silent_whileTrue.
        step_src_silent.
        step_obs;eauto. eexists. inv_eval_nosome. rewrite VAL in H2. inv H2.
        split.
        {
          repeat econs. eauto.
        }
        step_tgt_silent. step_src_silent. 
        step_tgt_silent. inv_eval_nosome.
        2: {
          exfalso. eapply UNDEF. repeat econs.
          unfold Reg.write. simpl. eauto. 
        }
        step_tgt_silent.
        step_src_silent;eauto.
        step_src_silent. ss. eapply IHn. 
        unfold Reg.write in *. ss. f_equal. 
        rewrite VAL in H1. inv H1. nia.
      }
    }
    eapply H.
    unfold Reg.write. simpl. eauto.
    Unshelve.
    eauto.
    eauto.
  Qed.


  (* DIV2. However, we can't prove the following refinement because it can diverge.
     Also note that even though src5 and tgt5 are the same programs (thus trivially refines each other), 
     our simulation relation is too weak to prove this.
   *)
  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Goal refines (Imp_Program_Ext src6) (Imp_Program_Ext tgt6).
  Proof.
  (* We can't prove this right now. Try to prove using induction, and see where it fails. *)
  (* 안해봤는데 알겠다. 새로운 "x"가 더 작다는 보장이 없다! *)
  Abort.

End DIV.

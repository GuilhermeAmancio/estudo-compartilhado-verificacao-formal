(* Somador de 2 bits com carry-in / carry-out.
   Arquivo: src/Ex/IC/Adder2.v

   Estrutura copiada de Ex/RvCore/Mem.v (ICacheA) e Ex/RvCore/MemSpec.v.
   A parte estrutural (modulo + mtrs) ja compilou na versao de 8 bits.
   A prova final (Adder2Spec.adder2_trs_spec) foi escrita a partir do goal
   real que voce me mandou, mas AINDA NAO FOI COMPILADA. *)

From Coq Require Import Lia.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import coqutil.Z.BitOps.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Local Open Scope Z_scope.

Module Adder2.

  (* ---------- 1. Identificadores ---------- *)
  Inductive vid :=
  | adder2
  | in_a | in_b | in_cin
  | out_sum | out_cout
  | tmp_total.

(* Não entendemos -- Pesquisar *)
  Definition vid_eq_dec' : forall (v1 v2: vid), {v1 = v2} + {v1 <> v2} :=
    ltac:(decide equality).

  #[global] Instance vid_vid_t_c: vid_t_c := {| vid_t := vid |}.
  #[global] Instance vid_vid_ops: vid_ops := {| vid_eq_dec := vid_eq_dec' |}.

  Module Notations.
    Notation "'adder2'" := adder2 (in custom ce_top).

    Notation "'in_a'" := in_a (in custom ce_expr).
    Notation "'in_b'" := in_b (in custom ce_expr).
    Notation "'in_cin'" := in_cin (in custom ce_expr).
    Notation "'out_sum'" := out_sum (in custom ce_expr).
    Notation "'out_cout'" := out_cout (in custom ce_expr).
    Notation "'tmp_total'" := tmp_total (in custom ce_expr).

    Notation "'.in_a'" := in_a (in custom ce_portconnid).
    Notation "'.in_b'" := in_b (in custom ce_portconnid).
    Notation "'.in_cin'" := in_cin (in custom ce_portconnid).
    Notation "'.out_sum'" := out_sum (in custom ce_portconnid).
    Notation "'.out_cout'" := out_cout (in custom ce_portconnid).
  End Notations.

  Definition VExprIdvid := @VExprId vid.
  Coercion VExprIdvid: vid >-> VExpr.
  Definition VPortIdsOnevid := @VPortIdsOne vid.
  Coercion VPortIdsOnevid: vid >-> VPortIds.

  (* ---------- 2. O modulo Verilog ----------
     tmp_total tem 3 bits para guardar o carry. *)
  Module M.
    Import Notations.

    Definition m: @VModuleDecl vid_t := #[
module adder2
   (input  logic [1:0] in_a,
    input  logic [1:0] in_b,
    input  logic       in_cin,
    output logic [1:0] out_sum,
    output logic       out_cout);

   logic [2:0] tmp_total;

   assign tmp_total = (3 '(in_a)) + (3 '(in_b)) + (3 '(in_cin));
   assign out_sum   = tmp_total[1:0];
   assign out_cout  = tmp_total[2:2];

endmodule].

  End M.

  (* ---------- 3. Entradas, registradores, saidas ---------- *)
  (* Pesquisar mais sobre Record *)
  Record Inputs :=
    { a_v: SZ;
      b_v: SZ;
      cin_v: SZ }.

  (* Modulo puramente combinacional: nao ha registradores. *)
  Inductive Flops : Set := NoFlops.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun state =>
          a_v <- sfind in_a state <~ [];
          b_v <- sfind in_b state <~ [];
          cin_v <- sfind in_cin state <~ [];
            Sret {|
              a_v := hbits a_v;
              b_v := hbits b_v;
              cin_v := hbits cin_v;
            |};
      to_state := fun i =>
        match i with {|
          a_v := a_v;
          b_v := b_v;
          cin_v := cin_v;
          |} =>
            HMapStr [(in_a, HMapBits a_v);
                     (in_b, HMapBits b_v);
                     (in_cin, HMapBits cin_v)]
        end;
    }.

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state := fun state => Sret NoFlops;
      to_state := fun _ => HMapStr [];
    }.

    Record Outputs := {
      sum_v: SZ;
      cout_v: SZ;
    }.

    Definition output_to_state (outputs: Outputs): State
      := HMapStr [(out_sum, HMapBits outputs.(sum_v));
                  (out_cout, HMapBits outputs.(cout_v))].

    Record Updates := {
      flop_update: State;
    }.

    Definition update_to_state (upds: Updates): State := upds.(flop_update).

    Definition etrs (eid: vid_t): trsOk MTrs := Fail TrsUndeclared.

    Definition trs_structured_sigT: {trs: forall (inputs: Inputs) (flops: Flops), (Updates * Outputs) |
      is_module_trs M.m fmapEmpty etrs Inputs Flops (to_unstructured_trs update_to_state output_to_state trs)
    }.
    Proof.
      unshelve epose (trs := _ : Inputs -> Flops -> Updates * Outputs).
      { intros i f. destruct i, f. split; econstructor; eapply _. }
      exists trs.
      red. unfold to_unstructured_trs. intros ???? Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: auto.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 1%nat). vm_compute. reflexivity. }
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
      all: vm_compute; reflexivity.
    Defined.

    Definition trs_structured := proj1_sig trs_structured_sigT.

    Definition mtrs: MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      eapply mk_MTrsOf with (mtrsof_mtrs := (Build_MTrs _ _ (to_unstructured_trs _ _ trs_structured))).
      1-2: vm_compute; reflexivity. unfold mtrs_func.
      eapply (proj2_sig trs_structured_sigT).
    Defined.

  End AbsOps.

End Adder2.


(* ---------- 4. Especificacao ---------- *)
Module Adder2Spec.
  Import Adder2.
  Import ListNotations.

  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  (* Resolve condicoes do tipo 0 <= x < 2^k. O primeiro "lia" cobre o caso
     em que ele entende 2^k; os outros reduzem a potencia antes. *)
  Ltac solve_range := first [lia | (cbn; lia) | (vm_compute; lia)].

  (* --- Lemas pequenos sobre SZ --- *)

  (* Um literal sem sinal, cujo valor cabe na largura, ja esta normalizado. *)
  Lemma szNorm_unsigned (z w: Z) :
    0 <= z < 2 ^ w -> szNorm #{z, w, false} = z.
  Proof.
    intros H. unfold szNorm, szNormZ. cbn.
    apply Z.mod_small. exact H.
  Qed.

  Lemma szNormZ_small (z w: Z) :
    0 <= z < 2 ^ w -> szNormZ #{z, w, false} = z.
  Proof.
    intros H. unfold szNormZ. cbn.
    apply Z.mod_small. exact H.
  Qed.

  (* --- Aritmetica de fatias de bits ---
     As fatias que o Verilog extrai de tmp_total (3 bits):
       tmp_total[1:0] = T mod 4      tmp_total[2:2] = T / 4
     quando T = a + b + cin cabe em 3 bits (T <= 7). *)
  Lemma adder2_arith (za zb zc: Z) :
    0 <= za < 4 -> 0 <= zb < 4 -> (zc = 0 \/ zc = 1) ->
    bitSlice (za + zb + zc) 0 (1 + 1) = (za + zb + zc) mod 4 /\
    bitSlice (za + zb + zc) 2 (2 + 1) = (za + zb + zc) / 4.
  Proof.
    intros Ha Hb Hc.
    assert (Hc' : 0 <= zc <= 1) by (destruct Hc; lia).
    split.
    - rewrite bitSlice_alt by lia. unfold bitSlice'.
      replace (2 ^ 0) with 1 by reflexivity.
      replace (2 ^ (1 + 1 - 0)) with 4 by reflexivity.
      rewrite Z.div_1_r. reflexivity.
    - rewrite bitSlice_alt by lia. unfold bitSlice'.
      replace (2 ^ 2) with 4 by reflexivity.
      replace (2 ^ (2 + 1 - 2)) with 2 by reflexivity.
      apply Z.mod_small.
      split.
      + apply Z.div_pos; lia.
      + apply Z.div_lt_upper_bound; lia.
  Qed.

  (* O valor de 3 bits que o modulo calcula para tmp_total (exatamente o
     termo que apareceu no goal) e a soma aritmetica a + b + cin. *)
  Lemma adder2_total (za zb zc: Z) :
    0 <= za < 4 -> 0 <= zb < 4 -> 0 <= zc <= 1 ->
    szNorm #{szBin Z.add
               #{szBin Z.add #{szNormZ #{za,2,false},3,false}
                              #{szNormZ #{zb,2,false},3,false},3,false}
               #{szNormZ #{zc,1,false},3,false},3,false} = za + zb + zc.
  Proof.
    intros Ha Hb Hc.
    rewrite (szNormZ_small za 2) by solve_range.
    rewrite (szNormZ_small zb 2) by solve_range.
    rewrite (szNormZ_small zc 1) by solve_range.
    unfold szBin.
    rewrite (szNorm_unsigned za 3) by solve_range.
    rewrite (szNorm_unsigned zb 3) by solve_range.
    rewrite (szNorm_unsigned zc 3) by solve_range.
    rewrite (szNorm_unsigned (za + zb) 3) by solve_range.
    apply (szNorm_unsigned (za + zb + zc) 3).
    solve_range.
  Qed.

  (* --- Enunciado principal ---
     Para quaisquer a, b de 2 bits e cin de 1 bit, o modulo devolve
     sum = (a + b + cin) mod 4  e  cout = (a + b + cin) / 4. *)
  Lemma adder2_trs_spec (za zb zc: Z) :
    0 <= za < 4 -> 0 <= zb < 4 -> (zc = 0 \/ zc = 1) ->
    exists upd sum_sz cout_sz,
      trs_structured
        {| a_v := #{za, 2, false};
           b_v := #{zb, 2, false};
           cin_v := #{zc, 1, false} |} NoFlops
      = (upd, {| sum_v := sum_sz; cout_v := cout_sz |}) /\
      szNorm sum_sz = (za + zb + zc) mod 4 /\
      szNorm cout_sz = (za + zb + zc) / 4.
  Proof.
    intros Ha Hb Hc.
    assert (Hc' : 0 <= zc <= 1) by (destruct Hc; lia).
    eexists _, _, _.
    split.
    { cbn. reflexivity. }
    split.
    - (* soma: tmp_total[1:0] *)
      unfold szRange.
      rewrite (adder2_total za zb zc Ha Hb Hc').
      rewrite (proj1 (adder2_arith za zb zc Ha Hb Hc)).
      apply szNorm_unsigned.
      pose proof (Z.mod_pos_bound (za + zb + zc) 4 ltac:(lia)) as [Hm1 Hm2].
      split; [exact Hm1 |].
      replace (2 ^ (1 - 0 + 1)) with 4 by reflexivity.
      exact Hm2.
    - (* carry: tmp_total[2:2] *)
      unfold szRange.
      rewrite (adder2_total za zb zc Ha Hb Hc').
      rewrite (proj2 (adder2_arith za zb zc Ha Hb Hc)).
      apply szNorm_unsigned.
      split.
      + apply Z.div_pos; lia.
      + replace (2 ^ (2 - 2 + 1)) with 2 by reflexivity.
        apply Z.div_lt_upper_bound; lia.
  Qed.

End Adder2Spec.
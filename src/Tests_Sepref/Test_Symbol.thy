theory Test_Symbol
imports 
  Main
  First_Order_Terms.Term
  Refine_Imperative_HOL.Sepref
begin
datatype 'f symbol =
	Star 
| F 'f nat
for
  map: map
  rel: symbol_all2
  pred: symbol_all

fun to_symbol :: "('f, 'v) term \<Rightarrow>'f symbol" where
  "to_symbol (Var x) = Star "
| "to_symbol (Fun f ts) = F f (length ts)"

fun symbol_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a symbol \<Rightarrow> 'c symbol \<Rightarrow> assn" where 
"symbol_assn P Star Star = emp"|
"symbol_assn P (F fa na) (F fc nc) = P fa fc * \<up>(na = nc)"|
"symbol_assn _ _ _ = false"

lemma hn_Star[sepref_fr_rules]: 
  "hn_refine emp (return Star) emp (symbol_assn P) (RETURN$Star)"
  unfolding hn_refine_def
  by sep_auto

(*
lemma hn_Cons[sepref_fr_rules]: 
  "hn_refine 
  (hn_ctxt P x x' * hn_ctxt (list_assn P) xs xs') 
  (return (x'#xs')) 
  (hn_invalid P x x' * hn_invalid (list_assn P) xs xs') (list_assn P)
  (RETURN$((#) $x$xs))"
  unfolding hn_refine_def
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply solve_entails
  done
*)
find_theorems list_assn
lemma hn_F[sepref_fr_rules]: 
  "hn_refine 
   (hn_ctxt (symbol_assn P) f f' * hn_ctxt (nat_assn) n n')
   (return f')
   (hn_invalid (symbol_assn P) f f' * hn_invalid (nat_assn) n n')
   (symbol_assn P)
   (RETURN$f)"
  unfolding hn_refine_def 
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "nat_assn"]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "symbol_assn P"]], frame_inference)
  apply solve_entails
    done
  oops
  

definition "symbol_assn_id (s :: 'f symbol) \<equiv> RETURN s"

definition symbol_rel where symbol_rel_def_internal:
  "symbol_rel R \<equiv> {(l,l'). symbol_all2 (\<lambda>x x'. (x,x')\<in>R) l l'}"

lemma symbol_assn_pure_conv[constraint_simps]: "symbol_assn (pure R) = pure (\<langle>R\<rangle>symbol_rel)"
proof (intro ext)
  fix l li
  show "symbol_assn (pure R) l li = pure (\<langle>R\<rangle>symbol_rel) l li"
    apply (induction "pure R" l li rule: symbol_assn.induct; simp_all add : pure_def symbol_rel_def_internal symbol_all2_def)
    subgoal
      sorry
    subgoal
      sorry
    subgoal
      sorry
    subgoal
      sorry
    done
qed

lemma symbol_assn_pure[constraint_rules]: 
  assumes P: "is_pure P" 
  shows "is_pure (symbol_assn P)"
proof -
  from P obtain P' where P_eq: "\<And>x x'. P x x' = \<up>(P' x x')" 
    by (rule is_pureE) blast
  {
    fix s s'
    have "symbol_assn P s s' = \<up>(symbol_all2 P' s s')"(*Trouve un équivalent à list_all2*)
      by (induct P\<equiv>P s s' rule: symbol_assn.induct)
         (simp_all add: P_eq)
  } thus ?thesis by rule 
qed
  oops

find_theorems list_assn

sepref_definition symbol_id is "symbol_assn_id" ::
"(symbol_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a (symbol_assn id_assn)"
  unfolding symbol_assn_id_def
  apply sepref_dbg_keep
  done
end
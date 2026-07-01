theory Test_Tree
imports
  Main
  Refine_Imperative_HOL.Sepref
begin

datatype node =
  NodeC nat  "node ref option"  "node ref option"

sepref_register NodeC

datatype 'a tree =
    Leaf
    | Node (val: "'a") (left: "'a tree") (right: "'a tree")
for
  map: map
  rel: tree_all2
  pred: tree_all
sepref_register Leaf
sepref_register Node

fun tree_id :: "'a tree \<Rightarrow> 'a tree nres" where
"tree_id t = RETURN t"

definition "tree_idd (t:: 'a tree) \<equiv> RETURN t"

definition tree_is_Leaf :: "'a tree \<Rightarrow> bool nres" where
"tree_is_Leaf t \<equiv> case t of Leaf \<Rightarrow> RETURN True | (Node x l r) \<Rightarrow> RETURN False"


fun tree_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a tree \<Rightarrow> 'c tree \<Rightarrow> assn" where 
"tree_assn P Leaf Leaf = emp"|
"tree_assn P (Node va la ra) (Node vc lc rc) = P va vc * tree_assn P la lc * tree_assn P ra rc" |
"tree_assn _ _ _ = false"

definition tree_rel where tree_rel_def_internal:
  "tree_rel R \<equiv> {(t,t'). tree_all2 (\<lambda>x x'. (x,x')\<in>R) t t'}"

lemma tree_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>tree_rel \<equiv> {(t,t'). tree_all2 (\<lambda>x x'. (x,x')\<in>R) t t'}"
  by (simp add: tree_rel_def_internal relAPP_def)

lemma tree_assn_aux_simp[simp]:
  "tree_assn P Leaf t' = (\<up>(t'=Leaf))"
  "tree_assn P t Leaf = (\<up>(t=Leaf))"
  unfolding hn_ctxt_def
  apply (cases t')
  apply simp
  apply simp
  apply (cases t)
  apply simp
  apply simp
  done    

lemma tree_assn_simps[simp]:
  "hn_ctxt (tree_assn P) Leaf t' = (\<up>(t'=Leaf))"
  "hn_ctxt (tree_assn P) t Leaf = (\<up>(t=Leaf))"
  "hn_ctxt (tree_assn P) Leaf Leaf = emp"
  "hn_ctxt (tree_assn P) (Node va la ra) (Node vc lc rc) = hn_ctxt P va vc * hn_ctxt (tree_assn P) la lc * hn_ctxt (tree_assn P) ra rc"
  "hn_ctxt (tree_assn P) (Node va la ra) Leaf = false"
  "hn_ctxt (tree_assn P) Leaf (Node vc lc rc) = false"
  unfolding hn_ctxt_def
  apply (cases t')
  apply simp
  apply simp
  apply (cases t)
  apply simp
  apply simp
  apply simp_all
  done

lemma tree_assn_pure_conv[constraint_simps]: "tree_assn (pure R) = pure (\<langle>R\<rangle>tree_rel)"
proof (intro ext)
  fix t ti
  show "tree_assn (pure R) t ti = pure (\<langle>R\<rangle>tree_rel) t ti"
    apply (induction "pure R" t ti rule: tree_assn.induct)
    by (simp_all add: pure_def tree_rel_def)
qed
lemma tree_match_cong[sepref_frame_match_rules]: 
  "\<lbrakk>\<And>x x'. \<lbrakk>x\<in>set t; x'\<in>set t'\<rbrakk> \<Longrightarrow> hn_ctxt A x x' \<Longrightarrow>\<^sub>t hn_ctxt A' x x' \<rbrakk> \<Longrightarrow> hn_ctxt (tree_assn A) t t' \<Longrightarrow>\<^sub>t hn_ctxt (tree_assn A') t t'"
  unfolding hn_ctxt_def
  by (induct A t t' rule: tree_assn.induct) (simp_all add: entt_star_mono)

lemmas hn_ctxt_tree = hn_ctxt_eq[of "tree_assn A" for A]

lemma hn_case_tree[sepref_prep_comb_rule, sepref_comb_rules, simp]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (tree_assn P) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (tree_assn P) p p' * F"
  assumes Rn: "p=Leaf \<Longrightarrow> hn_refine (hn_ctxt (tree_assn P) p p' * F) f1' (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
  assumes Rs: "\<And>va la ra vc lc rc. \<lbrakk> p=(Node va la ra); p'=(Node vc lc rc) \<rbrakk> \<Longrightarrow> 
    hn_refine 
      (hn_ctxt P va vc * hn_ctxt (tree_assn P) la lc * hn_ctxt (tree_assn P) ra rc * INVE * F) 
      (f2' vc lc rc)
      (hn_ctxt P1' va vc * hn_ctxt (tree_assn P2a') la lc * hn_ctxt (tree_assn P2b') ra rc * hn_ctxt XX2 p p' * \<Gamma>2')
      R 
      (f2 va la ra)"
  assumes MERGE_VAL: "\<And>x x'. hn_ctxt P1' x x' \<or>\<^sub>A hn_ctxt P2a' x x' \<or>\<^sub>A hn_ctxt P2b' x x' \<Longrightarrow>\<^sub>t hn_ctxt P' x x'"
  assumes MERGE_LEFT: "\<And>x x'. hn_ctxt (tree_assn P2a') x x' \<Longrightarrow>\<^sub>t hn_ctxt (tree_assn P') x x'"
  assumes MERGE_RIGHT: "\<And>x x'. hn_ctxt (tree_assn P2b') x x' \<Longrightarrow>\<^sub>t hn_ctxt (tree_assn P') x x'"
  assumes MERGE2: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"  
  shows "hn_refine \<Gamma> (case_tree f1' f2' p') (hn_ctxt (tree_assn P') p p' * \<Gamma>') R (case_tree$f1$(\<lambda>\<^sub>2v l r. f2 v l r)$p)"
  apply (rule hn_refine_cons_pre[OF FR])
  apply extract_hnr_invalids
  apply (cases p; cases p'; simp add: tree_assn.simps[THEN hn_ctxt_tree])
  subgoal
    apply (rule hn_refine_cons[OF _ Rn _ entt_refl]; assumption?)
    apply (simp add: hn_ctxt_def)
    apply (subst mult.commute, rule entt_fr_drop)
    apply (rule entt_trans[OF _ MERGE2])
    apply (simp add: ent_disjI1' ent_disjI2')
    done
  subgoal for va la ra vc lc rc
    apply (rule hn_refine_cons[OF _ Rs _ entt_refl]; assumption?)
    apply (simp add: hn_ctxt_def)
    apply (rule entt_star_mono)
    apply (rule entt_fr_drop)
    apply (rule entt_star_mono)
    apply (rule entt_star_mono)
       apply (rule entt_trans[OF _ MERGE_VAL])
       (*
    apply (rule ent_disjI1')
    apply (rule entt_refl)
    apply (rule entt_star_mono)
    apply (rule entt_trans[OF _ MERGE_LEFT])
    apply (rule entt_refl)
    apply (rule entt_trans[OF _ MERGE_RIGHT])
    apply (rule entt_refl)
    apply (rule entt_trans[OF _ MERGE2])
    apply (rule ent_disjI2')
    apply (rule entt_refl)*)
    sorry
  done



lemma tree_case_hnr[simplified mult.commute mult.assoc]:
  assumes LEAF: "hn_refine (hn_ctxt (tree_assn P) Leaf xi * \<Gamma>) (fl xi) \<Gamma>' R (f Leaf)"
  assumes NODE: "\<And>a l r ai li ri. 
      hn_refine (hn_ctxt P a ai * hn_ctxt (tree_assn P) l li * hn_ctxt (tree_assn P) r ri * \<Gamma>) 
                (fn ai li ri) \<Gamma>' R (f (Node a l r))"
  shows "hn_refine (hn_ctxt (tree_assn P) x xi * \<Gamma>) 
                   (case xi of Leaf \<Rightarrow> fl xi | Node ai li ri \<Rightarrow> fn ai li ri) 
                   \<Gamma>' R (f x)"
  unfolding tree_assn.simps hn_refine_def
  apply(cases xi) 
  subgoal
    apply(simp)
    using LEAF[simplified hn_ctxt_def tree_assn.simps hn_refine_def]
    apply sep_auto
    done
  subgoal
    apply simp
    apply (cases x)
    subgoal
      apply (simp add: hn_ctxt_def)
      done
    subgoal for a l r
      apply (simp)
      using NODE[simplified hn_ctxt_def tree_assn.simps hn_refine_def]
      apply (simp add: hn_ctxt_def)
      done
    done
  done


lemma hn_Leaf[sepref_fr_rules]: 
  "hn_refine emp (return Leaf) emp (tree_assn P) (RETURN$Leaf)"
  unfolding hn_refine_def
  by sep_auto
lemma hn_Cons[sepref_fr_rules]: 
  "hn_refine (hn_ctxt P a ai' * hn_ctxt (tree_assn P) l l' * hn_ctxt (tree_assn P) r r') 
  (return (Node ai' l' r'))
  (hn_invalid P a ai' * hn_invalid (tree_assn P) l l' * hn_invalid (tree_assn P) r r') (tree_assn P)
  (RETURN$((Node) $a$l$r))"
  unfolding hn_refine_def  
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "tree_assn P"]], frame_inference) 
  by (smt (verit) assn_aci(10) assn_times_comm ent_true_drop(1) invalid_assn_def invalidate lambda_one mult.right_neutral
      prec_split1_aux pure_false pure_true star_false_right)
  
  
lemma tree_assn_pure[constraint_rules]: 
  assumes P: "is_pure P" 
  shows "is_pure (tree_assn P)"
proof -
  from P obtain P' where P_eq: "\<And>x x'. P x x' = \<up>(P' x x')" 
    by (rule is_pureE) blast

  {
    fix l l'
    have "tree_assn P l l' = \<up>(tree_all2 P' l l')"
      by (induct P\<equiv>P l l' rule: tree_assn.induct)
         (simp_all add: P_eq)
  } thus ?thesis by rule
qed

find_theorems list_assn




sepref_definition tree_is_Leaf_impl is "tree_is_Leaf" ::
"(tree_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding tree_is_Leaf_def
  apply sepref_dbg_keep
  done

sepref_register tree_id

sepref_definition tree_id_impl is "tree_id" :: 
"(tree_assn id_assn)\<^sup>d \<rightarrow>\<^sub>a (tree_assn id_assn)"
  unfolding tree_id.simps
  apply sepref
  done

end

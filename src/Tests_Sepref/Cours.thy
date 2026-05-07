theory Cours
imports
Main
Refine_Imperative_HOL.Sepref
Refine_Imperative_HOL.IICF
begin

definition min_of_list :: "'a::linorder list \<Rightarrow> 'a nres" where
 "min_of_list l \<equiv> ASSERT (l\<noteq>[]) >> SPEC (\<lambda>x. \<forall>y\<in>set l. x\<le>y) "
  
definition min_of_list1 :: "'a::linorder list \<Rightarrow> 'a nres" where
 "min_of_list1 l \<equiv> ASSERT (l\<noteq>[]) >> RETURN (fold min (tl l) (hd l))"


lemma min_of_list_1_refine : "(min_of_list1, min_of_list) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding min_of_list1_def min_of_list_def
  apply (clarsimp intro!: nres_relI)
  apply (refine_vcg)
  by (auto simp: neq_Nil_conv Min.set_eq_fold[symmetric])

definition min_of_list2 :: "'a::linorder list \<Rightarrow> 'a nres" where 
"min_of_list2 l \<equiv> ASSERT (l\<noteq>[]) \<then> RETURN(
  fold (\<lambda>i. min (l!(i+1)))[0..<length l - 1](l!0)
)"

lemma min_of_list2_refine: "(min_of_list2, min_of_list1)\<in>Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding min_of_list2_def[abs_def] min_of_list1_def[abs_def]
  apply refine_vcg
  apply clarsimp_all
  apply (rewrite in "_=\<hole>" fold_idx_conv)
  by (auto simp: nth_tl hd_conv_nth)

sepref_definition min_of_list3 is "min_of_list2" ::
"(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding min_of_list2_def[abs_def]
  by sepref
thm min_of_list3_def

theorem min_of_list3_correct : "(min_of_list3,min_of_list) \<in> (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  using min_of_list3.refine[FCOMP min_of_list2_refine, FCOMP min_of_list_1_refine] .

lemma "l\<noteq>[] \<Longrightarrow> <array_assn nat_assn l a> min_of_list3 a <\<lambda>x. array_assn nat_assn l a * \<up>(\<forall>y\<in>set l. x\<le>y)>\<^sub>t"
by (sep_auto 
      simp: min_of_list_def pure_def pw_le_iff refine_pw_simps
      heap: min_of_list3_correct[THEN hfrefD, of l a, THEN hn_refineD, simplified])


definition "in_sorted_list1_invar x xs \<equiv> \<lambda>(l,u,found).
    (l\<le>u \<and> u\<le>length xs)
  \<and> (found \<longrightarrow> x\<in>set xs)
  \<and> (\<not>found \<longrightarrow> (x\<notin>set (take l xs) \<and> x\<notin>set (drop u xs))
  )"
definition "in_sorted_list1' x xs \<equiv> do {
  let l=0;
  let u=length xs;
  (_,_,r) \<leftarrow> WHILEIT (in_sorted_list1_invar x xs)
    (\<lambda>(l,u,found). l<u \<and> \<not>found) (\<lambda>(l,u,found). do {
      let i = (l+u) div 2;
      let xi = xs!i; \<comment> \<open>It's not trivial to show that \<open>i\<close> is in range\<close>
      if x=xi then
        RETURN (l,u,True)
      else if x<xi then
        RETURN (l,i,False)
      else  
        RETURN (i+1,u,False)
  
    }) (l,u,False);
  RETURN r  
}"

sepref_thm in_sorted_list2 is "uncurry in_sorted_list1'" ::
"nat_assn\<^sup>k *\<^sub>a (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding in_sorted_list1'_def[abs_def]
  apply sepref_dbg_keep
      supply [[goals_limit=1]]
      apply sepref_dbg_trans_keep
                    apply sepref_dbg_trans_step_keep
                    apply (sepref_dbg_side_keep)
  done
  oops

sepref_thm test_add_2 is "\<lambda>x. RETURN(2+x)" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref
  done

sepref_thm test is "\<lambda>l. ASSERT(length l > 1) \<then> RETURN(l!1+2)" :: 
"(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_dbg_keep
  done


end
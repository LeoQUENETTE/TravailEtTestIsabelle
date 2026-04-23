theory Test_Graph
imports
Main
Refine_Imperative_HOL.Sepref
Refine_Imperative_HOL.Sepref_Graph
begin

definition count_nodes :: "('v rel) \<Rightarrow> 'v \<Rightarrow> (nat) nres" where
  "count_nodes E v0 \<equiv> do {
    (_, count) \<leftarrow> RECT (\<lambda>count (V, v). 
      if v \<in> V then 
        RETURN (V, 0)
      else do {
        let V = insert v V;
        (V', sum_counts) \<leftarrow> 
          FOREACH\<^sub>C (E``{v}) (\<lambda>_. True)
            (\<lambda>v' (V, acc). do {
              (V'', c) \<leftarrow> count (V, v');
              RETURN (V'', acc + c)
            }) (V, 1);
        RETURN (V', sum_counts)
      }
    ) ({}, v0);
    RETURN count
  }"

sepref_definition count_nodes_impl is "uncurry count_nodes" ::
  "(adjg_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  unfolding count_nodes_def[abs_def]
  apply (rewrite in "RECT _ (\<hole>,_)" ias.fold_custom_empty)
  apply sepref_dbg_keep
  done
export_code count_nodes_impl in Haskell

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)



end
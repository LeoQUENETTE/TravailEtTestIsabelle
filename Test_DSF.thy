theory Test_DSF
imports
  Main
  Refine_Imperative_HOL.Sepref
  Refine_Imperative_HOL.Sepref_Graph
begin
context 
  fixes E :: "'v rel" and v0 :: 'v and tgt :: "'v \<Rightarrow> bool"
begin
definition dfs :: "('v set \<times> bool) nres" where
  "dfs \<equiv> do {
    (V,r) \<leftarrow> RECT (\<lambda>dfs (V,v). 
      if v\<in>V then RETURN (V,False)
      else do {
        let V=insert v V;
        if tgt v then
          RETURN (V,True)
        else
          FOREACH\<^sub>C (E``{v}) (\<lambda>(_,b). \<not>b) (\<lambda>v' (V,_). dfs (V,v')) (V,False)
      }
    ) ({},v0);
    RETURN (V,r)
  }"

end
sepref_definition dfs_impl is "uncurry2 dfs" ::
 "(adjg_assn nat_assn)\<^sup>k*\<^sub>anat_assn\<^sup>k*\<^sub>a(pure (nat_rel \<rightarrow> bool_rel))\<^sup>k \<rightarrow>\<^sub>a prod_assn (ias.assn nat_assn) bool_assn"
  unfolding dfs_def[abs_def] 
  using [[goals_limit = 1]]
  apply (rewrite in "RECT _ (\<hole>,_)" ias.fold_custom_empty) \<comment> \<open>Select impls\<close>
  apply (rewrite in "if \<hole> then RETURN (_,True) else _" fold_pho_apply)
  apply sepref \<comment> \<open>Invoke sepref-tool\<close>
  done
export_code dfs_impl in Haskell module_name DFS

end
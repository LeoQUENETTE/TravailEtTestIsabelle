theory Test_BFS
imports
  Main
  Refine_Imperative_HOL.Sepref
  Refine_Imperative_HOL.Sepref_Graph
begin
  definition BFS_level :: "('v rel) \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool nres" where
  "BFS_level E frontier visited t \<equiv> do { RECT(\<lambda>_.
    if t \<in> frontier then
      RETURN True
    else if frontier = {} then
      RETURN False
    else do {
      let next = (\<Union> v \<in> frontier. E `` {v}) - visited - frontier;
      RETURN BFS_level E next (visited \<union> frontier) t
    }
  )(E {v0} {} t)}"

  definition BFS :: "('v rel) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool nres" where
    "BFS E v0 t \<equiv> BFS_level E {v0} {} t"
  
  
  
  sepref_definition BFS_impl is "uncurry2 BFS":: 
    "(adjg_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding BFS_def[abs_def]
    apply sepref_dbg_keep
    apply sepref_dbg_cons_solve
    done
end
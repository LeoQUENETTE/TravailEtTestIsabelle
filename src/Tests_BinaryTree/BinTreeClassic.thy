theory BinTreeClassic
imports 
Main
Complex_Main
begin

datatype 'v bin_tree =
  Leaf (\<open>..\<close>)|
  Node  'v (left  : "'v bin_tree") (right : "'v bin_tree")
for
  map: map
  rel: bt_all2
  pred: bt_all

definition bt_rel where bin_tree_rel_def_internal:
  "bt_rel R \<equiv> {(t,t'). bt_all2 (\<lambda>x x'. (x,x')\<in>R) t t'}"

definition get_val :: "'v bin_tree \<Rightarrow> 'v"  where
"get_val t = (case t of
  Leaf \<Rightarrow> undefined|
  Node v l r \<Rightarrow> v
)"
 

fun nb_node :: "'a bin_tree \<Rightarrow> nat" where
"nb_node (Node _ l r) = 1 + nb_node l + nb_node r"
|"nb_node _ = 0"

fun count_val :: "('v::linorder) bin_tree \<Rightarrow> 'v \<Rightarrow> nat" where
  "count_val Leaf x = 0" |
  "count_val (Node v l r) x = 
     (if v = x then 1 else 0) + count_val l x + count_val r x"

fun get_root_value :: "'v bin_tree \<Rightarrow> 'v option" where
"get_root_value (Leaf) = None"|
"get_root_value (Node v _ _) = Some v"
fun nb_leaf :: "'a bin_tree \<Rightarrow> nat" where
"nb_leaf Leaf = 1"|
"nb_leaf (Node _ l r) = nb_leaf l + nb_leaf r"



fun to_list :: "'a bin_tree \<Rightarrow> 'a list" where
"to_list Leaf = []"
|"to_list (Node v l r) = [v] @ to_list l @ to_list r"

fun to_set where
"to_set Leaf = {}"|
"to_set (Node v l  r) = {v} \<union> to_set l \<union> to_set r"

fun bst_invariant :: "'v::linorder bin_tree \<Rightarrow> bool" where
  "bst_invariant Leaf = False"
| "bst_invariant (Node v l r) =
      ((bst_invariant l \<or> l = Leaf) \<and> (bst_invariant r \<or> r = Leaf)
       \<and> (\<forall>x\<in>to_set l. x < v)
       \<and> (\<forall>x\<in>to_set r. v < x)
)"


fun insert :: "('v::linorder) bin_tree \<Rightarrow> 'v \<Rightarrow> 'v bin_tree" where
"insert Leaf x = Node x Leaf Leaf" |
"insert (Node v l r) x =
   (if x < v then Node v (insert l x) r
    else if v < x then Node v l (insert r x)
    else Node v l r)"


fun insert_lists :: "('v::linorder) bin_tree \<Rightarrow> 'v list \<Rightarrow> 'v bin_tree" where
"insert_lists t [] = t"|
"insert_lists t (x#xs) = insert_lists (insert t x) xs"

definition insert_set :: "('v::linorder) bin_tree \<Rightarrow> 'v set \<Rightarrow> 'v bin_tree" where
"insert_set t s = insert_lists t (SOME l. set l = s)"

definition list_to_tree :: "('v::linorder) list \<Rightarrow> 'v bin_tree" where
"list_to_tree l = insert_lists Leaf l"

definition set_to_tree :: "('v::linorder) set \<Rightarrow> 'v bin_tree" where
"set_to_tree l = insert_set Leaf l"


definition fusion :: "('v::linorder) bin_tree \<Rightarrow> ('v::linorder) bin_tree \<Rightarrow> 'v bin_tree" where
"fusion t t' = set_to_tree ((to_set t) \<union> (to_set t'))"
  
fun is_present :: "'v bin_tree \<Rightarrow> 'v \<Rightarrow> bool" where
"is_present Leaf x = False"|
"is_present (Node v l r) x = (if v = x then True else (is_present l x \<or> is_present r x))"

fun bst_is_present :: "('v::linorder) bin_tree \<Rightarrow> 'v \<Rightarrow> bool" where
"bst_is_present Leaf x = False"|
"bst_is_present (Node v l r) x = (
  if x = v then True 
  else (if x < v then (bst_is_present l x )
    else (bst_is_present r x)
    )
  )"


fun search_node :: "('v::linorder) bin_tree \<Rightarrow> 'v  \<Rightarrow>'v bin_tree" where
"search_node Leaf x = Leaf"|
"search_node (Node v l r) x = 
  (if x = v then (Node v l r) else (if x < v then search_node l x else search_node r x))"

fun search_max :: "'v bin_tree \<Rightarrow> 'v" where
"search_max Leaf = undefined"|
"search_max (Node v l Leaf) = v"|
"search_max (Node v l r) = search_max r"

fun search_min :: "'v bin_tree \<Rightarrow> 'v" where
"search_min Leaf = undefined" |
"search_min (Node v Leaf r) = v"|
"search_min (Node v l r) = search_min l"

fun delete :: "('v::linorder) bin_tree \<Rightarrow> 'v \<Rightarrow> 'v bin_tree" where
"delete Leaf x = Leaf"|
"delete (Node v Leaf r) x = r"|
"delete (Node v l Leaf) x = l"|
"delete (Node v l r) x = (
  if v = x then (
    let lv = search_max l in
    (Node lv (delete l lv) r)
  )
  else if v > x then (Node v (delete l x) r)
  else (Node v l (delete r x))
)"


end
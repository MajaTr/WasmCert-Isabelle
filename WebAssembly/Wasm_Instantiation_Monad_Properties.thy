theory Wasm_Instantiation_Monad_Properties 
  imports "../libs/Misc_Generic_Lemmas" "../libs/List_Assn" 
    Wasm_Instantiation_Monad Wasm_Monad_Assertions Wasm_Instantiation_Properties begin

abbreviation "fits_at_in l n la \<equiv> case l of [] \<Rightarrow> True | x#xs \<Rightarrow> n+length l \<le> length la"

abbreviation "insert_at_in l n la \<equiv> take n la @ l @ drop (n+length l) la"

lemma list_blit_array_triple:
  "<a \<mapsto>\<^sub>a la> 
  list_blit_array l a n
  <\<lambda>r. \<up>(fits_at_in l n la) 
    * a \<mapsto>\<^sub>a insert_at_in l n la>"
proof(induct l arbitrary:a la n)
case Nil
  then show ?case by sep_auto
next
  case (Cons a l)
  show ?case 
    supply [simp del] = list_blit_array.simps
    apply(subst list_blit_array.simps)
    apply(sep_auto heap:Cons split:list.splits simp: take_update_last)
    done
qed

(*todo: better name *)
(*abbreviation "list1_assn P xs \<equiv> List.fold (\<lambda>x acc. acc * P x) xs emp" *)
fun list1_assn :: "('a \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> assn" where
  "list1_assn P [] = emp"
| "list1_assn P (a#as) = P a * list1_assn P as"


lemma fold_map_triple':
  assumes "\<And> i. i < length xs \<Longrightarrow> <P (xs!i)> f (xs!i) <\<lambda>r. Q (xs!i) r>"
  shows "<list1_assn P xs> 
  Heap_Monad.fold_map f xs 
  <\<lambda>r. list_assn Q xs r>"
  using assms 
proof(induct xs)
  case Nil
  then show ?case by sep_auto
next
  case (Cons a xs)

  have 1:"<P a> f a <\<lambda>r. Q a r>" using Cons(2)[of 0] by simp
  have 2:"\<And> i. i < length xs \<Longrightarrow> <P (xs!i)> f (xs!i) <\<lambda>r. Q (xs!i) r>" 
    using Cons(2) 
    by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  show ?case 
    by (sep_auto heap:1 Cons(1)[OF 2])
qed

lemma fold_map_triple:
  assumes "\<And> x. <F> f x <\<lambda>r. Q x r * F>"
  shows "<F> 
  Heap_Monad.fold_map f xs 
  <\<lambda>r. list_assn Q xs r * F>"
  using assms 
proof(induct xs)
  case Nil
  then show ?case by sep_auto
next
  case (Cons a xs)
  show ?case 
    by (sep_auto heap:Cons(2) Cons(1)[OF Cons(2)])
qed


lemma array_blit_map_triple':
  assumes  "\<And> i. i < length xs \<Longrightarrow> <P (xs!i)> f (xs!i) <\<lambda>r. Q (xs!i) r>"
  shows 
    "<a \<mapsto>\<^sub>a la * list1_assn P xs> 
    array_blit_map xs f a n
    <\<lambda>r. \<exists>\<^sub>Ays. \<up>(fits_at_in xs n la)
  *  a \<mapsto>\<^sub>a insert_at_in ys n la 
  * list_assn Q xs ys>"
proof -
  {
    fix ys
    have "<a \<mapsto>\<^sub>a la * list_assn Q xs ys> 
    list_blit_array ys a n
    <\<lambda>r.\<up>(fits_at_in xs n la)
  *  a \<mapsto>\<^sub>a insert_at_in ys n la 
  * list_assn Q xs ys>"
      supply [simp del] = list_blit_array.simps
      apply(extract_pre_pure)
      apply(sep_auto heap: list_blit_array_triple split:list.splits)
      done
  }
  note 1 = this

  show ?thesis 
    supply [simp del] = list_blit_array.simps
    apply(sep_auto heap:fold_map_triple'[where P=P and Q=Q, OF assms] )
    apply(sep_auto heap:1)
    done 
qed 

lemma array_blit_map_triple:
  assumes  "\<And> x. <F> f x <\<lambda>r. Q x r * F>"
  shows 
    "<a \<mapsto>\<^sub>a la * F> 
    array_blit_map xs f a n
    <\<lambda>r. \<exists>\<^sub>Ays. \<up>(fits_at_in xs n la)
  *  a \<mapsto>\<^sub>a insert_at_in ys n la
  * list_assn Q xs ys * F>"
proof -
  {
    fix ys
    have "<a \<mapsto>\<^sub>a la * list_assn Q xs ys * F> 
    list_blit_array ys a n
    <\<lambda>r.\<up>(fits_at_in xs n la)
  *  a \<mapsto>\<^sub>a insert_at_in ys n la 
  * list_assn Q xs ys * F>"
      supply [simp del] = list_blit_array.simps
      apply(extract_pre_pure)
      apply(sep_auto heap: list_blit_array_triple split:list.splits)
      done
  }
  note 1 = this

  show ?thesis 
    supply [simp del] = list_blit_array.simps
    apply(sep_auto heap:fold_map_triple[OF assms] 1) 
    done 
qed 

lemma array_blit_map_triple_emp:
  assumes  "\<And> x. <emp> f x <\<lambda>r. Q x r>"
  shows 
    "<a \<mapsto>\<^sub>a la> 
    array_blit_map xs f a n
    <\<lambda>r. \<exists>\<^sub>Ays. \<up>(fits_at_in xs n la)
  *  a \<mapsto>\<^sub>a insert_at_in ys n la
  * list_assn Q xs ys>"
  using array_blit_map_triple[of emp f Q a la xs n]
  by(simp del:array_blit_map.simps add:assms) 

abbreviation "module_func_to_cl inst inst_types \<equiv> 
  (\<lambda>(i_t, loc_ts, b_es). cl.Func_native inst (inst_types!i_t) loc_ts b_es)"


abbreviation "alloc_funcs_simple' m_fs inst inst_types \<equiv> 
  map (\<lambda>m_f. module_func_to_cl inst inst_types m_f) m_fs" 

lemma alloc_funcs_simple_conv:
  "alloc_funcs_simple m_fs inst = alloc_funcs_simple' m_fs inst (inst.types inst)" 
  unfolding alloc_func_simple_def by simp

lemma list_assn_map1:"list_assn P (map f xs) ys = list_assn (\<lambda>x y. P (f x) y) xs ys"
  by(induct "(\<lambda>x y. P (f x) y)"  xs ys rule: list_assn.induct, auto)
  
lemma alloc_funcs_m_triple:
  "< s_funcs \<mapsto>\<^sub>a fs * inst_types \<mapsto>\<^sub>a m_tfs> 
  alloc_funcs_m s_funcs n m_fs inst_m inst_types
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_fs n fs)
  *  s_funcs \<mapsto>\<^sub>a insert_at_in ys n fs
  *  list_assn (cl_m_assn ([inst], [inst_m])) (alloc_funcs_simple' m_fs inst m_tfs) ys
  *  inst_types \<mapsto>\<^sub>a m_tfs>"
  unfolding alloc_funcs_m_def cl_m_assn_def
  by(simp only: list_assn_map1, rule array_blit_map_triple, sep_auto)

lemma alloc_tabs_m_triple: 
  "< s_tabs \<mapsto>\<^sub>a ts> 
  alloc_tabs_m s_tabs n m_ts
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_ts n ts)
  *  s_tabs \<mapsto>\<^sub>a insert_at_in ys n ts
  *  list_assn tabinst_m_assn (alloc_tabs_simple m_ts) ys>"
  unfolding alloc_tabs_m_def tabinst_m_assn_def alloc_tab_simple_def
  by(simp only: list_assn_map1, rule array_blit_map_triple_emp, sep_auto)

lemma alloc_mems_m_triple: 
  "< s_mems \<mapsto>\<^sub>a ms> 
  alloc_mems_m s_mems n m_ms
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in m_ms n ms)
  *  s_mems \<mapsto>\<^sub>a insert_at_in ys n ms
  *  list_assn mem_m_assn (alloc_mems_simple m_ms) ys>"
  unfolding alloc_mems_m_def mem_m_assn_def alloc_mem_simple_def
  apply(simp only: list_assn_map1, rule array_blit_map_triple_emp)
  apply(sep_auto simp:mem_mk_def mem_rep_mk_def bytes_replicate_def 
      zero_byte_def mem_rep.Abs_mem_rep_inverse)
  done


lemma list_assn_pure:"list_assn (\<lambda>x y. \<up>(P x y)) xs ys = \<up>(list_all2 P xs ys)"
  by(induct "\<lambda>x y. \<up>(P x y)"  xs ys rule: list_assn.induct, auto)

(* todo: learn how to make this nicer *)
lemma alloc_globs_m_triple': 
  "< s_globs \<mapsto>\<^sub>a gs> 
  alloc_globs_m s_globs n m_gs gvs 
  <\<lambda>r.\<exists>\<^sub>Ays. \<up>(fits_at_in (zip m_gs gvs) n gs)
  *  s_globs \<mapsto>\<^sub>a insert_at_in ys n gs
  *  \<up>((alloc_globs_simple m_gs gvs) = ys)>"
  unfolding alloc_globs_m_def alloc_glob_simple_def
  apply(simp only: list.rel_eq list_assn_pure flip: list.rel_eq list_assn_pure)
  apply(simp only: list_assn_map1)
  apply(rule array_blit_map_triple_emp)
  apply(sep_auto)
  done


lemma alloc_globs_m_triple: 
  "< s_globs \<mapsto>\<^sub>a gs> 
  alloc_globs_m s_globs n m_gs gvs 
  <\<lambda>r. \<up>(fits_at_in (zip m_gs gvs) n gs)
  *  s_globs \<mapsto>\<^sub>a insert_at_in (alloc_globs_simple m_gs gvs) n gs>"
  by(rule cons_post_rule[OF alloc_globs_m_triple'], sep_auto)

abbreviation "get_exports inst m_exps \<equiv> 
  map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) m_exps"

lemma get_exports_m_triple: 
  "<f_m \<mapsto>\<^sub>a f * t_m \<mapsto>\<^sub>a t  * m_m \<mapsto>\<^sub>a m * g_m \<mapsto>\<^sub>a g> 
  get_exports_m \<lparr>inst_m.types = tf_m, funcs = f_m, tabs = t_m, mems = m_m, globs = g_m \<rparr> m_exps 
  <\<lambda>r. \<up>(get_exports \<lparr>inst.types = tf, funcs = f, tabs = t, mems = m, globs = g \<rparr> m_exps = r)
  *  (f_m \<mapsto>\<^sub>a f * t_m \<mapsto>\<^sub>a t * m_m \<mapsto>\<^sub>a m * g_m \<mapsto>\<^sub>a g)>"
  unfolding get_exports_m_def 
  apply(simp only: list.rel_eq list_assn_pure flip: list.rel_eq list_assn_pure)
  apply(simp only: list_assn_map1)
  apply(rule fold_map_triple)
  unfolding export_get_v_ext_m_def export_get_v_ext_def
  by(sep_auto split:v_ext.splits)

lemma alloc_funcs_equiv_full:"alloc_funcs s m_fs i
  = (s\<lparr>s.funcs := s.funcs s @ alloc_funcs_simple m_fs i\<rparr>, 
     [length (s.funcs s)..<length (s.funcs s) + length m_fs])"
  using alloc_funcs_equiv alloc_funcs_range
  by (metis surjective_pairing) 

lemma alloc_tabs_equiv_full:"alloc_tabs s m_ts
  = (s\<lparr>s.tabs := s.tabs s @ alloc_tabs_simple m_ts\<rparr>, 
     [length (s.tabs s)..<length (s.tabs s) + length m_ts])"
  using alloc_tabs_equiv alloc_tabs_range
  by (metis surjective_pairing) 

lemma alloc_mems_equiv_full:"alloc_mems s m_ms
  = (s\<lparr>s.mems := s.mems s @ alloc_mems_simple m_ms\<rparr>, 
     [length (s.mems s)..<length (s.mems s) + length m_ms])"
  using alloc_mems_equiv alloc_mems_range
  by (metis surjective_pairing) 

lemma alloc_globs_equiv_full:"alloc_globs s m_gs gvs
  = (s\<lparr>s.globs := s.globs s @ alloc_globs_simple m_gs gvs\<rparr>, 
     [length (s.globs s)..<length (s.globs s) + min (length m_gs) (length gvs)])"
  using alloc_globs_equiv alloc_globs_range
  by (metis surjective_pairing) 



lemma "< s_m_assn (is, i_ms) s s_m * inst_store_assn (is, i_ms)>
  interp_alloc_module_m s_m m imps gvs
  <\<lambda>(s_m', i_m, exps_m). let (s', i, exps) = interp_alloc_module s m imps gvs in 
  \<up>(exps=exps_m) * inst_store_assn (is@[i], i_ms@[i_m]) * s_m_assn (is@[i], i_ms@[i_m]) s' s_m' >"
  unfolding interp_alloc_module_m_def make_empty_inst_m_def
    s_m_assn_def funcs_m_assn_def tabs_m_assn_def mems_m_assn_def globs_m_assn_def
  supply [simp del] = array_blit_map.simps
  
  apply(sep_auto)
   apply(sep_auto heap:alloc_funcs_m_triple)
  apply(sep_auto)
   apply(sep_auto heap:alloc_tabs_m_triple)
  apply(sep_auto)
   apply(sep_auto heap:alloc_mems_m_triple)
  apply(sep_auto)
   apply(sep_auto heap:alloc_globs_m_triple)
  apply(sep_auto)
   apply(sep_auto heap:get_exports_m_triple)
  apply(sep_auto)

  apply(extract_pre_pure)
  apply(sep_auto simp:interp_alloc_module_def Let_def split:prod.splits) (* takes a while *)
  apply(sep_auto simp:alloc_funcs_equiv_full alloc_funcs_simple_conv 
      alloc_tabs_equiv_full alloc_mems_equiv_full alloc_globs_equiv_full)
  sorry
end

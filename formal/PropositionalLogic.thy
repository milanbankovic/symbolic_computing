theory PropositionalLogic
imports Main
begin

section \<open>Syntax\<close>

datatype prop_form = 
     TOP
   | BOT
   | VAR nat
   | NOT prop_form
   | AND prop_form prop_form (infixl "AND" 104)
   | OR prop_form prop_form (infixl "OR" 103) 
   | IMP prop_form prop_form (infixl "IMP" 102)
   | EQ prop_form prop_form (infixl "EQ" 101)
  
term "(TOP AND BOT) OR TOP"

section \<open>Semantics\<close>

type_synonym valuation = "nat \<Rightarrow> bool"

primrec Iv :: "valuation \<Rightarrow> prop_form \<Rightarrow> bool" where
  "Iv v TOP = True"
| "Iv v BOT = False"
| "Iv v (VAR n) = v n"
| "Iv v (NOT f) = (\<not> (Iv v f))"
| "Iv v (f1 AND f2) = (Iv v f1 \<and> Iv v f2)"
| "Iv v (f1 OR f2) = (Iv v f1 \<or> Iv v f2)"
| "Iv v (f1 IMP f2) = (Iv v f1 \<longrightarrow> Iv v f2)"
| "Iv v (f1 EQ f2) = (Iv v f1 \<longleftrightarrow> Iv v f2)"

lemma
  shows "Iv v (f1 AND f2) \<longleftrightarrow> 
        (if Iv v f1 = True \<and> Iv v f2 = True then True else False)" 
  by auto

lemma
  shows "Iv v (f1 IMP f2) = True \<longleftrightarrow> 
         Iv v f1 = False \<or> Iv v f2 = True"
  by auto

definition satisfies :: "valuation \<Rightarrow> prop_form \<Rightarrow> bool" (infix "|=" 50) where
 "v |= f \<longleftrightarrow> Iv v f = True"

lemma satisfies [simp]:
  "v |= TOP"
  "\<not> (v |= BOT)"
  "v |= VAR n \<longleftrightarrow> v n"
  "v |= NOT f \<longleftrightarrow> \<not> v |= f"
  "v |= f1 AND f2 \<longleftrightarrow> v |= f1 \<and> v |= f2"
  "v |= f1 OR f2 \<longleftrightarrow> v |= f1 \<or> v |= f2"
  "v |= f1 IMP f2 \<longleftrightarrow> v |= f1 \<longrightarrow> v |= f2"
  "v |= f1 EQ f2 \<longleftrightarrow> (v |= f1 \<longleftrightarrow> v |= f2)"
  by (auto simp add: satisfies_def)

primrec vars :: "prop_form \<Rightarrow> nat set"  where
  "vars TOP = {}"
| "vars BOT = {}"
| "vars (VAR n) = {n}"
| "vars (NOT f) = vars f"
| "vars (f1 AND f2) = vars f1 \<union> vars f2"
| "vars (f1 OR f2) = vars f1 \<union> vars f2"
| "vars (f1 IMP f2) = vars f1 \<union> vars f2"
| "vars (f1 EQ f2) = vars f1 \<union> vars f2"

lemma finite_vars: 
  shows "finite (vars f)"
  by (induction f) auto

lemma relevant_vars:
  assumes "\<forall> n \<in> vars f. v1 n = v2 n"
  shows "Iv v1 f = Iv v2 f"
  using assms
  by (induction f) auto

definition tautology :: "prop_form \<Rightarrow> bool" where
  "tautology f \<longleftrightarrow> (\<forall> v. v |= f)"

definition satisfiable :: "prop_form \<Rightarrow> bool" where
  "satisfiable f \<longleftrightarrow> (\<exists> v. v |= f)"

lemma "tautology f \<longleftrightarrow> \<not> satisfiable (NOT f)"
  unfolding tautology_def satisfiable_def
  by auto

lemma 
  assumes "tautology f"
  shows "satisfiable f"
  using assms
  using satisfiable_def tautology_def by auto

lemma
  shows "tautology TOP"
  unfolding tautology_def
  by auto

lemma
  shows "\<not> satisfiable BOT"
  unfolding satisfiable_def
  by auto

definition satisfies_set :: "valuation \<Rightarrow> prop_form set \<Rightarrow> bool" (infix "|=\<^sub>s" 120) where 
  "v |=\<^sub>s \<Gamma> \<longleftrightarrow> (\<forall> f \<in> \<Gamma>. v |= f)"

definition satisfiable_set :: "prop_form set \<Rightarrow> bool" where
  "satisfiable_set \<Gamma> \<longleftrightarrow> (\<exists> v. v |=\<^sub>s \<Gamma>)"

lemma 
  assumes "satisfiable_set \<Gamma>" "tautology f"
  shows "satisfiable_set (\<Gamma> \<union> {f})"
  using assms
  using satisfiable_set_def satisfies_set_def tautology_def by auto

lemma
  assumes "\<not> satisfiable_set \<Gamma>" 
  shows "\<not> satisfiable_set (\<Gamma> \<union> {f})"
  using assms satisfiable_set_def satisfies_set_def by auto

lemma
  assumes "\<not> satisfiable_set \<Gamma>" "tautology f" 
  shows "\<not> satisfiable_set (\<Gamma> - {f})"
  using assms
  unfolding satisfiable_set_def tautology_def satisfies_set_def Ball_def
  by auto

definition equiv :: "prop_form \<Rightarrow> prop_form \<Rightarrow> bool" (infix "\<equiv>\<^sub>e" 120) where
  "f1 \<equiv>\<^sub>e f2 \<longleftrightarrow> (\<forall> v. v |= f1 \<longleftrightarrow> v |= f2)"

lemma
  shows "f1 \<equiv>\<^sub>e f2 \<longleftrightarrow> tautology (f1 EQ f2)"
  by (simp add: equiv_def tautology_def)

lemma
  shows "equiv (NOT (NOT f)) f"
  by (simp add: equiv_def)

definition entails :: "prop_form \<Rightarrow> prop_form \<Rightarrow> bool" (infix "|=\<^sub>e" 120) where
  "f1 |=\<^sub>e f2 \<longleftrightarrow> (\<forall> v. v |= f1 \<longrightarrow> v |= f2)"

lemma
  assumes "f1 |=\<^sub>e f2" "f2 |=\<^sub>e f1"
  shows "f1 \<equiv>\<^sub>e f2"
  using assms
  unfolding entails_def equiv_def
  by auto

lemma
  shows "f1 |=\<^sub>e f2 \<longleftrightarrow> tautology (f1 IMP f2)"
  unfolding entails_def tautology_def satisfies_def
  by auto

section \<open>Substitution\<close>

text \<open>substitute formula f in place of variable p\<close>
primrec subst :: "nat \<Rightarrow> prop_form \<Rightarrow> prop_form \<Rightarrow> prop_form" where
  "subst p f BOT = BOT"
| "subst p f TOP = TOP"
| "subst p f (VAR q) = (if p = q then f else VAR q)"
| "subst p f (NOT f') = NOT (subst p f f')"
| "subst p f (f1 AND f2) = (subst p f f1) AND (subst p f f2)" 
| "subst p f (f1 OR f2) = (subst p f f1) OR (subst p f f2)" 
| "subst p f (f1 IMP f2) = (subst p f f1) IMP (subst p f f2)" 
| "subst p f (f1 EQ f2) = (subst p f f1) EQ (subst p f f2)" 

value "let p = VAR 0; 
           q = VAR 1;
           f = (p AND q) IMP (p OR q)
        in subst 0 ((VAR 2) AND (VAR 3)) f"

lemma vars_subst:
  shows "vars (subst p f f') = 
         (if p \<in> vars f' then vars f' - {p} \<union> vars f else vars f')"
  by (induction f') auto

lemma subst_TOP:
  assumes "v p = True"
  shows "v |= f \<longleftrightarrow> v (p := x) |= (subst p TOP f)"
  using assms
  by (induction f) auto

lemma subst_BOT:
  assumes "v p = False"
  shows "v |= f \<longleftrightarrow> v (p := x) |= (subst p BOT f)"
  using assms
  by (induction f) auto

lemma satisfiable_backtrack:
  "satisfiable f \<longleftrightarrow> 
   satisfiable (subst p TOP f) \<or> satisfiable (subst p BOT f)"
  using subst_TOP subst_BOT
  unfolding satisfiable_def
  by (metis fun_upd_same fun_upd_upd)

lemma tautology_backtrack:
  "tautology f \<longleftrightarrow> 
   tautology (subst p TOP f) \<and> tautology (subst p BOT f)"
  using subst_TOP subst_BOT
  unfolding tautology_def
  by (metis fun_upd_same fun_upd_upd)

section \<open>Simplification of constants\<close>

fun simplify_const_NOT :: "prop_form \<Rightarrow> prop_form" where
  "simplify_const_NOT (NOT f) = 
   (if f = TOP then BOT
    else if f = BOT then TOP
    else NOT f)"
|  "simplify_const_NOT f = f"

lemma [simp]:
  "simplify_const_NOT (NOT TOP) = BOT"
  "simplify_const_NOT (NOT BOT) = TOP"
  by auto

lemma simplify_const_NOT [simp]:
  shows "v |= (simplify_const_NOT f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_NOT.induct) auto

lemma simplify_const_NOT_equiv:
  shows "(simplify_const_NOT f) \<equiv>\<^sub>e f"
  by (simp add: equiv_def)

fun simplify_const_AND :: "prop_form \<Rightarrow> prop_form" where
  "simplify_const_AND (f1 AND f2) = 
   (if f2 = TOP then f1
    else if f2 = BOT then BOT
    else if f1 = TOP then f2
    else if f1 = BOT then BOT
    else (f1 AND f2))"
|  "simplify_const_AND f = f"

lemma [simp]:
 "simplify_const_AND (TOP AND f) = f"
 "simplify_const_AND (BOT AND f) = BOT"
 "simplify_const_AND (f AND TOP) = f"
 "simplify_const_AND (f AND BOT) = BOT"
  by auto

lemma simplify_const_AND [simp]:
  shows "v |= (simplify_const_AND f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_AND.induct) auto

fun simplify_const_OR where
  "simplify_const_OR (f1 OR f2) = 
   (if f2 = TOP then TOP
    else if f2 = BOT then f1
    else if f1 = TOP then TOP
    else if f1 = BOT then f2
    else (f1 OR f2))"
|  "simplify_const_OR f = f"

lemma [simp]:
  "simplify_const_OR (TOP OR f) = TOP"
  "simplify_const_OR (BOT OR f) = f"
  "simplify_const_OR (f OR TOP) = TOP"
  "simplify_const_OR (f OR BOT) = f"
  by auto

lemma simplify_const_OR [simp]:
  shows "v |= (simplify_const_OR f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_OR.induct) auto

fun simplify_const_IMP where
  "simplify_const_IMP (f1 IMP f2) = 
   (if f1 = BOT then TOP
    else if f1 = TOP then f2
    else if f2 = TOP then TOP
    else if f2 = BOT then simplify_const_NOT (NOT f1)
    else (f1 IMP f2))"
|  "simplify_const_IMP f = f"

lemma [simp]:
  "simplify_const_IMP (TOP IMP f) = f"
  "simplify_const_IMP (BOT IMP f) = TOP"
  "simplify_const_IMP (f IMP TOP) = TOP"
  "simplify_const_IMP (f IMP BOT) = simplify_const_NOT (NOT f)"
  by auto

lemma simplify_const_IMP [simp]:
  shows "v |= (simplify_const_IMP f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_IMP.induct) auto

fun simplify_const_EQ where
  "simplify_const_EQ (f1 EQ f2) = 
   (if f1 = TOP then f2
    else if f2 = TOP then f1
    else if f1 = BOT then simplify_const_NOT (NOT f2)
    else if f2 = BOT then simplify_const_NOT (NOT f1)
    else (f1 EQ f2))"
|  "simplify_const_EQ f = f"


lemma [simp]:
  "simplify_const_EQ (TOP EQ f) = f"
  "simplify_const_EQ (BOT EQ f) = simplify_const_NOT (NOT f)"
  "simplify_const_EQ (f EQ TOP) = f"
  "simplify_const_EQ (f EQ BOT) = simplify_const_NOT (NOT f)"
  by auto

lemma simplify_const_EQ [simp]:
  shows "v |= (simplify_const_EQ f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_EQ.induct) auto

primrec simplify_const :: "prop_form \<Rightarrow> prop_form" where
   "simplify_const TOP = TOP"
 | "simplify_const BOT = BOT"
 | "simplify_const (VAR n) = VAR n"
 | "simplify_const (NOT f) = simplify_const_NOT (NOT (simplify_const f))" 
 | "simplify_const (f1 AND f2) = 
        simplify_const_AND ((simplify_const f1) AND (simplify_const f2))"
 | "simplify_const (f1 OR f2) = 
        simplify_const_OR ((simplify_const f1) OR (simplify_const f2))"
 | "simplify_const (f1 EQ f2) = 
        simplify_const_EQ ((simplify_const f1) EQ (simplify_const f2))"
 | "simplify_const (f1 IMP f2) = 
        simplify_const_IMP ((simplify_const f1) IMP (simplify_const f2))"

value "simplify_const (((VAR 0) AND BOT) OR (((VAR 1) EQ TOP)))"

lemma simplify_const [simp]:
  shows "v |= simplify_const f \<longleftrightarrow> v |= f"
  by (induction f) auto

lemma simplify_const_equiv:
  shows "simplify_const f \<equiv>\<^sub>e f"
  using equiv_def simplify_const
  by blast

lemma simplify_const_satisfiable [simp]:
  shows "satisfiable (simplify_const f) \<longleftrightarrow> satisfiable f"
  by (simp add: satisfiable_def)

lemma simplify_const_tautology [simp]:
  shows "tautology (simplify_const f) \<longleftrightarrow> tautology f"
  by (simp add: tautology_def)

lemma vars_simp_const [simp]:
  shows "vars (simplify_const f) \<subseteq> vars f"
  by (induction f) auto

lemma card_vars_simp_const [simp]:
  shows "card (vars (simplify_const f)) \<le> card (vars f)"
  by (meson card_mono finite_vars vars_simp_const)

lemma vars_simp_const_nonempty:
  assumes "(simplify_const f) \<noteq> TOP" "(simplify_const f) \<noteq> BOT"
  shows "vars (simplify_const f) \<noteq> {}"
  using assms
  by (induction f) (auto split: if_split_asm)

section \<open>SAT solver\<close>

lemma vars_subst_const:
  assumes "p \<in> vars f"
  shows "vars (subst p TOP f) \<subset> vars f"
        "vars (subst p BOT f) \<subset> vars f"
  using assms vars_subst  
  by fastforce+

lemma card_vars_subst_const:
  assumes "p \<in> vars f"
  shows "card (vars (subst p TOP f)) < card (vars f)"
        "card (vars (subst p BOT f)) < card (vars f)"
  by (simp_all add: assms finite_vars vars_subst_const psubset_card_mono)

definition choose_var :: "prop_form \<Rightarrow> nat" where
  "choose_var f = hd (sorted_list_of_set (vars f))"

lemma choose_var_in_vars:
  assumes "vars f \<noteq> {}"
  shows "choose_var f \<in> vars f"
  using assms
  unfolding choose_var_def
  by (metis finite_vars hd_in_set set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)

lemma choose_var_simp_const:
  assumes "simplify_const f \<noteq> TOP" "simplify_const f \<noteq> BOT"
  shows "choose_var (simplify_const f) \<in> vars (simplify_const f)"
  using assms
  by (simp add: choose_var_in_vars vars_simp_const_nonempty)  

function check_sat where
 "check_sat f = 
     (let f' = simplify_const f 
       in if f' = TOP then True
          else if f' = BOT then False
          else (let p = choose_var f'
                 in check_sat (subst p TOP f') \<or> check_sat (subst p BOT f')))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda> f. card (vars f))", simp_all)
  apply (meson card_vars_simp_const card_vars_subst_const(1) choose_var_simp_const dual_order.strict_trans2 leD leI)
  apply (meson card_vars_simp_const card_vars_subst_const(2) choose_var_simp_const not_less order.strict_trans1)
  done
  
declare check_sat.simps [simp del]

lemma satisfiable_TOP [simp]:
  shows "satisfiable TOP"
  by (simp add: satisfiable_def)

lemma unsatisfiable_BOT [simp]:
  shows "\<not> satisfiable BOT"
  by (simp add: satisfiable_def)

lemma satisfiable_simp_const_TOP [simp]:
  assumes "simplify_const f = TOP"
  shows "satisfiable f"
  by (metis assms satisfiable_TOP satisfiable_def simplify_const)

lemma unsatisfiable_simp_const_BOT [simp]:
  assumes "simplify_const f = BOT"
  shows "\<not> satisfiable f"
  by (metis assms unsatisfiable_BOT satisfiable_def simplify_const)

theorem 
  shows "check_sat f \<longleftrightarrow> satisfiable f"
proof (induction f rule: check_sat.induct)
  case (1 f)
  then show ?case
    using check_sat.simps[of f]
    using satisfiable_backtrack
    by (auto simp add: Let_def)
qed

function check_taut where
 "check_taut f = 
     (let f' = simplify_const f 
       in if f' = TOP then True
          else if f' = BOT then False
          else (let p = choose_var f'
                 in check_taut (subst p TOP f') \<and> check_taut (subst p BOT f')))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda> f. card (vars f))", simp_all)
  apply (meson card_vars_simp_const card_vars_subst_const(1) choose_var_simp_const dual_order.strict_trans2 leD leI)
  apply (meson card_vars_simp_const card_vars_subst_const(2) choose_var_simp_const not_less order.strict_trans1)
  done

declare check_taut.simps[simp del]

lemma tautology_TOP [simp]:
  shows "tautology TOP"
  by (simp add: tautology_def)

lemma refutable_BOT [simp]:
  shows "\<not> tautology BOT"
  by (simp add: tautology_def)

lemma tautology_simp_const_Top [simp]:
  assumes "simplify_const f = TOP"
  shows "tautology f"
  by (metis assms tautology_TOP tautology_def simplify_const)

lemma refutable_simp_const_BOT [simp]:
  assumes "simplify_const f = BOT"
  shows "\<not> tautology f"
  by (metis assms refutable_BOT simplify_const tautology_def)

theorem 
  shows "check_taut f \<longleftrightarrow> tautology f"
proof (induction f rule: check_taut.induct)
  case (1 f)
  then show ?case
    using check_taut.simps[of f]
    using tautology_backtrack
    by (auto simp add: Let_def)
qed

value "check_taut ((NOT ((VAR 0) AND (VAR 1)) EQ ((NOT (VAR 0)) OR (NOT (VAR 1)))))"

end

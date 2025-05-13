theory introduction
  imports Main
begin

section "Introduction"

text \<open>
Isabelle/HOL includes:

\<^item> A functional programming language
\<^item> A system for interactively proving statements

\<close>

subsection "Application: Functional Programming"

text \<open>The following example shows an implementation of the binary search algorithm, 
a termination proof for the function, and a correctness proof.\<close>

function binary_search where
\<open>binary_search list key low high = (
  if low \<ge> high then
    None
  else 
    let mid = (low + high) div 2 in
    let (k,v) = list ! mid in
    if k < key then
      binary_search list key low (mid - 1)
    else if k > key then
      binary_search list key (mid + 1) high
    else
      Some v)\<close>
  by pat_completeness auto
termination by (relation "measure (\<lambda>(list,key,low,high). 1 + high - low)") auto

(*
lemma 
  assumes sorted: "sorted list"
    and unique_keys: "distinct (map fst list)"
  shows "if binary_search list key l h = Some v then (key,v) \<in> set list"  

text "Look at @{thm[display] blub}."
*)

subsection "Application: Mathematics"

text \<open>If you are more interested in mathematics than programming, the following example might be for you.
It is a proof that there are infinitely many prime numbers formalized in Isabelle.\<close>


definition is_prime :: "nat \<Rightarrow> bool" where 
"is_prime n \<equiv> n > 1 \<and> (\<nexists>a b. a<n \<and> b<n \<and> a*b = n)"

lemma two_is_prime: "is_prime 2"
  unfolding is_prime_def 
  using less_2_cases by fastforce

lemma zero_not_prime: "\<not>is_prime 0"
  unfolding is_prime_def by simp

lemma exists_prime_divider:
  assumes "n > 1"
  shows "\<exists>k. is_prime k \<and> k dvd n"
using assms proof (induct n rule: less_induct)
  case (less n)

  show "\<exists>k. is_prime k \<and> k dvd n "
  proof (cases "is_prime n")
    case True
    assume "is_prime n"
    moreover have "n dvd n"
      by simp
    ultimately show "\<exists>k. is_prime k \<and> k dvd n"
      by blast
  next
    case False
    assume "\<not>is_prime n"
    from this obtain a b
      where "a * b = n"
        and "a < n"
        and "b < n"
      unfolding is_prime_def 
      using \<open>n > 1\<close> by auto

    have "a > 1"
      using \<open>a * b = n\<close> \<open>b < n\<close> le_less_trans by auto

    obtain ap where "is_prime ap" and "ap dvd a"
      using \<open>1 < a\<close> \<open>a < n\<close> less.hyps by blast

    hence "ap dvd n"
      using \<open>a * b = n\<close> dvd_mult2 by blast

    with `is_prime ap`
    show "\<exists>k. is_prime k \<and> k dvd n"
      by auto
  qed
qed




lemma infinite_primes:
  shows "infinite {x. is_prime x}"
proof 
  assume "finite {x. is_prime x}"


  define P where "P \<equiv> (\<Prod>{x. is_prime x}) + 1"

  have "P > 1"
    unfolding P_def
    using `finite {x. is_prime x}` zero_not_prime
    using linorder_neqE_nat by auto



  have "is_prime P"
  proof (rule ccontr)
    assume "\<not> is_prime P"

    with exists_prime_divider
    obtain p where "is_prime p" and "p dvd P"
      using \<open>1 < P\<close> by blast

    hence "p dvd (P - (\<Prod>{x. is_prime x}))"
      by (meson \<open>finite {x. is_prime x}\<close> dvd_diff_nat dvd_prod_eqI mem_Collect_eq)

    hence "p dvd 1"
      unfolding P_def by simp

    thus False
      using \<open>is_prime p\<close> is_prime_def by auto
  qed

  moreover have "P > n" if "is_prime n" for n
    by (metis One_nat_def P_def \<open>1 < P\<close> \<open>finite {x. is_prime x}\<close> add.right_neutral add_Suc_right dvd_prod_eqI le_simps(3) mem_Collect_eq nat_dvd_not_less not_less that)

  ultimately show False
    by blast

qed






end
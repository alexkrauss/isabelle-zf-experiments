(*  Title:      ZF/upair.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge

Observe the order of dependence:
    Upair is defined in terms of Replace
    \<union> is defined in terms of Upair and \<Union>(similarly for Int)
    cons is defined in terms of Upair and Un
    Ordered pairs and descriptions are defined using cons ("set notation")
*)

section\<open>Unordered Pairs\<close>

theory Unordered_Pair
imports Set_Theory
keywords "print_tcset" :: diag
begin

ML_file "Tools/typechk.ML"

lemma atomize_ball [symmetric, rulify]:
     "(!!x. x \<in> A ==> P(x)) == Trueprop (\<forall>x\<in>A. P(x))"
by (simp add: Ball_def atomize_all atomize_imp)


subsection\<open>Unordered Pairs: constant @{term Upair}\<close>

lemma Upair_iff [simp]: "c \<in> Upair a b \<longleftrightarrow> (c=a | c=b)"
by (unfold Upair_def, blast)

lemma UpairI1: "a \<in> Upair a b"
by simp

lemma UpairI2: "b \<in> Upair a b"
by simp

lemma UpairE: "[| a \<in> Upair b c;  a=b ==> P;  a=c ==> P |] ==> P"
by (simp, blast)

subsection\<open>Rules for Binary Union, Defined via @{term Upair}\<close>

lemma Un_iff [simp]: "c \<in> A \<union> B \<longleftrightarrow> (c \<in> A | c \<in> B)"
apply (simp add: Un_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma UnI1: "c \<in> A ==> c \<in> A \<union> B"
by simp

lemma UnI2: "c \<in> B ==> c \<in> A \<union> B"
by simp

declare UnI1 [elim?]  UnI2 [elim?]

lemma UnE [elim!]: "[| c \<in> A \<union> B;  c \<in> A ==> P;  c \<in> B ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma UnE': "[| c \<in> A \<union> B;  c \<in> A ==> P;  [| c \<in> B;  c\<notin>A |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI [intro!]: "(c \<notin> B ==> c \<in> A) ==> c \<in> A \<union> B"
by (simp, blast)

subsection\<open>Rules for Binary Intersection, Defined via @{term Upair}\<close>

lemma Int_iff [simp]: "c \<in> A \<inter> B \<longleftrightarrow> (c \<in> A & c \<in> B)"
apply (unfold Int_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma IntI [intro!]: "[| c \<in> A;  c \<in> B |] ==> c \<in> A \<inter> B"
by simp

lemma IntD1: "c \<in> A \<inter> B ==> c \<in> A"
by simp

lemma IntD2: "c \<in> A \<inter> B ==> c \<in> B"
by simp

lemma IntE [elim!]: "[| c \<in> A \<inter> B;  [| c \<in> A; c \<in> B |] ==> P |] ==> P"
by simp


subsection\<open>Rules for Set Difference, Defined via @{term Upair}\<close>

lemma Diff_iff [simp]: "c \<in> A-B \<longleftrightarrow> (c \<in> A & c\<notin>B)"
by (unfold Diff_def, blast)

lemma DiffI [intro!]: "[| c \<in> A;  c \<notin> B |] ==> c \<in> A - B"
by simp

lemma DiffD1: "c \<in> A - B ==> c \<in> A"
by simp

lemma DiffD2: "c \<in> A - B ==> c \<notin> B"
by simp

lemma DiffE [elim!]: "[| c \<in> A - B;  [| c \<in> A; c\<notin>B |] ==> P |] ==> P"
by simp


subsection\<open>Rules for @{term cons}\<close>

lemma cons_iff [simp]: "a \<in> cons b A \<longleftrightarrow> (a=b | a \<in> A)"
apply (unfold cons_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

(*risky as a typechecking rule, but solves otherwise unconstrained goals of
the form x \<in> ?A*)
lemma consI1 [simp,TC]: "a \<in> cons a B"
by simp


lemma consI2: "a \<in> B ==> a \<in> cons b B"
by simp

lemma consE [elim!]: "[| a \<in> cons b A;  a=b ==> P;  a \<in> A ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma consE':
    "[| a \<in> cons b A;  a=b ==> P;  [| a \<in> A;  a\<noteq>b |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule*)
lemma consCI [intro!]: "(a\<notin>B ==> a=b) ==> a \<in> cons b B"
by (simp, blast)

lemma cons_not_0 [simp]: "cons a B \<noteq> 0"
by (blast elim: equalityE)

lemmas cons_neq_0 = cons_not_0 [THEN notE]

declare cons_not_0 [THEN not_sym, simp]


subsection\<open>Singletons\<close>

lemma singleton_iff: "a \<in> {b} \<longleftrightarrow> a=b"
by simp

lemma singletonI [intro!]: "a \<in> {a}"
by (rule consI1)

lemmas singletonE = singleton_iff [THEN iffD1, elim_format, elim!]


subsection\<open>Descriptions\<close>

lemma the_equality [intro]:
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
apply (unfold the_def)
apply (fast dest: subst)
done

(* Only use this if you already know \<exists>!x. P(x) *)
lemma the_equality2: "[| \<exists>!x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
by blast

lemma theI: "\<exists>!x. P(x) ==> P(THE x. P(x))"
apply (erule ex1E)
apply (subst the_equality)
apply (blast+)
done

(*No congruence rule is necessary: if @{term"\<forall>y.P(y)\<longleftrightarrow>Q(y)"} then
  @{term "THE x.P(x)"}  rewrites to @{term "THE x.Q(x)"} *)

(*If it's "undefined", it's zero!*)
lemma the_0: "~ (\<exists>!x. P(x)) ==> (THE x. P(x))=0"
apply (unfold the_def)
apply (blast elim!: ReplaceE)
done

(*Easier to apply than theI: conclusion has only one occurrence of P*)
lemma theI2:
    assumes p1: "~ Q(0) ==> \<exists>!x. P(x)"
        and p2: "!!x. P(x) ==> Q(x)"
    shows "Q(THE x. P(x))"
apply (rule classical)
apply (rule p2)
apply (rule theI)
apply (rule classical)
apply (rule p1)
apply (erule the_0 [THEN subst], assumption)
done

lemma the_eq_trivial [simp]: "(THE x. x = a) = a"
by blast

lemma the_eq_trivial2 [simp]: "(THE x. a = x) = a"
by blast


subsection\<open>Conditional Terms: \<open>if-then-else\<close>\<close>

lemma if_true [simp]: "(if True then a else b) = a"
by (unfold if_def, blast)

lemma if_false [simp]: "(if False then a else b) = b"
by (unfold if_def, blast)

(*Never use with case splitting, or if P is known to be true or false*)
lemma if_cong:
    "[| P\<longleftrightarrow>Q;  Q ==> a=c;  ~Q ==> b=d |]
     ==> (if P then a else b) = (if Q then c else d)"
by (simp add: if_def cong add: conj_cong)

(*Prevents simplification of x and y \<in> faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
lemma if_weak_cong: "P\<longleftrightarrow>Q ==> (if P then x else y) = (if Q then x else y)"
by simp

(*Not needed for rewriting, since P would rewrite to True anyway*)
lemma if_P: "P ==> (if P then a else b) = a"
by (unfold if_def, blast)

(*Not needed for rewriting, since P would rewrite to False anyway*)
lemma if_not_P: "~P ==> (if P then a else b) = b"
by (unfold if_def, blast)

lemma split_if [split]:
     "P(if Q then x else y) \<longleftrightarrow> ((Q \<longrightarrow> P(x)) & (~Q \<longrightarrow> P(y)))"
by (case_tac Q, simp_all)

(** Rewrite rules for boolean case-splitting: faster than split_if [split]
**)

lemmas split_if_eq1 = split_if [of "%x. x = b"] for b
lemmas split_if_eq2 = split_if [of "%x. a = x"] for a

lemmas split_if_mem1 = split_if [of "%x. x \<in> b"] for b
lemmas split_if_mem2 = split_if [of "%x. a \<in> x"] for a

lemmas split_ifs = split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

(*Logically equivalent to split_if_mem2*)
lemma if_iff: "a: (if P then x else y) \<longleftrightarrow> P & a \<in> x | ~P & a \<in> y"
by simp

lemma if_type [TC]:
    "[| P ==> a \<in> A;  ~P ==> b \<in> A |] ==> (if P then a else b): A"
by simp

(** Splitting IFs in the assumptions **)

lemma split_if_asm: "P(if Q then x else y) \<longleftrightarrow> (~((Q & ~P(x)) | (~Q & ~P(y))))"
by simp

lemmas if_splits = split_if split_if_asm


subsection\<open>Consequences of Foundation\<close>

(*was called mem_anti_sym*)
lemma mem_asym: "[| a \<in> b;  ~P ==> b \<in> a |] ==> P"
apply (rule classical)
apply (rule_tac A1 = "{a,b}" in foundation [THEN disjE])
apply (blast elim!: equalityE)+
done

(*was called mem_anti_refl*)
lemma mem_irrefl: "a \<in> a ==> P"
by (blast intro: mem_asym)

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

lemma mem_not_refl: "a \<notin> a"
apply (rule notI)
apply (erule mem_irrefl)
done

(*Good for proving inequalities by rewriting*)
lemma mem_imp_not_eq: "a \<in> A ==> a \<noteq> A"
by (blast elim!: mem_irrefl)

lemma eq_imp_not_mem: "a=A ==> a \<notin> A"
by (blast intro: elim: mem_irrefl)

subsection\<open>Rules for Successor\<close>

lemma succ_iff: "i \<in> succ(j) \<longleftrightarrow> i=j | i \<in> j"
by (unfold succ_def, blast)

lemma succI1 [simp]: "i \<in> succ(i)"
by (simp add: succ_iff)

lemma succI2: "i \<in> j ==> i \<in> succ(j)"
by (simp add: succ_iff)

lemma succE [elim!]:
    "[| i \<in> succ(j);  i=j ==> P;  i \<in> j ==> P |] ==> P"
apply (simp add: succ_iff, blast)
done

(*Classical introduction rule*)
lemma succCI [intro!]: "(i\<notin>j ==> i=j) ==> i \<in> succ(j)"
by (simp add: succ_iff, blast)

lemma succ_not_0 [simp]: "succ(n) \<noteq> 0"
by (blast elim!: equalityE)

lemmas succ_neq_0 = succ_not_0 [THEN notE, elim!]

declare succ_not_0 [THEN not_sym, simp]
declare sym [THEN succ_neq_0, elim!]

(* @{term"succ(c) \<subseteq> B ==> c \<in> B"} *)
lemmas succ_subsetD = succI1 [THEN [2] subsetD]

(* @{term"succ(b) \<noteq> b"} *)
lemmas succ_neq_self = succI1 [THEN mem_imp_not_eq, THEN not_sym]

lemma succ_inject_iff [simp]: "succ(m) = succ(n) \<longleftrightarrow> m=n"
by (blast elim: mem_asym elim!: equalityE)

lemmas succ_inject = succ_inject_iff [THEN iffD1, dest!]


subsection\<open>Miniscoping of the Bounded Universal Quantifier\<close>

lemma ball_simps1:
     "(\<forall>x\<in>A. P(x) & Q)   \<longleftrightarrow> (\<forall>x\<in>A. P(x)) & (A=0 | Q)"
     "(\<forall>x\<in>A. P(x) | Q)   \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) | Q)"
     "(\<forall>x\<in>A. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) \<longrightarrow> Q)"
     "(~(\<forall>x\<in>A. P(x))) \<longleftrightarrow> (\<exists>x\<in>A. ~P(x))"
     "(\<forall>x\<in>0.P(x)) \<longleftrightarrow> True"
     "(\<forall>x\<in>succ i. P(x)) \<longleftrightarrow> P(i) & (\<forall>x\<in>i. P x)"
     "(\<forall>x\<in>cons a B. P(x)) \<longleftrightarrow> P(a) & (\<forall>x\<in>B. P x)"
     "(\<forall>x\<in>RepFun A f. P(x)) \<longleftrightarrow> (\<forall>y\<in>A. P (f y))"
     "(\<forall>x\<in>\<Union>(A).P x) \<longleftrightarrow> (\<forall>y\<in>A. \<forall>x\<in>y. P x)"
by blast+

lemma ball_simps2:
     "(\<forall>x\<in>A. P & Q(x))   \<longleftrightarrow> (A=0 | P) & (\<forall>x\<in>A. Q(x))"
     "(\<forall>x\<in>A. P | Q(x))   \<longleftrightarrow> (P | (\<forall>x\<in>A. Q(x)))"
     "(\<forall>x\<in>A. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x\<in>A. Q(x)))"
by blast+

lemma ball_simps3:
     "(\<forall>x\<in>Collect A Q. P(x)) \<longleftrightarrow> (\<forall>x\<in>A. Q(x) \<longrightarrow> P(x))"
by blast+

lemmas ball_simps [simp] = ball_simps1 ball_simps2 ball_simps3

lemma ball_conj_distrib:
    "(\<forall>x\<in>A. P(x) & Q(x)) \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) & (\<forall>x\<in>A. Q(x)))"
by blast


subsection\<open>Miniscoping of the Bounded Existential Quantifier\<close>

lemma bex_simps1:
     "(\<exists>x\<in>A. P(x) & Q) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) & Q)"
     "(\<exists>x\<in>A. P(x) | Q) \<longleftrightarrow> (\<exists>x\<in>A. P(x)) | (A\<noteq>0 & Q)"
     "(\<exists>x\<in>A. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<forall>x\<in>A. P(x)) \<longrightarrow> (A\<noteq>0 & Q))"
     "(\<exists>x\<in>0.P(x)) \<longleftrightarrow> False"
     "(\<exists>x\<in>succ(i).P(x)) \<longleftrightarrow> P(i) | (\<exists>x\<in>i. P(x))"
     "(\<exists>x\<in>cons a B. P(x)) \<longleftrightarrow> P(a) | (\<exists>x\<in>B. P(x))"
     "(\<exists>x\<in>RepFun A f. P(x)) \<longleftrightarrow> (\<exists>y\<in>A. P(f(y)))"
     "(\<exists>x\<in>\<Union>(A).P(x)) \<longleftrightarrow> (\<exists>y\<in>A. \<exists>x\<in>y.  P(x))"
     "(~(\<exists>x\<in>A. P(x))) \<longleftrightarrow> (\<forall>x\<in>A. ~P(x))"
by blast+

lemma bex_simps2:
     "(\<exists>x\<in>A. P & Q(x)) \<longleftrightarrow> (P & (\<exists>x\<in>A. Q(x)))"
     "(\<exists>x\<in>A. P | Q(x)) \<longleftrightarrow> (A\<noteq>0 & P) | (\<exists>x\<in>A. Q(x))"
     "(\<exists>x\<in>A. P \<longrightarrow> Q(x)) \<longleftrightarrow> ((A=0 | P) \<longrightarrow> (\<exists>x\<in>A. Q(x)))"
by blast+

lemma bex_simps3:
     "(\<exists>x\<in>Collect A Q. P(x)) \<longleftrightarrow> (\<exists>x\<in>A. Q(x) & P(x))"
by blast

lemmas bex_simps [simp] = bex_simps1 bex_simps2 bex_simps3

lemma bex_disj_distrib:
    "(\<exists>x\<in>A. P(x) | Q(x)) \<longleftrightarrow> ((\<exists>x\<in>A. P(x)) | (\<exists>x\<in>A. Q(x)))"
by blast


(** One-point rule for bounded quantifiers: see HOL/Set.ML **)

lemma bex_triv_one_point1 [simp]: "(\<exists>x\<in>A. x=a) \<longleftrightarrow> (a \<in> A)"
by blast

lemma bex_triv_one_point2 [simp]: "(\<exists>x\<in>A. a=x) \<longleftrightarrow> (a \<in> A)"
by blast

lemma bex_one_point1 [simp]: "(\<exists>x\<in>A. x=a & P(x)) \<longleftrightarrow> (a \<in> A & P(a))"
by blast

lemma bex_one_point2 [simp]: "(\<exists>x\<in>A. a=x & P(x)) \<longleftrightarrow> (a \<in> A & P(a))"
by blast

lemma ball_one_point1 [simp]: "(\<forall>x\<in>A. x=a \<longrightarrow> P(x)) \<longleftrightarrow> (a \<in> A \<longrightarrow> P(a))"
by blast

lemma ball_one_point2 [simp]: "(\<forall>x\<in>A. a=x \<longrightarrow> P(x)) \<longleftrightarrow> (a \<in> A \<longrightarrow> P(a))"
by blast


subsection\<open>Miniscoping of the Replacement Operator\<close>

text\<open>These cover both @{term Replace} and @{term Collect}\<close>
lemma Rep_simps [simp]:
     "{x. y \<in> 0, R x y} = 0"
     "{x \<in> 0. P(x)} = 0"
     "{x \<in> A. Q} = (if Q then A else 0)"
     "RepFun 0 f = 0"
     "RepFun (succ i) f = cons (f i) (RepFun i f)"
     "RepFun (cons a B) f = cons (f a) (RepFun B f)"
by (simp_all, blast+)


subsection\<open>Miniscoping of Unions\<close>

lemma UN_simps1:
     "(\<Union>x\<in>C. cons a (B x)) = (if C=0 then 0 else cons a (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) \<union> B')   = (if C=0 then 0 else (\<Union>x\<in>C. A(x)) \<union> B')"
     "(\<Union>x\<in>C. A' \<union> B(x))   = (if C=0 then 0 else A' \<union> (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) \<inter> B')  = ((\<Union>x\<in>C. A(x)) \<inter> B')"
     "(\<Union>x\<in>C. A' \<inter> B(x))  = (A' \<inter> (\<Union>x\<in>C. B(x)))"
     "(\<Union>x\<in>C. A(x) - B')    = ((\<Union>x\<in>C. A(x)) - B')"
     "(\<Union>x\<in>C. A' - B(x))    = (if C=0 then 0 else A' - (\<Inter>x\<in>C. B(x)))"
apply (simp_all add: Inter_def)
apply (blast intro!: equalityI )+
done

lemma UN_simps2:
      "(\<Union>x\<in>\<Union>(A). B(x)) = (\<Union>y\<in>A. \<Union>x\<in>y. B(x))"
      "(\<Union>z\<in>(\<Union>x\<in>A. B(x)). C(z)) = (\<Union>x\<in>A. \<Union>z\<in>B(x). C(z))"
      "(\<Union>x\<in>RepFun A f. B(x)) = (\<Union>a\<in>A. B(f(a)))"
by blast+

lemmas UN_simps [simp] = UN_simps1 UN_simps2

text\<open>Opposite of miniscoping: pull the operator out\<close>

lemma UN_extend_simps1:
     "(\<Union>x\<in>C. A(x)) \<union> B   = (if C=0 then B else (\<Union>x\<in>C. A(x) \<union> B))"
     "((\<Union>x\<in>C. A(x)) \<inter> B) = (\<Union>x\<in>C. A(x) \<inter> B)"
     "((\<Union>x\<in>C. A(x)) - B) = (\<Union>x\<in>C. A(x) - B)"
apply simp_all
apply blast+
done

lemma UN_extend_simps2:
     "cons a (\<Union>x\<in>C. B(x)) = (if C=0 then {a} else (\<Union>x\<in>C. cons a (B x)))"
     "A \<union> (\<Union>x\<in>C. B(x))   = (if C=0 then A else (\<Union>x\<in>C. A \<union> B(x)))"
     "(A \<inter> (\<Union>x\<in>C. B(x))) = (\<Union>x\<in>C. A \<inter> B(x))"
     "A - (\<Inter>x\<in>C. B(x))    = (if C=0 then A else (\<Union>x\<in>C. A - B(x)))"
     "(\<Union>y\<in>A. \<Union>x\<in>y. B(x)) = (\<Union>x\<in>\<Union>(A). B(x))"
     "(\<Union>a\<in>A. B(f(a))) = (\<Union>x\<in>RepFun A f. B(x))"
apply (simp_all add: Inter_def)
apply (blast intro!: equalityI)+
done

lemma UN_UN_extend:
     "(\<Union>x\<in>A. \<Union>z\<in>B(x). C(z)) = (\<Union>z\<in>(\<Union>x\<in>A. B(x)). C(z))"
by blast

lemmas UN_extend_simps = UN_extend_simps1 UN_extend_simps2 UN_UN_extend


subsection\<open>Miniscoping of Intersections\<close>

lemma INT_simps1:
     "(\<Inter>x\<in>C. A(x) \<inter> B) = (\<Inter>x\<in>C. A(x)) \<inter> B"
     "(\<Inter>x\<in>C. A(x) - B)   = (\<Inter>x\<in>C. A(x)) - B"
     "(\<Inter>x\<in>C. A(x) \<union> B)  = (if C=0 then 0 else (\<Inter>x\<in>C. A(x)) \<union> B)"
by (simp_all add: Inter_def, blast+)

lemma INT_simps2:
     "(\<Inter>x\<in>C. A \<inter> B(x)) = A \<inter> (\<Inter>x\<in>C. B(x))"
     "(\<Inter>x\<in>C. A - B(x))   = (if C=0 then 0 else A - (\<Union>x\<in>C. B(x)))"
     "(\<Inter>x\<in>C. cons a (B x)) = (if C=0 then 0 else cons a (\<Inter>x\<in>C. B(x)))"
     "(\<Inter>x\<in>C. A \<union> B(x))  = (if C=0 then 0 else A \<union> (\<Inter>x\<in>C. B(x)))"
  by (auto simp add: Inter_def)

lemmas INT_simps [simp] = INT_simps1 INT_simps2

text\<open>Opposite of miniscoping: pull the operator out\<close>


lemma INT_extend_simps1:
     "(\<Inter>x\<in>C. A(x)) \<inter> B = (\<Inter>x\<in>C. A(x) \<inter> B)"
     "(\<Inter>x\<in>C. A(x)) - B = (\<Inter>x\<in>C. A(x) - B)"
     "(\<Inter>x\<in>C. A(x)) \<union> B  = (if C=0 then B else (\<Inter>x\<in>C. A(x) \<union> B))"
  by (auto simp add: Inter_def)

lemma INT_extend_simps2:
     "A \<inter> (\<Inter>x\<in>C. B(x)) = (\<Inter>x\<in>C. A \<inter> B(x))"
     "A - (\<Union>x\<in>C. B(x))   = (if C=0 then A else (\<Inter>x\<in>C. A - B(x)))"
     "cons a (\<Inter>x\<in>C. B(x)) = (if C=0 then {a} else (\<Inter>x\<in>C. cons a (B x)))"
     "A \<union> (\<Inter>x\<in>C. B(x))  = (if C=0 then A else (\<Inter>x\<in>C. A \<union> B(x)))"
  by (auto simp add: Inter_def)

lemmas INT_extend_simps = INT_extend_simps1 INT_extend_simps2


subsection\<open>Other simprules\<close>


(*** Miniscoping: pushing in big Unions, Intersections, quantifiers, etc. ***)

lemma misc_simps [simp]:
     "0 \<union> A = A"
     "A \<union> 0 = A"
     "0 \<inter> A = 0"
     "A \<inter> 0 = 0"
     "0 - A = 0"
     "A - 0 = A"
     "\<Union>(0) = 0"
     "\<Union>(cons b A) = b \<union> \<Union>(A)"
     "\<Inter>({b}) = b"
by blast+

end

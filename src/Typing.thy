theory Typing
  imports Function
begin

ML_file "zf_logic.ML"


text \<open>
  We define a syntax for types, which is disconnected from the actual term language, but
  uses the same machinery. It just consists of a type declaration and some uninterpreted symbols,
  most notably for Pi-types (dependent function types).
  
  We define some syntax translations to introduce a telescope-like syntax.
\<close>

typedecl type

axiomatization set :: "i \<Rightarrow> type"
and Type :: "type"
and Pi_type :: "type \<Rightarrow> ('a \<Rightarrow> type) \<Rightarrow> type"
and Implicit_Pi_type :: "type \<Rightarrow> ('a \<Rightarrow> type) \<Rightarrow> type"
and has_type :: "('b::{}) \<Rightarrow> type \<Rightarrow> prop" (infix ":::" 40)

syntax
  "_telescope" :: "[pttrn, type, type] \<Rightarrow> type"  ("'(_ : _') \<Rightarrow> _" 50)
  "_telescope_implicit" :: "[pttrn, type, type] \<Rightarrow> type"  ("'{_ : _'} \<Rightarrow> _" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "{x : A} \<Rightarrow> B" \<rightleftharpoons> "CONST Implicit_Pi_type A (\<lambda>x. B)"

term "(x : A) \<Rightarrow> (y : B) \<Rightarrow> C y"
term "t ::: (x : set A) \<Rightarrow> (set (A + B))"


subsection \<open> Interpretation of soft types as propositions \<close>

definition Univ :: "i \<Rightarrow> o"
  where "Univ x \<longleftrightarrow> True"

             
ML_file "soft_type.ML"

text \<open>
  The interpretation of soft types as defined above is given extra-logically by a function that
  translates typing judgements into propositions.

  Below are some examples:
\<close>


axiomatization
  List :: "i \<Rightarrow> i"
and Nil :: "i \<Rightarrow> i"
and Cons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"


lemma "Cons ::: (A: Type) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (List A)) \<Rightarrow> set (List A)"
  oops

lemma "Nil ::: (A : Type) \<Rightarrow> set (List A)"
  oops




ML_file "soft_type_context.ML"
ML_file "soft_type_inference.ML"


context
  fixes x n m A B N :: "i"
  fixes f g S T :: "i \<Rightarrow> i"
  fixes plus :: "i \<Rightarrow> i \<Rightarrow> i"
  fixes append :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
begin




declare [[type "plus ::: (x: set N) \<Rightarrow> (y : set N) \<Rightarrow> set N"]]
declare [[type "Pair ::: (x: set A) \<Rightarrow> (y : set B) \<Rightarrow> set (A \<times> B)"]]
declare [[type "Nil ::: (A: Type) \<Rightarrow> set (List A)"]]
declare [[type "Cons ::: (A: Type) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (List A)) \<Rightarrow> set (List A)"]]
declare [[type "n ::: set N"]]



ML \<open>

Soft_Type_Inference.infer_type @{context} [
  @{term "append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "append A (Nil A) ys = ys"} 
]

\<close>


end


end

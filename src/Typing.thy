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

ML_file "soft_type.ML"

text \<open>
  The interpretation of soft types as defined above is given extra-logically by a function that
  translates typing judgements into propositions.

  Below are some examples:
\<close>


context
  fixes A B N :: i \<comment> \<open>some sets\<close>
  fixes f :: "i \<Rightarrow> i" \<comment> \<open>a function\<close>
  fixes vec :: "i \<Rightarrow> i" \<comment> \<open>a type constructor\<close>
  fixes vec_concat :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" \<comment> \<open> Vector concatenation. First two arguments are type arguments \<close>
begin

ML \<open>
  fun testfn ctxt t = 
    let
      val j = Soft_Type.judgement_of_prop t
      val prp = Soft_Type.prop_of_judgement j
      val _ = if (prp <> t) then error ("Not inverse" ^ (@{make_string} (prp, t))) else ();
    in 
      Syntax.pretty_term ctxt prp
    end;

    testfn @{context} @{term "f ::: (x : set A) \<Rightarrow> set (A + B)"};
    testfn @{context} @{term "vec_concat ::: {n : set N} \<Rightarrow> {m : set N} \<Rightarrow> (x : set (vec n)) \<Rightarrow> (y : set (vec m)) \<Rightarrow> set (vec (n + m))"};
  \<close>

end




ML \<open>
  
fun expect (x:Soft_Type.soft_type) f = if not (f x) then raise Fail ("expectation failed. Value is " ^ @{make_string} x) else ();


(* substitute a free *)
expect (Soft_Type.subst_bound @{term "x::i"} (Soft_Type.Set (Bound 0))) 
   (curry op = (Soft_Type.Set @{term "x::i"}));

(* substitute a bound -- no effect *)
expect (Soft_Type.subst_bound (Bound 0) (Soft_Type.Set (Bound 0))) 
   (curry op = (Soft_Type.Set (Bound 0)));

(* loose bounds are decremented *)
expect (Soft_Type.subst_bound @{term "0"} (Soft_Type.Set (Bound 1))) 
   (curry op = (Soft_Type.Set (Bound 0)));

(* substitute under Pi *)

expect (Soft_Type.subst_bound @{term "y::i"} 
   (Soft_Type.Pi (false, "x", @{typ i}, Soft_Type.Set (@{term "A::i"}), Soft_Type.Set (@{term "B::i=>i"} $ Bound 1)))) 
   (curry op = (Soft_Type.Pi (false, "x", @{typ i}, Soft_Type.Set (@{term "A::i"}), Soft_Type.Set (@{term "(B::(i\<Rightarrow>i)) y"}))));

\<close>

ML_file "soft_type_context.ML"
ML_file "soft_type_inference.ML"



context
  fixes x n m A B N :: "i"
  fixes f g S T :: "i \<Rightarrow> i"
  fixes plus :: "i \<Rightarrow> i \<Rightarrow> i"
begin


declare [[type "plus ::: (x: set N) \<Rightarrow> (y : set N) \<Rightarrow> set N"]]
declare [[type "n ::: set N"]]

ML \<open>


Soft_Type_Inference.infer_type @{context} @{term "plus n n"}

\<close>




end

end
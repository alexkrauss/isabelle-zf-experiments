theory Tests
imports Typing
begin


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
      (* In the process, we lose type information, but the next step should be a fixpoint *)
      val j2 = Soft_Type.judgement_of_prop prp
      val _ = if (j <> j2) then error ("Not inverse" ^ (@{make_string} (prp, t))) else ();
    in 
      Syntax.pretty_term ctxt prp
    end;

    testfn @{context} @{term "f ::: (x : set A) \<Rightarrow> set (A + B)"};
    testfn @{context} @{term "vec_concat ::: {n : set N} \<Rightarrow> {m : set N} \<Rightarrow> (x : set (vec n)) \<Rightarrow> (y : set (vec m)) \<Rightarrow> set (vec (n + m))"};
  \<close>

end



text \<open> Soft_Type.subst_bound \<close>

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
   (Soft_Type.Pi (false, "x", Soft_Type.Set (@{term "A::i"}), Soft_Type.Set (@{term "B::i=>i"} $ Bound 1)))) 
   (curry op = (Soft_Type.Pi (false, "x", Soft_Type.Set (@{term "A::i"}), Soft_Type.Set (@{term "(B::(i\<Rightarrow>i)) y"}))));

\<close>

end
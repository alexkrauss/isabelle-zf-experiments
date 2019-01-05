(*  Title:      soft_type_inference.ML
    Author:     Alexander Krauss

Soft type inference.
*)

signature SOFT_TYPE_INFERENCE =
sig

  datatype constraint =
    Eq of Soft_Type.soft_type * Soft_Type.soft_type  (* equality *)

  (* Context \<Gamma>, which maps variables and constants to their types. Also used to collect constraints
     during inference.
   *)
  datatype inference_context = Inference_Context of {
    var_types: Soft_Type.soft_type Termtab.table,
    constraints: constraint list,
    fresh_idx: int
  }

  val init_context: (term * Soft_Type.soft_type) list -> inference_context;

  (* computes the type of a term in a context, and collects constraints *)
  val collect_constraints: inference_context -> term -> Soft_Type.soft_type * inference_context

  (* removes redundant and trivial constraints *)
val simplify_constraints: constraint list -> (indexname * Soft_Type.soft_type) list
     -> (term * term) list
     -> (indexname * Soft_Type.soft_type) list * (term * term) list

val infer_type: Proof.context -> term -> unit;

end;

structure Soft_Type_Inference : SOFT_TYPE_INFERENCE =
struct

  open Soft_Type

  datatype constraint =
    Eq of Soft_Type.soft_type * Soft_Type.soft_type

  datatype inference_context = Inference_Context of {
    var_types: Soft_Type.soft_type Termtab.table,
    constraints: constraint list,
    fresh_idx: int
  }

  fun init_context (vts : (term * Soft_Type.soft_type) list) =
    Inference_Context {
      var_types = Termtab.make vts,
      constraints = [],
      fresh_idx = 0
    };
  
  fun get_var_type (Inference_Context {var_types, ...}) (v : term) =
    Termtab.lookup var_types v;
  
  fun add_constraint (c : constraint) (Inference_Context {var_types, constraints, fresh_idx}) =
    Inference_Context {var_types=var_types, constraints = c :: constraints, fresh_idx=fresh_idx};
  
  fun fresh_variable (Inference_Context {var_types, constraints, fresh_idx}) =
    (Soft_Type.STVar ("A", fresh_idx), 
     Inference_Context {var_types=var_types, constraints=constraints, fresh_idx=fresh_idx + 1})

  fun add_free (v, st) (Inference_Context {var_types, constraints, fresh_idx}) =
    Inference_Context {var_types=Termtab.update_new (v, st) var_types, constraints=constraints, fresh_idx=fresh_idx};

  fun collect_constraints (Gamma : inference_context) t =
    case t of 
      Free _ => 
        (case get_var_type Gamma t of
          SOME st => (st, Gamma)
        | NONE => fresh_variable Gamma)
    | Const _ => 
        (case get_var_type Gamma t of
          SOME st => (st, Gamma)
        | NONE => error ("Cannot resolve type of constant"))
    | s $ u => 
        let
          val (s_st, Gamma1) = collect_constraints Gamma s
          val (u_st, Gamma2) = collect_constraints Gamma1 u
        in
          case s_st of 
            Soft_Type.Pi (_, _, _, sTA, sTB) =>  
              let
                val new_constraint = Eq (sTA, u_st)
                val application_type = Soft_Type.subst_bound u sTB
              in
                (application_type, add_constraint new_constraint Gamma2)
              end
          | _ => error ("bad soft_type at application head: " ^ quote (@{make_string} s_st))
        end
    | Bound _ => error "illegal bound variable"
    | Var _ => error "illegal Var"
    | Abs (x, T, body) => 
        let 
          val (stvar, Gamma1) = fresh_variable Gamma (* invent fresh type variable *)
          val x_free = Free (x, T)                   (* FIXME!: Proper fresh name in context *)
          val Gamma2 = add_free (Free (x, T), stvar) Gamma1 (* assume that x has that type in the context *)
          val (body_st, Gamma3) = collect_constraints Gamma2 (Term.subst_bound (x_free, body))
          val st = Soft_Type.Pi (false, x, T, stvar, Soft_Type.abstract_over x_free body_st)
          val Inference_Context {constraints, ...} = Gamma3
          val Inference_Context {var_types, fresh_idx, ...} = Gamma2
        in
          (st, Inference_Context {var_types=var_types, fresh_idx=fresh_idx, constraints=constraints})
        end;

  
  (* returns true, if a variable occurs in the given soft type *)
  fun occurs_check idxn st =
    case st of
      Set _ => false
    | Pi (_, _, _, stA, stB) => occurs_check idxn stA andalso occurs_check idxn stB
    | STVar v => (idxn = v)

  (* Simple constraint simplification by unification. 
     Applies unification on the constraints, creating a type substitution and a list of term equations
     that must hold to make the constraints true.
  *)
  fun simplify_constraints [] type_subst term_eqs = (type_subst, term_eqs)
    | simplify_constraints (c :: cs) type_subst term_eqs =
       case c of 
         Eq (Set A, Set B) => 
           if (A aconv B) 
           then simplify_constraints cs type_subst term_eqs
           else simplify_constraints cs type_subst ((A, B)::term_eqs)           
       | Eq (Set _, Pi _) => error ("Unsatisfiable: " ^ @{make_string} c)
       | Eq (Pi _, Set _) => error ("Unsatisfiable: " ^ @{make_string} c)
       | Eq (Pi (_, _, _, stA, stB), Pi (_, _, _, stA', stB')) =>
           simplify_constraints (Eq (stA, stA') :: Eq (stB, stB') :: cs) type_subst term_eqs
       | Eq (STVar v, st) => 
           if occurs_check v st then error ("Unsatisfiable: " ^ @{make_string} c)
           else simplify_constraints cs ((v, st) :: type_subst) term_eqs
       | Eq (st, STVar v) => simplify_constraints (Eq (STVar v, st) :: cs) type_subst term_eqs


fun infer_type ctxt t = 
  let
    val ictxt = Inference_Context {
        var_types = Soft_Type_Context.Ctxt.get (Context.Proof ctxt),
        constraints = [],
        fresh_idx = 0
      }
    val (sT, Inference_Context {constraints, ...}) = collect_constraints ictxt t
    val (subst, eqs) = simplify_constraints constraints [] []
    val instantiated = Soft_Type.subst_STVars subst sT
    val _ = Output.tracing (@{make_string} (instantiated, eqs))
  in () end 

end

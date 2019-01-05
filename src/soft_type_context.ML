(*  Title:      soft_type_context.ML
    Author:     Alexander Krauss

Context information regarding soft types.

Allows the declaration of soft types for symbols, which are then available for type checking.
Symbols are either free variables (declared in the context) or constants.

Also introduces a command typing, which can add an (atomic) typing judgement to the context.
*)

structure Soft_Type_Context =
struct

  (* Context data. Maps terms to soft types. *)
  structure Ctxt = Generic_Data(
    type T = Soft_Type.soft_type Termtab.table;
    val empty = Termtab.empty;
    val extend = I;
    val merge = Termtab.merge (op =);
  );

  (* Canonical get and put operations *)
  fun put t sty = Ctxt.map (Termtab.update (t, sty));
  fun get ctxt t = Termtab.lookup (Ctxt.get ctxt) t;


  fun add_typing propstr ctxt =
    let
      val prop = Syntax.read_prop (Context.proof_of ctxt) propstr
      val Soft_Type.Judgement (x, T) = Soft_Type.read_judgement prop
    in 
      put x T ctxt
    end; 


  val _ = Theory.setup (Attrib.setup @{binding type} (Scan.lift Parse.prop >>
    (fn propstr => Thm.declaration_attribute (K (add_typing propstr)))) "define a soft type")


end

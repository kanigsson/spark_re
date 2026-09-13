--  Pattern parsing. Produces a syntax tree and, on success, proves that the
--  tree derives the whole pattern in the independent expression grammar
--  declared here. The grammar's definition is deliberately hidden in the
--  body: clients reason with the derivation, never with its unfolding.

generic
package Spark_Re_Trees.Parsing with SPARK_Mode is

   type Grammar_Level is
     (Atom_Grammar, Factor_Grammar, Term_Grammar, Expr_Grammar);

   --  A derivation of an expression span in a supplied tree. The grammar
   --  independently states precedence and grouping, and makes no reference
   --  to parser frames, allocation order beyond Tree_Valid, or scanner calls.
   function Grammar
     (Pattern     : String;
      Nodes       : Tree;
      Id          : Live_Node;
      First, Last : Natural;
      Level       : Grammar_Level) return Boolean
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes) and First <= Last and Last <= Pattern'Length,
     Post               =>
       (if Grammar'Result and Level in Atom_Grammar | Factor_Grammar
        then First < Last),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Last - First, Decreases => Level);

   --  Byte-only syntax acceptance, independent of allocation and Parse.
   function Pattern_Valid (Pattern : String) return Boolean
   with Ghost => Static;

   --  Every complete grammar derivation satisfies the byte-only predicate.
   procedure Lemma_Grammar_Valid
     (Pattern : String; Nodes : Tree; Id : Live_Node)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then Grammar (Pattern, Nodes, Id, 0, Pattern'Length, Expr_Grammar),
     Post  => Pattern_Valid (Pattern);

   procedure Parse
     (Pattern : String;
      Nodes   : out Tree;
      Root    : out Node_Id;
      Status  : out Compile_Status)
   with Global => null, Always_Terminates;
   pragma
     Postcondition
       (Static =>
          Tree_Valid (Nodes)
          and then
            Status in Success | Syntax_Error | Node_Limit | Pattern_Too_Long
          and then (if Pattern_Valid (Pattern) then Status /= Syntax_Error)
          and then
            (if Status = Success
             then
               Root /= 0
               and then
                 Grammar
                   (Pattern, Nodes, Root, 0, Pattern'Length, Expr_Grammar)));

   --  Completeness for an arbitrary supplied derivation. Resource failures
   --  remain explicit; a valid derivation can never produce Syntax_Error.
   procedure Parse_Complete
     (Pattern : String;
      Witness : Tree;
      Id      : Live_Node;
      Nodes   : out Tree;
      Root    : out Node_Id;
      Status  : out Compile_Status)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Witness)
       and then
         Grammar (Pattern, Witness, Id, 0, Pattern'Length, Expr_Grammar),
     Post  =>
       Tree_Valid (Nodes)
       and then Status in Success | Node_Limit | Pattern_Too_Long
       and then
         (if Status = Success
          then
            Root /= 0
            and then
              Grammar (Pattern, Nodes, Root, 0, Pattern'Length, Expr_Grammar));

end Spark_Re_Trees.Parsing;

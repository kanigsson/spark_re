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

   --  Byte-only span denotation. Neither the definition nor its helpers
   --  construct a tree or call Parse, Compile, or the executable scanners.
   function Pattern_Matches
     (Pattern, Text : String; First, Last : Natural) return Boolean
   with Ghost => Static, Pre => First <= Last and Last <= Text'Length;

   procedure Lemma_Grammar_Matches
     (Pattern, Text : String;
      Nodes         : Tree;
      Id            : Live_Node;
      First, Last   : Natural)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then First <= Last
       and then Last <= Text'Length
       and then Grammar (Pattern, Nodes, Id, 0, Pattern'Length, Expr_Grammar),
     Post  =>
       Matches (Nodes, Id, Text, First, Last)
       = Pattern_Matches (Pattern, Text, First, Last);

   --  Any two derivations of the same bytes have the same span semantics.
   procedure Lemma_Derivation_Independent
     (Pattern, Text : String;
      Left, Right   : Tree;
      L, R          : Live_Node;
      First, Last   : Natural)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Left)
       and then Tree_Valid (Right)
       and then First <= Last
       and then Last <= Text'Length
       and then Grammar (Pattern, Left, L, 0, Pattern'Length, Expr_Grammar)
       and then Grammar (Pattern, Right, R, 0, Pattern'Length, Expr_Grammar),
     Post  =>
       Matches (Left, L, Text, First, Last)
       = Matches (Right, R, Text, First, Last);

   function Pattern_Accepts
     (Pattern, Text : String; Whole : Boolean) return Boolean
   is (if Whole
       then Pattern_Matches (Pattern, Text, 0, Text'Length)
       else
         (for some First in 0 .. Text'Length =>
            (for some Last in First .. Text'Length =>
               Pattern_Matches (Pattern, Text, First, Last))))
   with Ghost => Static;

   procedure Lemma_Grammar_Accepts
     (Pattern, Text : String; Nodes : Tree; Id : Live_Node; Whole : Boolean)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then Grammar (Pattern, Nodes, Id, 0, Pattern'Length, Expr_Grammar),
     Post  =>
       Pattern_Accepts (Pattern, Text, Whole)
       = (if Whole
          then Matches (Nodes, Id, Text, 0, Text'Length)
          else
            (for some First in 0 .. Text'Length =>
               (for some Last in First .. Text'Length =>
                  Matches (Nodes, Id, Text, First, Last))));

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

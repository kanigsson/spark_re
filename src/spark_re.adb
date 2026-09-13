with Spark_Re_Trees.Parsing;

package body Spark_Re
  with SPARK_Mode
is
   package Parsing is new Trees.Parsing;
   use Trees;

   function Is_Valid (Self : Program) return Boolean
   is (Matching.Is_Valid (Self.Impl));
   function State_Count (Self : Program) return Natural
   is (Matching.State_Count (Self.Impl));

   function NFA_Accepts
     (Self : Program; Text : String; Whole : Boolean) return Boolean
   is (Matching.NFA_Accepts (Self.Impl, Text, Whole));

   function Search (Self : Program; Text : String) return Boolean
   is (Matching.Search (Self.Impl, Text));
   function Full_Match (Self : Program; Text : String) return Boolean
   is (Matching.Full_Match (Self.Impl, Text));

   function Pattern_Accepts
     (Pattern, Text : String; Whole : Boolean) return Boolean
   is (Parsing.Pattern_Accepts (Pattern, Text, Whole));

   --  The executable entry point and the text-specific proof use this same
   --  parse/compile operation, retaining its tree as a grammar witness. This
   --  is the only place where a parser result and a matcher result meet, and
   --  it joins them through opaque certificates from either side.
   procedure Compile_With_Tree
     (Pattern : String;
      Result  : out Program;
      Status  : out Compile_Status;
      Nodes   : out Tree;
      Root    : out Node_Id)
   with
     Post => (Is_Valid (Result) = (Status = Success)) and Well_Formed (Result)
   is
      pragma
        Postcondition
          (Static =>
             Tree_Valid (Nodes)
             and then
               (if Status = Success
                then
                  Root /= 0
                  and then
                    Parsing.Grammar
                      (Pattern,
                       Nodes,
                       Root,
                       0,
                       Pattern'Length,
                       Parsing.Expr_Grammar)
                  and then Matching.Tree_Compiled (Nodes, Root, Result.Impl)));
   begin
      Result := (Impl => <>);
      Parsing.Parse (Pattern, Nodes, Root, Status);
      if Status = Success then
         Matching.Compile_Tree (Nodes, Root, Result.Impl, Status);
      end if;
   end Compile_With_Tree;

   procedure Compile
     (Pattern : String; Result : out Program; Status : out Compile_Status)
   is
      Nodes : Tree;
      Root  : Node_Id;
   begin
      Compile_With_Tree (Pattern, Result, Status, Nodes, Root);
      pragma
        Assert
          (Static =>
             Tree_Valid (Nodes)
             and then
               (if Status = Success
                then
                  Root /= 0
                  and then
                    Parsing.Grammar
                      (Pattern,
                       Nodes,
                       Root,
                       0,
                       Pattern'Length,
                       Parsing.Expr_Grammar)));
   end Compile;

   --  The composed theorem: for a supplied text, a successfully compiled
   --  pattern matches exactly when its byte-only denotation accepts.
   procedure Compile_Pattern_For_Text
     (Pattern, Text : String;
      Whole         : Boolean;
      Result        : out Program;
      Status        : out Compile_Status;
      Nodes         : out Tree;
      Root          : out Node_Id)
   with
     Ghost => Static,
     Post  =>
       Tree_Valid (Nodes)
       and then Well_Formed (Result)
       and then (Is_Valid (Result) = (Status = Success))
       and then
         (if Status = Success
          then
            Root /= 0
            and then
              Parsing.Grammar
                (Pattern, Nodes, Root, 0, Pattern'Length, Parsing.Expr_Grammar)
            and then
              NFA_Accepts (Result, Text, Whole)
              = Matching.Tree_Accepts (Nodes, Root, Text, Whole)
            and then
              Matching.Tree_Accepts (Nodes, Root, Text, Whole)
              = Pattern_Accepts (Pattern, Text, Whole)
            and then
              (if Whole
               then Full_Match (Result, Text)
               else Search (Result, Text))
              = Matching.Tree_Accepts (Nodes, Root, Text, Whole))
   is
   begin
      Compile_With_Tree (Pattern, Result, Status, Nodes, Root);
      if Status = Success then
         Matching.Lemma_Compiler_Correct
           (Nodes, Root, Result.Impl, Text, Whole);
         Parsing.Lemma_Grammar_Accepts (Pattern, Text, Nodes, Root, Whole);
      end if;
   end Compile_Pattern_For_Text;

   procedure Compile_For_Text
     (Pattern, Text : String;
      Whole         : Boolean;
      Result        : out Program;
      Status        : out Compile_Status)
   is
      Nodes : Tree;
      Root  : Node_Id;
   begin
      Compile_Pattern_For_Text
        (Pattern, Text, Whole, Result, Status, Nodes, Root);
      pragma
        Assert
          (Tree_Valid (Nodes) and then (if Status = Success then Root /= 0));
   end Compile_For_Text;
end Spark_Re;

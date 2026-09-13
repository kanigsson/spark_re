--  The NFA: instruction programs, the Thompson-style tree compiler, and the
--  simulator, together with their proof that a compiled program accepts
--  exactly the language of the tree it was built from. Nothing here mentions
--  pattern syntax; the parser supplies a tree and that is the whole contract.

generic
   Max_States : Positive := 4_096;
package Spark_Re_Trees.Matching with SPARK_Mode is

   --  A default-initialized Program is well formed and rejects every input,
   --  so the facade can hand one back on a compile failure without seeing
   --  the instruction representation.
   type Program is private
   with
     Default_Initial_Condition =>
       Well_Formed (Program) and not Is_Valid (Program);

   function Is_Valid (Self : Program) return Boolean
   with Global => null;
   function State_Count (Self : Program) return Natural
   with Global => null, Post => State_Count'Result <= Max_States;
   --  Every emitted edge stays within the compiled prefix, and successful
   --  programs have a live entry point.
   function Well_Formed (Self : Program) return Boolean
   with Ghost, Global => null;

   --  Declarative semantics of the compiled NFA, including absolute anchors
   --  and restart at every text boundary for search.
   function NFA_Accepts
     (Self : Program; Text : String; Whole : Boolean) return Boolean
   with Ghost => Static, Global => null;

   function Search (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Search'Result);
   pragma
     Postcondition (Static => Search'Result = NFA_Accepts (Self, Text, False));

   function Full_Match (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Full_Match'Result);
   pragma
     Postcondition
       (Static => Full_Match'Result = NFA_Accepts (Self, Text, True));

   --  Certificate that Self is the program Compile_Tree builds for
   --  (Nodes, Root). Its definition is private to the body: a client carries
   --  this certificate from the compiler to the correctness theorem without
   --  ever seeing the instruction layout it describes.
   function Tree_Compiled
     (Nodes : Tree; Root : Live_Node; Self : Program) return Boolean
   with Ghost => Static, Pre => Tree_Valid (Nodes);

   --  The tree's own language: the whole input, or some span of it.
   function Tree_Accepts
     (Nodes : Tree; Root : Live_Node; Text : String; Whole : Boolean)
      return Boolean
   is (if Whole
       then Matches (Nodes, Root, Text, 0, Text'Length)
       else
         (for some First in 0 .. Text'Length =>
            (for some Last in First .. Text'Length =>
               Matches (Nodes, Root, Text, First, Last))))
   with Ghost => Static, Pre => Tree_Valid (Nodes);

   procedure Compile_Tree
     (Nodes  : Tree;
      Root   : Live_Node;
      Result : out Program;
      Status : out Compile_Status)
   with
     Global => null,
     Always_Terminates,
     Post   =>
       Is_Valid (Result) = (Status = Success)
       and Well_Formed (Result)
       and Status in Success | State_Limit | Expansion_Limit;
   pragma Precondition (Static => Tree_Valid (Nodes));
   pragma
     Postcondition
       (Static =>
          (if Status = Success then Tree_Compiled (Nodes, Root, Result)));

   --  Compiler correctness: a compiled program's language is its tree's.
   procedure Lemma_Compiler_Correct
     (Nodes : Tree;
      Root  : Live_Node;
      Self  : Program;
      Text  : String;
      Whole : Boolean)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then Well_Formed (Self)
       and then Is_Valid (Self)
       and then Tree_Compiled (Nodes, Root, Self),
     Post  =>
       NFA_Accepts (Self, Text, Whole)
       = Tree_Accepts (Nodes, Root, Text, Whole)
       and then (if Whole
                 then Full_Match (Self, Text)
                 else Search (Self, Text))
                = Tree_Accepts (Nodes, Root, Text, Whole);

   --  Apply the theorem to the actual compiler for an arbitrary supplied text.
   procedure Compile_Tree_For_Text
     (Nodes  : Tree;
      Root   : Live_Node;
      Text   : String;
      Whole  : Boolean;
      Result : out Program;
      Status : out Compile_Status)
   with
     Ghost => Static,
     Pre   => Tree_Valid (Nodes),
     Post  =>
       Well_Formed (Result)
       and then (Is_Valid (Result) = (Status = Success))
       and then Status in Success | State_Limit | Expansion_Limit
       and then (if Status = Success
                 then
                   (if Whole
                    then Full_Match (Result, Text)
                    else Search (Result, Text))
                   = Tree_Accepts (Nodes, Root, Text, Whole));

private
   subtype State_Id is Natural range 0 .. Max_States;
   subtype Live_State is State_Id range 1 .. Max_States;
   type Opcode is (Dead, Consume, Split, At_Start, At_End, Accept_State);
   type Instruction is record
      Op             : Opcode := Dead;
      Bytes          : Byte_Set := [others => False];
      Next_1, Next_2 : State_Id := 0;
   end record;
   type Code_Array is array (Live_State) of Instruction;
   function Internal_Valid (Self : Program) return Boolean
   with Ghost;
   type Program is record
      Code         : Code_Array;
      Count, Start : State_Id := 0;
      Valid        : Boolean := False;
   end record
   with Type_Invariant => Internal_Valid (Program);
   function Links_Valid (Self : Program) return Boolean
   is (for all Id in 1 .. Self.Count =>
         Self.Code (Id).Next_1 <= Self.Count
         and Self.Code (Id).Next_2 <= Self.Count)
   with Ghost;
   function Internal_Valid (Self : Program) return Boolean
   is (Links_Valid (Self)
       and then (if Self.Valid then Self.Start in 1 .. Self.Count));
   function Well_Formed (Self : Program) return Boolean
   is (Internal_Valid (Self));
end Spark_Re_Trees.Matching;

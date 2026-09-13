--  Syntax trees and their span semantics. This is the shared vocabulary of
--  the parser and the matcher: the parser produces a tree, the matcher
--  compiles one, and neither refers to the other's entities.

with Spark_Re_Common; use Spark_Re_Common;

generic
   Max_Nodes : Positive := 512;
package Spark_Re_Trees with SPARK_Mode is

   subtype Node_Id is Natural range 0 .. Max_Nodes;
   subtype Live_Node is Node_Id range 1 .. Max_Nodes;
   type Node_Kind is
     (Empty_Node,
      Bytes_Node,
      Start_Node,
      End_Node,
      Concat_Node,
      Alt_Node,
      Repeat_Node);
   type Node is record
      Kind        : Node_Kind := Empty_Node;
      Bytes       : Byte_Set := [others => False];
      Left, Right : Node_Id := 0;
      Low, High   : Natural range 0 .. Max_Repetition := 0;
      Unlimited   : Boolean := False;
   end record;
   type Tree is array (Live_Node) of Node;
   function Node_Valid (N : Node; Before : Node_Id) return Boolean
   is (N.Left <= Before
       and then N.Right <= Before
       and then
         (case N.Kind is
            when Concat_Node | Alt_Node => N.Left > 0 and N.Right > 0,
            when Repeat_Node            =>
              N.Left > 0 and (N.Unlimited or N.Low <= N.High),
            when others                 => True))
   with Ghost => Static;

   function Tree_Valid (Nodes : Tree) return Boolean
   is (for all Id in Live_Node => Node_Valid (Nodes (Id), Id - 1))
   with Ghost => Static;

   --  Spans use offsets in the whole input, not Ada array indices.
   function Matches
     (Nodes : Tree; Id : Live_Node; Text : String; First, Last : Natural)
      return Boolean
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes) and First <= Last and Last <= Text'Length,
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(Max_Repetition + 1),
        Decreases => Natural'(Max_Repetition + 1),
        Decreases => Last - First);

   function Repeated_Matches
     (Nodes       : Tree;
      Id          : Live_Node;
      Text        : String;
      First, Last : Natural;
      Low, High   : Natural;
      Unlimited   : Boolean) return Boolean
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and Nodes (Id).Kind = Repeat_Node
       and First <= Last
       and Last <= Text'Length
       and Low <= Max_Repetition
       and High <= Max_Repetition
       and (Unlimited or Low <= High),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Low,
        Decreases => High,
        Decreases => Last - First);

   function Matches
     (Nodes : Tree; Id : Live_Node; Text : String; First, Last : Natural)
      return Boolean
   is (case Nodes (Id).Kind is
         when Empty_Node  => First = Last,
         when Bytes_Node  =>
           First < Last
           and then Last - First = 1
           and then Nodes (Id).Bytes (Text (Text'First + First)),
         when Start_Node  => First = Last and First = 0,
         when End_Node    => First = Last and Last = Text'Length,
         when Concat_Node =>
           (for some Middle in First .. Last =>
              Matches (Nodes, Nodes (Id).Left, Text, First, Middle)
              and then Matches (Nodes, Nodes (Id).Right, Text, Middle, Last)),
         when Alt_Node    =>
           Matches (Nodes, Nodes (Id).Left, Text, First, Last)
           or else Matches (Nodes, Nodes (Id).Right, Text, First, Last),
         when Repeat_Node =>
           Repeated_Matches
             (Nodes,
              Id,
              Text,
              First,
              Last,
              Nodes (Id).Low,
              Nodes (Id).High,
              Nodes (Id).Unlimited));

   --  Mandatory copies may be empty. After the lower bound is met,
   --  unbounded repetition omits empty copies and advances on each copy.
   function Repeated_Matches
     (Nodes       : Tree;
      Id          : Live_Node;
      Text        : String;
      First, Last : Natural;
      Low, High   : Natural;
      Unlimited   : Boolean) return Boolean
   is (if Low > 0
       then
         (for some Middle in First .. Last =>
            Matches (Nodes, Nodes (Id).Left, Text, First, Middle)
            and then
              Repeated_Matches
                (Nodes,
                 Id,
                 Text,
                 Middle,
                 Last,
                 Low - 1,
                 (if Unlimited then High else High - 1),
                 Unlimited))
       elsif First = Last
       then True
       elsif Unlimited
       then
         (for some Middle in First + 1 .. Last =>
            Matches (Nodes, Nodes (Id).Left, Text, First, Middle)
            and then
              Repeated_Matches (Nodes, Id, Text, Middle, Last, 0, High, True))
       elsif High > 0
       then
         (for some Middle in First .. Last =>
            Matches (Nodes, Nodes (Id).Left, Text, First, Middle)
            and then
              Repeated_Matches
                (Nodes, Id, Text, Middle, Last, 0, High - 1, False))
       else False);

   procedure Lemma_Empty_Repetition
     (Nodes     : Tree;
      Id        : Live_Node;
      Text      : String;
      Position  : Natural;
      Low, High : Natural;
      Unlimited : Boolean)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and Nodes (Id).Kind = Repeat_Node
       and Position <= Text'Length
       and Low <= Max_Repetition
       and High <= Max_Repetition
       and (Unlimited or Low <= High),
     Post               =>
       Repeated_Matches
         (Nodes, Id, Text, Position, Position, Low, High, Unlimited)
       = (Low = 0
          or else Matches (Nodes, Nodes (Id).Left, Text, Position, Position)),
     Subprogram_Variant => (Decreases => Low);

   function Nullable
     (Nodes : Tree; Id : Live_Node; At_Start, At_End : Boolean) return Boolean
   is (case Nodes (Id).Kind is
         when Empty_Node  => True,
         when Bytes_Node  => False,
         when Start_Node  => At_Start,
         when End_Node    => At_End,
         when Concat_Node =>
           Nullable (Nodes, Nodes (Id).Left, At_Start, At_End)
           and then Nullable (Nodes, Nodes (Id).Right, At_Start, At_End),
         when Alt_Node    =>
           Nullable (Nodes, Nodes (Id).Left, At_Start, At_End)
           or else Nullable (Nodes, Nodes (Id).Right, At_Start, At_End),
         when Repeat_Node =>
           Nodes (Id).Low = 0
           or else Nullable (Nodes, Nodes (Id).Left, At_Start, At_End))
   with
     Ghost              => Static,
     Pre                => Tree_Valid (Nodes),
     Subprogram_Variant => (Decreases => Id);

   procedure Lemma_Nullable
     (Nodes : Tree; Id : Live_Node; Text : String; Position : Natural)
   with
     Ghost              => Static,
     Pre                => Tree_Valid (Nodes) and Position <= Text'Length,
     Post               =>
       Matches (Nodes, Id, Text, Position, Position)
       = Nullable (Nodes, Id, Position = 0, Position = Text'Length),
     Subprogram_Variant => (Decreases => Id);

end Spark_Re_Trees;

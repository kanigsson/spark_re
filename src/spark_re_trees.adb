package body Spark_Re_Trees
  with SPARK_Mode
is

   procedure Lemma_Empty_Repetition
     (Nodes     : Tree;
      Id        : Live_Node;
      Text      : String;
      Position  : Natural;
      Low, High : Natural;
      Unlimited : Boolean) is
   begin
      if Low > 0 then
         Lemma_Empty_Repetition
           (Nodes,
            Id,
            Text,
            Position,
            Low - 1,
            (if Unlimited then High else High - 1),
            Unlimited);
      end if;
   end Lemma_Empty_Repetition;

   procedure Lemma_Nullable
     (Nodes : Tree; Id : Live_Node; Text : String; Position : Natural)
   is
      N : constant Node := Nodes (Id);
   begin
      case N.Kind is
         when Concat_Node | Alt_Node =>
            Lemma_Nullable (Nodes, N.Left, Text, Position);
            Lemma_Nullable (Nodes, N.Right, Text, Position);

         when Repeat_Node            =>
            Lemma_Nullable (Nodes, N.Left, Text, Position);
            Lemma_Empty_Repetition
              (Nodes, Id, Text, Position, N.Low, N.High, N.Unlimited);

         when others                 =>
            null;
      end case;
   end Lemma_Nullable;

end Spark_Re_Trees;

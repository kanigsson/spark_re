with Ada.Numerics.Big_Numbers.Big_Integers;

package body Spark_Re_Trees.Matching with SPARK_Mode is
   use Ada.Numerics.Big_Numbers.Big_Integers;

   function Closed_Interval
     (Code : Code_Array; Base, Limit, Next : State_Id) return Boolean
   is (for all K in 1 .. Limit =>
         (if K > Base
          then
            Code (K).Op in Consume | Split | At_Start | At_End
            and then
              (Code (K).Next_1 = Next or Code (K).Next_1 in Base + 1 .. Limit)
            and then
              (if Code (K).Op = Split
               then
                 Code (K).Next_2 = Next
                 or Code (K).Next_2 in Base + 1 .. Limit)))
   with Ghost => Static;

   function Fragment_Closed
     (Self : Program; Base, Next : State_Id) return Boolean
   is (for all K in 1 .. Self.Count =>
         (if K > Base
          then
            Self.Code (K).Op in Consume | Split | At_Start | At_End
            and then
              (Self.Code (K).Next_1 = Next
               or Self.Code (K).Next_1 in Base + 1 .. Self.Count)
            and then
              (if Self.Code (K).Op = Split
               then
                 Self.Code (K).Next_2 = Next
                 or Self.Code (K).Next_2 in Base + 1 .. Self.Count)))
   with Ghost => Static;

   --  Mathematical budgets allow compositional path witnesses without an
   --  artificial machine-integer ceiling. All uses are erased static ghost code.
   subtype Path_Steps is Big_Natural;

   function Fragment_Path
     (Code              : Code_Array;
      Entry_State, Stop : State_Id;
      Text              : String;
      First, Last       : Natural;
      Fuel              : Path_Steps) return Boolean
   is (if Entry_State = Stop
       then First = Last
       elsif Entry_State = 0 or else Fuel = 0
       then False
       else
         (case Code (Entry_State).Op is
            when Dead | Accept_State => False,
            when Consume             =>
              First < Last
              and then Code (Entry_State).Bytes (Text (Text'First + First))
              and then
                Fragment_Path
                  (Code,
                   Code (Entry_State).Next_1,
                   Stop,
                   Text,
                   First + 1,
                   Last,
                   Fuel - 1),
            when Split               =>
              Fragment_Path
                (Code,
                 Code (Entry_State).Next_1,
                 Stop,
                 Text,
                 First,
                 Last,
                 Fuel - 1)
              or else
                Fragment_Path
                  (Code,
                   Code (Entry_State).Next_2,
                   Stop,
                   Text,
                   First,
                   Last,
                   Fuel - 1),
            when At_Start            =>
              First = 0
              and then
                Fragment_Path
                  (Code,
                   Code (Entry_State).Next_1,
                   Stop,
                   Text,
                   First,
                   Last,
                   Fuel - 1),
            when At_End              =>
              First = Text'Length
              and then
                Fragment_Path
                  (Code,
                   Code (Entry_State).Next_1,
                   Stop,
                   Text,
                   First,
                   Last,
                   Fuel - 1)))
   with
     Ghost              => Static,
     Pre                => First <= Last and Last <= Text'Length,
     Subprogram_Variant => (Decreases => Fuel);

   procedure Lemma_Path_Monotone
     (Code              : Code_Array;
      Entry_State, Stop : State_Id;
      Text              : String;
      First, Last       : Natural;
      Small, Large      : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       First <= Last and Last <= Text'Length and Small <= Large,
     Post               =>
       (if Fragment_Path (Code, Entry_State, Stop, Text, First, Last, Small)
        then
          Fragment_Path (Code, Entry_State, Stop, Text, First, Last, Large)),
     Subprogram_Variant => (Decreases => Small)
   is
   begin
      if Entry_State /= Stop and Entry_State /= 0 and Small > 0 then
         case Code (Entry_State).Op is
            when Consume             =>
               if First < Last then
                  Lemma_Path_Monotone
                    (Code,
                     Code (Entry_State).Next_1,
                     Stop,
                     Text,
                     First + 1,
                     Last,
                     Small - 1,
                     Large - 1);
               end if;

            when Split               =>
               Lemma_Path_Monotone
                 (Code,
                  Code (Entry_State).Next_1,
                  Stop,
                  Text,
                  First,
                  Last,
                  Small - 1,
                  Large - 1);
               Lemma_Path_Monotone
                 (Code,
                  Code (Entry_State).Next_2,
                  Stop,
                  Text,
                  First,
                  Last,
                  Small - 1,
                  Large - 1);

            when At_Start | At_End   =>
               Lemma_Path_Monotone
                 (Code,
                  Code (Entry_State).Next_1,
                  Stop,
                  Text,
                  First,
                  Last,
                  Small - 1,
                  Large - 1);

            when Dead | Accept_State =>
               null;
         end case;
      end if;
   end Lemma_Path_Monotone;

   procedure Lemma_Path_Frame
     (Before, After           : Program;
      Base, Entry_State, Stop : State_Id;
      Text                    : String;
      First, Last             : Natural;
      Fuel                    : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       First <= Last
       and Last <= Text'Length
       and Stop <= Base
       and Base <= Before.Count
       and
         (Entry_State = Stop
          or (Entry_State > Base and Entry_State <= Before.Count))
       and Fragment_Closed (Before, Base, Stop)
       and
         (for all K in 1 .. Before.Count =>
            (if K > Base then Before.Code (K) = After.Code (K))),
     Post               =>
       Fragment_Path (Before.Code, Entry_State, Stop, Text, First, Last, Fuel)
       = Fragment_Path
           (After.Code, Entry_State, Stop, Text, First, Last, Fuel),
     Subprogram_Variant => (Decreases => Fuel)
   is
   begin
      if Entry_State /= Stop and Fuel > 0 then
         case Before.Code (Entry_State).Op is
            when Consume             =>
               if First < Last then
                  Lemma_Path_Frame
                    (Before,
                     After,
                     Base,
                     Before.Code (Entry_State).Next_1,
                     Stop,
                     Text,
                     First + 1,
                     Last,
                     Fuel - 1);
               end if;

            when Split               =>
               Lemma_Path_Frame
                 (Before,
                  After,
                  Base,
                  Before.Code (Entry_State).Next_1,
                  Stop,
                  Text,
                  First,
                  Last,
                  Fuel - 1);
               Lemma_Path_Frame
                 (Before,
                  After,
                  Base,
                  Before.Code (Entry_State).Next_2,
                  Stop,
                  Text,
                  First,
                  Last,
                  Fuel - 1);

            when At_Start | At_End   =>
               Lemma_Path_Frame
                 (Before,
                  After,
                  Base,
                  Before.Code (Entry_State).Next_1,
                  Stop,
                  Text,
                  First,
                  Last,
                  Fuel - 1);

            when Dead | Accept_State =>
               null;
         end case;
      end if;
   end Lemma_Path_Frame;

   procedure Lemma_Path_Compose
     (Code                            : Code_Array;
      Limit                           : State_Id;
      Base, Entry_State, Middle, Stop : State_Id;
      Text                            : String;
      First, Cut, Last                : Natural;
      Left_Fuel, Right_Fuel           : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       First <= Cut
       and then Cut <= Last
       and then Last <= Text'Length
       and then Middle <= Base
       and then Stop <= Base
       and then Base <= Limit
       and then
         (Entry_State = Middle
          or (Entry_State > Base and then Entry_State <= Limit))
       and then Closed_Interval (Code, Base, Limit, Middle)
       and then
         Fragment_Path (Code, Entry_State, Middle, Text, First, Cut, Left_Fuel)
       and then
         Fragment_Path (Code, Middle, Stop, Text, Cut, Last, Right_Fuel),
     Post               =>
       Fragment_Path
         (Code, Entry_State, Stop, Text, First, Last, Left_Fuel + Right_Fuel),
     Subprogram_Variant => (Decreases => Left_Fuel)
   is
   begin
      if Entry_State = Middle then
         Lemma_Path_Monotone
           (Code,
            Middle,
            Stop,
            Text,
            Cut,
            Last,
            Right_Fuel,
            Left_Fuel + Right_Fuel);
      else
         case Code (Entry_State).Op is
            when Consume             =>
               Lemma_Path_Compose
                 (Code,
                  Limit,
                  Base,
                  Code (Entry_State).Next_1,
                  Middle,
                  Stop,
                  Text,
                  First + 1,
                  Cut,
                  Last,
                  Left_Fuel - 1,
                  Right_Fuel);

            when Split               =>
               if Fragment_Path
                    (Code,
                     Code (Entry_State).Next_1,
                     Middle,
                     Text,
                     First,
                     Cut,
                     Left_Fuel - 1)
               then
                  Lemma_Path_Compose
                    (Code,
                     Limit,
                     Base,
                     Code (Entry_State).Next_1,
                     Middle,
                     Stop,
                     Text,
                     First,
                     Cut,
                     Last,
                     Left_Fuel - 1,
                     Right_Fuel);
               else
                  Lemma_Path_Compose
                    (Code,
                     Limit,
                     Base,
                     Code (Entry_State).Next_2,
                     Middle,
                     Stop,
                     Text,
                     First,
                     Cut,
                     Last,
                     Left_Fuel - 1,
                     Right_Fuel);
               end if;

            when At_Start | At_End   =>
               Lemma_Path_Compose
                 (Code,
                  Limit,
                  Base,
                  Code (Entry_State).Next_1,
                  Middle,
                  Stop,
                  Text,
                  First,
                  Cut,
                  Last,
                  Left_Fuel - 1,
                  Right_Fuel);

            when Dead | Accept_State =>
               null;
         end case;
      end if;
   end Lemma_Path_Compose;

   procedure Lemma_Path_Decompose
     (Code                            : Code_Array;
      Limit                           : State_Id;
      Base, Entry_State, Middle, Stop : State_Id;
      Text                            : String;
      First, Last                     : Natural;
      Fuel                            : Path_Steps;
      Cut                             : out Natural;
      Left_Fuel                       : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       First <= Last
       and then Last <= Text'Length
       and then Middle <= Base
       and then Stop <= Base
       and then Base <= Limit
       and then
         (Entry_State = Middle
          or (Entry_State > Base and then Entry_State <= Limit))
       and then Closed_Interval (Code, Base, Limit, Middle)
       and then
         Fragment_Path (Code, Entry_State, Stop, Text, First, Last, Fuel),
     Post               =>
       Cut in First .. Last
       and then Left_Fuel <= Fuel
       and then
         Fragment_Path (Code, Entry_State, Middle, Text, First, Cut, Left_Fuel)
       and then
         Fragment_Path (Code, Middle, Stop, Text, Cut, Last, Fuel - Left_Fuel),
     Subprogram_Variant => (Decreases => Fuel)
   is
   begin
      if Entry_State = Middle then
         Cut := First;
         Left_Fuel := 0;
      else
         case Code (Entry_State).Op is
            when Consume             =>
               Lemma_Path_Decompose
                 (Code,
                  Limit,
                  Base,
                  Code (Entry_State).Next_1,
                  Middle,
                  Stop,
                  Text,
                  First + 1,
                  Last,
                  Fuel - 1,
                  Cut,
                  Left_Fuel);

            when Split               =>
               if Fragment_Path
                    (Code,
                     Code (Entry_State).Next_1,
                     Stop,
                     Text,
                     First,
                     Last,
                     Fuel - 1)
               then
                  Lemma_Path_Decompose
                    (Code,
                     Limit,
                     Base,
                     Code (Entry_State).Next_1,
                     Middle,
                     Stop,
                     Text,
                     First,
                     Last,
                     Fuel - 1,
                     Cut,
                     Left_Fuel);
               else
                  Lemma_Path_Decompose
                    (Code,
                     Limit,
                     Base,
                     Code (Entry_State).Next_2,
                     Middle,
                     Stop,
                     Text,
                     First,
                     Last,
                     Fuel - 1,
                     Cut,
                     Left_Fuel);
               end if;

            when At_Start | At_End   =>
               Lemma_Path_Decompose
                 (Code,
                  Limit,
                  Base,
                  Code (Entry_State).Next_1,
                  Middle,
                  Stop,
                  Text,
                  First,
                  Last,
                  Fuel - 1,
                  Cut,
                  Left_Fuel);

            when Dead | Accept_State =>
               Cut := First;
               Left_Fuel := 0;
         end case;
         Left_Fuel := Left_Fuel + 1;
      end if;
   end Lemma_Path_Decompose;

   function Leaf_Compiled
     (N : Node; Self : Program; Base, Next, Entry_State : State_Id)
      return Boolean
   is (Next <= Base
       and then
         (case N.Kind is
            when Empty_Node                         => Entry_State = Next,
            when Bytes_Node | Start_Node | End_Node =>
              Entry_State > Base
              and then Entry_State <= Self.Count
              and then Self.Code (Entry_State).Next_1 = Next
              and then
                (case N.Kind is
                   when Bytes_Node =>
                     Self.Code (Entry_State).Op = Consume
                     and Self.Code (Entry_State).Bytes = N.Bytes,
                   when Start_Node => Self.Code (Entry_State).Op = At_Start,
                   when End_Node   => Self.Code (Entry_State).Op = At_End,
                   when others     => False),
            when others                             => False))
   with Ghost => Static;

   procedure Lemma_Leaf_Path
     (Nodes                   : Tree;
      Id                      : Live_Node;
      Self                    : Program;
      Base, Next, Entry_State : State_Id;
      Text                    : String;
      First, Last             : Natural;
      Fuel                    : Path_Steps)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and First <= Last
       and Last <= Text'Length
       and Fuel > 0
       and Leaf_Compiled (Nodes (Id), Self, Base, Next, Entry_State),
     Post  =>
       Matches (Nodes, Id, Text, First, Last)
       = Fragment_Path (Self.Code, Entry_State, Next, Text, First, Last, Fuel)
   is
   begin
      null;
   end Lemma_Leaf_Path;

   --  Structural compilation certificates inspect only their own code
   --  interval. Existential boundaries retain the witnesses needed to compose
   --  child languages without defining semantics by calling the compiler.
   function Compiled_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id) return Boolean
   with Ghost => Static, Pre => Tree_Valid (Nodes),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0));

   function Copies_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural) return Boolean
   with Ghost => Static, Pre => Tree_Valid (Nodes),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count);

   function Optional_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural) return Boolean
   with Ghost => Static, Pre => Tree_Valid (Nodes),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count);

   function Tail_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural; Unlimited : Boolean) return Boolean
   with Ghost => Static, Pre => Tree_Valid (Nodes),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(2), Decreases => Count);

   function Compiled_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id) return Boolean
   is (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then
         (case Nodes (Id).Kind is
            when Empty_Node => Base = Limit and Entry_State = Next,
            when Bytes_Node | Start_Node | End_Node =>
              Base < Limit and then Limit = Base + 1 and then Entry_State = Limit
              and then Code (Limit).Next_1 = Next
              and then
                (case Nodes (Id).Kind is
                   when Bytes_Node => Code (Limit).Op = Consume
                     and Code (Limit).Bytes = Nodes (Id).Bytes,
                   when Start_Node => Code (Limit).Op = At_Start,
                   when End_Node => Code (Limit).Op = At_End,
                   when others => False),
            when Concat_Node =>
              (for some Cut in Base .. Limit =>
                 (for some Middle in 0 .. Cut =>
                    Compiled_Shape
                      (Nodes, Nodes (Id).Right, Code, Base, Cut, Next, Middle)
                    and then Compiled_Shape
                      (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State))),
            when Alt_Node =>
              Base < Limit and then Entry_State = Limit
              and then Code (Limit).Op = Split
              and then (for some Cut in Base .. Limit - 1 =>
                Compiled_Shape
                  (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, Code (Limit).Next_1)
                and then Compiled_Shape
                  (Nodes, Nodes (Id).Right, Code, Cut, Limit - 1, Next, Code (Limit).Next_2)),
            when Repeat_Node =>
              (for some Cut in Base .. Limit =>
                 (for some Middle in 0 .. Cut =>
                    Tail_Shape
                      (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, Middle,
                       (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low),
                       Nodes (Id).Unlimited)
                    and then Copies_Shape
                      (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State,
                       Nodes (Id).Low)))));

   function Copies_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural) return Boolean
   is (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then (if Count = 0 then Base = Limit and Entry_State = Next
       else (for some Cut in Base .. Limit =>
         (for some Middle in 0 .. Cut =>
            Copies_Shape (Nodes, Id, Code, Base, Cut, Next, Middle, Count - 1)
            and then Compiled_Shape (Nodes, Id, Code, Cut, Limit, Middle, Entry_State)))));

   function Optional_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural) return Boolean
   is (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then (if Count = 0 then Base = Limit and Entry_State = Next
       else Base < Limit and then Entry_State = Limit and then Code (Limit).Op = Split
         and then (for some Cut in Base .. Limit - 1 =>
            Optional_Shape
              (Nodes, Id, Code, Base, Cut, Next, Code (Limit).Next_2, Count - 1)
            and then Compiled_Shape
              (Nodes, Id, Code, Cut, Limit - 1, Code (Limit).Next_2, Code (Limit).Next_1))));

   function Tail_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural; Unlimited : Boolean)
      return Boolean
   is (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then (if Unlimited then
         Base < Limit and then Entry_State = Base + 1
         and then Code (Entry_State).Op = Split and then Code (Entry_State).Next_2 = Next
         and then Compiled_Shape
           (Nodes, Id, Code, Entry_State, Limit, Entry_State, Code (Entry_State).Next_1)
       else Optional_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count)));

   procedure Reveal_Shape
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Compiled_Shape
       (Nodes, Id, Code, Base, Limit, Next, Entry_State),
     Post => (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then
         (case Nodes (Id).Kind is
            when Empty_Node => Base = Limit and Entry_State = Next,
            when Bytes_Node | Start_Node | End_Node =>
              Base < Limit and then Limit = Base + 1 and then Entry_State = Limit
              and then Code (Limit).Next_1 = Next
              and then
                (case Nodes (Id).Kind is
                   when Bytes_Node => Code (Limit).Op = Consume
                     and Code (Limit).Bytes = Nodes (Id).Bytes,
                   when Start_Node => Code (Limit).Op = At_Start,
                   when End_Node => Code (Limit).Op = At_End,
                   when others => False),
            when Concat_Node =>
              (for some Cut in Base .. Limit =>
                 (for some Middle in 0 .. Cut =>
                    Compiled_Shape
                      (Nodes, Nodes (Id).Right, Code, Base, Cut, Next, Middle)
                    and then Compiled_Shape
                      (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State))),
            when Alt_Node =>
              Base < Limit and then Entry_State = Limit
              and then Code (Limit).Op = Split
              and then (for some Cut in Base .. Limit - 1 =>
                Compiled_Shape
                  (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, Code (Limit).Next_1)
                and then Compiled_Shape
                  (Nodes, Nodes (Id).Right, Code, Cut, Limit - 1, Next, Code (Limit).Next_2)),
            when Repeat_Node =>
              (for some Cut in Base .. Limit =>
                 (for some Middle in 0 .. Cut =>
                    Tail_Shape
                      (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, Middle,
                       (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low),
                       Nodes (Id).Unlimited)
                    and then Copies_Shape
                      (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State,
                       Nodes (Id).Low)))))
   is
   begin
      null;
   end Reveal_Shape;

   procedure Reveal_Copies
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Copies_Shape
       (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count),
     Post => (Base <= Limit and then Next <= Base and then Entry_State <= Limit
       and then (if Count = 0 then Base = Limit and Entry_State = Next
       else (for some Cut in Base .. Limit =>
         (for some Middle in 0 .. Cut =>
            Copies_Shape (Nodes, Id, Code, Base, Cut, Next, Middle, Count - 1)
            and then Compiled_Shape (Nodes, Id, Code, Cut, Limit, Middle, Entry_State)))))
   is
   begin
      null;
   end Reveal_Copies;

   procedure Lemma_Shape_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K))),
     Post => Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State) = Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0),
        Decreases => Natural'(2));

   procedure Lemma_Copies_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K))),
     Post => Copies_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count) = Copies_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count,
        Decreases => Natural'(2));

   procedure Lemma_Optional_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K))),
     Post => Optional_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count) = Optional_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count,
        Decreases => Natural'(2));

   procedure Lemma_Tail_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural; Unlimited : Boolean)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K))),
     Post => Tail_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count, Unlimited) = Tail_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count, Unlimited),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(2), Decreases => Count,
        Decreases => Natural'(2));

   procedure Lemma_Shape_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State),
     Post => Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0),
        Decreases => Natural'(1));

   procedure Lemma_Copies_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Copies_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count),
     Post => Copies_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count,
        Decreases => Natural'(1));

   procedure Lemma_Optional_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Optional_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count),
     Post => Optional_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count,
        Decreases => Natural'(1));

   procedure Lemma_Tail_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural; Unlimited : Boolean)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Tail_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count, Unlimited),
     Post => Tail_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count, Unlimited),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(2), Decreases => Count,
        Decreases => Natural'(1));

   procedure Lemma_Copies_Join
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Cut, Limit, Next, Middle, Entry_State : State_Id; Count : Positive)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Cut and then Cut <= Limit
       and then Next <= Base and then Middle <= Cut and then Entry_State <= Limit
       and then Copies_Shape (Nodes, Id, Code, Base, Cut, Next, Middle, Count - 1)
       and then Compiled_Shape (Nodes, Id, Code, Cut, Limit, Middle, Entry_State),
     Post => Copies_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count)
   is
   begin
      pragma Assert (for some M in 0 .. Cut =>
        Copies_Shape (Nodes, Id, Code, Base, Cut, Next, M, Count - 1)
        and then Compiled_Shape (Nodes, Id, Code, Cut, Limit, M, Entry_State));
      pragma Assert_And_Cut
        (Tree_Valid (Nodes) and then Base <= Limit and then Next <= Base
         and then Entry_State <= Limit and then Count > 0
         and then (for some C in Base .. Limit =>
           (for some M in 0 .. C =>
              Copies_Shape (Nodes, Id, Code, Base, C, Next, M, Count - 1)
              and then Compiled_Shape (Nodes, Id, Code, C, Limit, M, Entry_State))));
   end Lemma_Copies_Join;

   procedure Lemma_Concat_Join
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Cut, Limit, Next, Middle, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Nodes (Id).Kind = Concat_Node
       and then Base <= Cut and then Cut <= Limit
       and then Next <= Base and then Middle <= Cut and then Entry_State <= Limit
       and then Compiled_Shape
         (Nodes, Nodes (Id).Right, Code, Base, Cut, Next, Middle)
       and then Compiled_Shape
         (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State),
     Post => Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State)
   is
   begin
      pragma Assert (for some M in 0 .. Cut =>
        Compiled_Shape (Nodes, Nodes (Id).Right, Code, Base, Cut, Next, M)
        and then Compiled_Shape (Nodes, Nodes (Id).Left, Code, Cut, Limit, M, Entry_State));
   end Lemma_Concat_Join;

   procedure Lemma_Repeat_Join
     (Nodes : Tree; Id : Live_Node; Code : Code_Array;
      Base, Cut, Limit, Next, Middle, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Nodes (Id).Kind = Repeat_Node
       and then Base <= Cut and then Cut <= Limit
       and then Next <= Base and then Middle <= Cut and then Entry_State <= Limit
       and then Tail_Shape
         (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, Middle,
          (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited)
       and then Copies_Shape
         (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State, Nodes (Id).Low),
     Post => Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State)
   is
      --  The child certificates are only carried into the repetition case,
      --  never inspected, so their definitions are pruned here.
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Tail_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Copies_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Optional_Shape);
   begin
      pragma Assert (for some M in 0 .. Cut =>
        Tail_Shape
          (Nodes, Nodes (Id).Left, Code, Base, Cut, Next, M,
           (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited)
        and then Copies_Shape
          (Nodes, Nodes (Id).Left, Code, Cut, Limit, M, Entry_State, Nodes (Id).Low));
      --  Witness the outer cut with Cut, so that folding into the repetition
      --  certificate is a single instantiation rather than a search.
      pragma Assert
        (for some C in Base .. Limit =>
           (for some M in 0 .. C =>
              Tail_Shape
                (Nodes, Nodes (Id).Left, Code, Base, C, Next, M,
                 (if Nodes (Id).Unlimited then 0
                  else Nodes (Id).High - Nodes (Id).Low),
                 Nodes (Id).Unlimited)
              and then Copies_Shape
                (Nodes, Nodes (Id).Left, Code, C, Limit, M, Entry_State,
                 Nodes (Id).Low)));
   end Lemma_Repeat_Join;

   --  Concatenation and repetition preservation are split out so that each
   --  can prune the shape definitions it only carries. The leaf and
   --  alternation cases below still need them unfolded, and information
   --  hiding is decided per verified entity, not per branch.
   procedure Lemma_Concat_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then Nodes (Id).Kind = Concat_Node
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State),
     Post => Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0),
        Decreases => Natural'(0))
   is
      --  This search reasons only about the certificates' quantifier structure:
      --  the witness comes from Reveal_Shape's postcondition and is consumed
      --  by the frame and join lemmas' contracts. Pruning the recursive
      --  definition keeps the nested existential from being re-instantiated
      --  under the enclosing universal invariant.
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Compiled_Shape);
   begin
      Reveal_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State);
         for Cut in Base .. Limit loop
            if (for some M in 0 .. Cut => Compiled_Shape (Nodes, Nodes (Id).Right, Before, Base, Cut, Next, M) and then Compiled_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, M, Entry_State)) then
            for Middle in 0 .. Cut loop
               if Compiled_Shape (Nodes, Nodes (Id).Right, Before, Base, Cut, Next, Middle) and then Compiled_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, Middle, Entry_State) then
                  Lemma_Shape_Frame (Nodes, Nodes (Id).Right, Before, After, Base, Cut, Next, Middle);
                  Lemma_Shape_Frame (Nodes, Nodes (Id).Left, Before, After, Cut, Limit, Middle, Entry_State);
                  Lemma_Concat_Join (Nodes, Id, After, Base, Cut, Limit, Next, Middle, Entry_State);
                  return;
               end if;
               pragma Loop_Invariant (for all M in 0 .. Middle => not (Compiled_Shape (Nodes, Nodes (Id).Right, Before, Base, Cut, Next, M) and then Compiled_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, M, Entry_State)));
            end loop;
            pragma Assert (False);
            end if;
            pragma Loop_Invariant (for some C in Base .. Limit => (for some M in 0 .. C => Compiled_Shape (Nodes, Nodes (Id).Right, Before, Base, C, Next, M) and then Compiled_Shape (Nodes, Nodes (Id).Left, Before, C, Limit, M, Entry_State)));
            --  Keep the negated witness in the same form as the guard.
            --  Each visited cut has no middle state joining the children.
            pragma Loop_Invariant
              (for all C in Base .. Cut =>
                 not (for some M in 0 .. C =>
                   Compiled_Shape
                     (Nodes, Nodes (Id).Right, Before, Base, C, Next, M)
                   and then Compiled_Shape
                     (Nodes, Nodes (Id).Left, Before, C, Limit, M, Entry_State)));
         end loop;
         pragma Assert (False);
   end Lemma_Concat_Preserve;

   procedure Lemma_Repeat_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then Nodes (Id).Kind = Repeat_Node
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State),
     Post => Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0),
        Decreases => Natural'(0))
   is
      --  As for concatenation: the repetition certificates are carried, never
      --  unfolded, so their definitions are pruned here.
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Compiled_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Copies_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Optional_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Tail_Shape);
   begin
      Reveal_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State);
         for Cut in Base .. Limit loop
            if (for some M in 0 .. Cut => Tail_Shape (Nodes, Nodes (Id).Left, Before, Base, Cut, Next, M, (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited) and then Copies_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, M, Entry_State, Nodes (Id).Low)) then
            for Middle in 0 .. Cut loop
               if Tail_Shape (Nodes, Nodes (Id).Left, Before, Base, Cut, Next, Middle, (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited) and then Copies_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, Middle, Entry_State, Nodes (Id).Low) then
                  Lemma_Tail_Frame (Nodes, Nodes (Id).Left, Before, After, Base, Cut, Next, Middle, (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited);
                  Lemma_Copies_Frame (Nodes, Nodes (Id).Left, Before, After, Cut, Limit, Middle, Entry_State, Nodes (Id).Low);
                  Lemma_Repeat_Join (Nodes, Id, After, Base, Cut, Limit, Next, Middle, Entry_State);
                  return;
               end if;
               pragma Loop_Invariant (for all M in 0 .. Middle => not (Tail_Shape (Nodes, Nodes (Id).Left, Before, Base, Cut, Next, M, (if Nodes (Id).Unlimited then 0 else Nodes (Id).High - Nodes (Id).Low), Nodes (Id).Unlimited) and then Copies_Shape (Nodes, Nodes (Id).Left, Before, Cut, Limit, M, Entry_State, Nodes (Id).Low)));
            end loop;
            pragma Assert (False);
            end if;
            pragma Loop_Invariant
              (for all C in Base .. Cut =>
                 not (for some M in 0 .. C =>
                   Tail_Shape
                     (Nodes, Nodes (Id).Left, Before, Base, C, Next, M,
                      (if Nodes (Id).Unlimited then 0
                       else Nodes (Id).High - Nodes (Id).Low),
                      Nodes (Id).Unlimited)
                   and then Copies_Shape
                     (Nodes, Nodes (Id).Left, Before, C, Limit, M,
                      Entry_State, Nodes (Id).Low)));
         end loop;
         pragma Assert (False);
   end Lemma_Repeat_Preserve;

   --  Alternation is split out for symmetry with the other compound cases:
   --  Lemma_Shape_Preserve is then a plain dispatch whose postcondition is
   --  each callee's, or a leaf certificate that depends only on the preserved
   --  instruction at Limit.
   procedure Lemma_Alt_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with Ghost => Static,
     Pre => Tree_Valid (Nodes) and then Base <= Limit
       and then Nodes (Id).Kind = Alt_Node
       and then (for all K in 1 .. Limit => (if K > Base then Before (K) = After (K)))
       and then Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State),
     Post => Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0),
        Decreases => Natural'(0))
   is
   begin
      Reveal_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State);
            for Cut in Base .. Limit - 1 loop
               if Compiled_Shape
                 (Nodes, Nodes (Id).Left, Before, Base, Cut, Next, Before (Limit).Next_1)
                 and then Compiled_Shape
                 (Nodes, Nodes (Id).Right, Before, Cut, Limit - 1, Next, Before (Limit).Next_2)
               then
                  Lemma_Shape_Frame
                    (Nodes, Nodes (Id).Left, Before, After, Base, Cut, Next, Before (Limit).Next_1);
                  Lemma_Shape_Frame
                    (Nodes, Nodes (Id).Right, Before, After, Cut, Limit - 1, Next, Before (Limit).Next_2);
                  return;
               end if;
               pragma Loop_Invariant (for all C in Base .. Cut => not
                 (Compiled_Shape
                    (Nodes, Nodes (Id).Left, Before, Base, C, Next, Before (Limit).Next_1)
                  and then Compiled_Shape
                    (Nodes, Nodes (Id).Right, Before, C, Limit - 1, Next, Before (Limit).Next_2)));
            end loop;
            pragma Assert (False);
   end Lemma_Alt_Preserve;

   procedure Lemma_Shape_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   is
   begin
      Reveal_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State);
      case Nodes (Id).Kind is
         when Empty_Node | Bytes_Node | Start_Node | End_Node => null;
         when Concat_Node =>
            Lemma_Concat_Preserve
              (Nodes, Id, Before, After, Base, Limit, Next, Entry_State);

         when Alt_Node =>
            Lemma_Alt_Preserve
              (Nodes, Id, Before, After, Base, Limit, Next, Entry_State);
         when Repeat_Node =>
            Lemma_Repeat_Preserve
              (Nodes, Id, Before, After, Base, Limit, Next, Entry_State);

      end case;
   end Lemma_Shape_Preserve;

   procedure Lemma_Copies_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   is
   begin
      Reveal_Copies (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count);
      if Count > 0 then
         for Cut in Base .. Limit loop
            if (for some M in 0 .. Cut => Copies_Shape (Nodes, Id, Before, Base, Cut, Next, M, Count - 1) and then Compiled_Shape (Nodes, Id, Before, Cut, Limit, M, Entry_State)) then
            for Middle in 0 .. Cut loop
               if Copies_Shape (Nodes, Id, Before, Base, Cut, Next, Middle, Count - 1) and then Compiled_Shape (Nodes, Id, Before, Cut, Limit, Middle, Entry_State) then
                  Lemma_Copies_Frame (Nodes, Id, Before, After, Base, Cut, Next, Middle, Count - 1);
                  Lemma_Shape_Frame (Nodes, Id, Before, After, Cut, Limit, Middle, Entry_State);
                  Lemma_Copies_Join (Nodes, Id, After, Base, Cut, Limit, Next, Middle, Entry_State, Count);
                  return;
               end if;
               pragma Loop_Invariant (for all M in 0 .. Middle => not (Copies_Shape (Nodes, Id, Before, Base, Cut, Next, M, Count - 1) and then Compiled_Shape (Nodes, Id, Before, Cut, Limit, M, Entry_State)));
            end loop;
            pragma Assert (False);
            end if;
            pragma Loop_Invariant (for some C in Base .. Limit => (for some M in 0 .. C => Copies_Shape (Nodes, Id, Before, Base, C, Next, M, Count - 1) and then Compiled_Shape (Nodes, Id, Before, C, Limit, M, Entry_State)));
            pragma Loop_Invariant
              (for all C in Base .. Cut =>
                 not (for some M in 0 .. C =>
                   Copies_Shape
                     (Nodes, Id, Before, Base, C, Next, M, Count - 1)
                   and then Compiled_Shape
                     (Nodes, Id, Before, C, Limit, M, Entry_State)));
         end loop;
         pragma Assert (False);

      end if;
   end Lemma_Copies_Preserve;

   procedure Lemma_Optional_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   is
   begin
      if Count > 0 then
         for Cut in Base .. Limit - 1 loop
            if Optional_Shape
              (Nodes, Id, Before, Base, Cut, Next, Before (Limit).Next_2, Count - 1)
              and then Compiled_Shape
              (Nodes, Id, Before, Cut, Limit - 1, Before (Limit).Next_2, Before (Limit).Next_1)
            then
               Lemma_Optional_Frame
                 (Nodes, Id, Before, After, Base, Cut, Next, Before (Limit).Next_2, Count - 1);
               Lemma_Shape_Frame
                 (Nodes, Id, Before, After, Cut, Limit - 1, Before (Limit).Next_2, Before (Limit).Next_1);
               return;
            end if;
            pragma Loop_Invariant (for all C in Base .. Cut => not
              (Optional_Shape
                 (Nodes, Id, Before, Base, C, Next, Before (Limit).Next_2, Count - 1)
               and then Compiled_Shape
                 (Nodes, Id, Before, C, Limit - 1, Before (Limit).Next_2, Before (Limit).Next_1)));
         end loop;
         pragma Assert (False);
      end if;
   end Lemma_Optional_Preserve;

   procedure Lemma_Tail_Preserve
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural; Unlimited : Boolean)
   is
   begin
      if Unlimited then
         Lemma_Shape_Frame
           (Nodes, Id, Before, After, Entry_State, Limit, Entry_State, Before (Entry_State).Next_1);
      else
         Lemma_Optional_Frame
           (Nodes, Id, Before, After, Base, Limit, Next, Entry_State, Count);
      end if;
   end Lemma_Tail_Preserve;

   procedure Lemma_Shape_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   is
   begin
      if Compiled_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State) then
         Lemma_Shape_Preserve (Nodes, Id, Before, After, Base, Limit, Next, Entry_State);
      elsif Compiled_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State) then
         Lemma_Shape_Preserve (Nodes, Id, After, Before, Base, Limit, Next, Entry_State);
      end if;
   end Lemma_Shape_Frame;

   procedure Lemma_Copies_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   is
   begin
      if Copies_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count) then
         Lemma_Copies_Preserve (Nodes, Id, Before, After, Base, Limit, Next, Entry_State, Count);
      elsif Copies_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count) then
         Lemma_Copies_Preserve (Nodes, Id, After, Before, Base, Limit, Next, Entry_State, Count);
      end if;
   end Lemma_Copies_Frame;

   procedure Lemma_Optional_Frame
     (Nodes : Tree; Id : Live_Node; Before, After : Code_Array;
      Base, Limit, Next, Entry_State : State_Id; Count : Natural)
   is
   begin
      if Optional_Shape (Nodes, Id, Before, Base, Limit, Next, Entry_State, Count) then
         Lemma_Optional_Preserve (Nodes, Id, Before, After, Base, Limit, Next, Entry_State, Count);
      elsif Optional_Shape (Nodes, Id, After, Base, Limit, Next, Entry_State, Count) then
         Lemma_Optional_Preserve (Nodes, Id, After, Before, Base, Limit, Next, Entry_State, Count);
      end if;
   end Lemma_Optional_Frame;

   procedure Lemma_Tail_Frame
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Before, After                  : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural;
      Unlimited                      : Boolean) is
   begin
      if Tail_Shape
           (Nodes,
            Id,
            Before,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Unlimited)
      then
         Lemma_Tail_Preserve
           (Nodes,
            Id,
            Before,
            After,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Unlimited);
      elsif Tail_Shape
              (Nodes,
               Id,
               After,
               Base,
               Limit,
               Next,
               Entry_State,
               Count,
               Unlimited)
      then
         Lemma_Tail_Preserve
           (Nodes,
            Id,
            After,
            Before,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Unlimited);
      end if;
   end Lemma_Tail_Frame;

   --  Extract construction witnesses once, before reasoning about paths.
   procedure Shape_Parts
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Cut, Middle                    : out State_Id)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind in Concat_Node | Alt_Node | Repeat_Node
       and then
         Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State),
     Post  =>
       Cut in Base .. Limit
       and then Middle <= Cut
       and then
         (case Nodes (Id).Kind is
            when Concat_Node =>
              Compiled_Shape
                (Nodes, Nodes (Id).Right, Code, Base, Cut, Next, Middle)
              and then
                Compiled_Shape
                  (Nodes,
                   Nodes (Id).Left,
                   Code,
                   Cut,
                   Limit,
                   Middle,
                   Entry_State),
            when Alt_Node    =>
              Cut < Limit
              and then
                Compiled_Shape
                  (Nodes,
                   Nodes (Id).Left,
                   Code,
                   Base,
                   Cut,
                   Next,
                   Code (Limit).Next_1)
              and then
                Compiled_Shape
                  (Nodes,
                   Nodes (Id).Right,
                   Code,
                   Cut,
                   Limit - 1,
                   Next,
                   Code (Limit).Next_2),
            when Repeat_Node =>
              Tail_Shape
                (Nodes,
                 Nodes (Id).Left,
                 Code,
                 Base,
                 Cut,
                 Next,
                 Middle,
                 (if Nodes (Id).Unlimited
                  then 0
                  else Nodes (Id).High - Nodes (Id).Low),
                 Nodes (Id).Unlimited)
              and then
                Copies_Shape
                  (Nodes,
                   Nodes (Id).Left,
                   Code,
                   Cut,
                   Limit,
                   Middle,
                   Entry_State,
                   Nodes (Id).Low),
            when others      => False)
   is
      --  These searches reason only about the shape certificates' quantifier
      --  structure: the witnesses come from Reveal_Shape's postcondition and
      --  are consumed by the frame and join lemmas' contracts. Pruning the
      --  recursive definitions keeps the nested existentials from being
      --  re-instantiated under each enclosing universal.
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Compiled_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Copies_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Optional_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Tail_Shape);
   begin
      Reveal_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State);
      case Nodes (Id).Kind is
         when Concat_Node =>
            for C in Base .. Limit loop
               if (for some M in 0 .. C =>
                     Compiled_Shape
                       (Nodes, Nodes (Id).Right, Code, Base, C, Next, M)
                     and then
                       Compiled_Shape
                         (Nodes,
                          Nodes (Id).Left,
                          Code,
                          C,
                          Limit,
                          M,
                          Entry_State))
               then
                  for M in 0 .. C loop
                     if Compiled_Shape
                          (Nodes, Nodes (Id).Right, Code, Base, C, Next, M)
                       and then
                         Compiled_Shape
                           (Nodes,
                            Nodes (Id).Left,
                            Code,
                            C,
                            Limit,
                            M,
                            Entry_State)
                     then
                        Cut := C;
                        Middle := M;
                        return;
                     end if;
                     pragma
                       Loop_Invariant
                         (for all J in 0 .. M =>
                            not (Compiled_Shape
                                   (Nodes,
                                    Nodes (Id).Right,
                                    Code,
                                    Base,
                                    C,
                                    Next,
                                    J)
                                 and then
                                   Compiled_Shape
                                     (Nodes,
                                      Nodes (Id).Left,
                                      Code,
                                      C,
                                      Limit,
                                      J,
                                      Entry_State)));
                  end loop;
                  pragma Assert (False);
               end if;
               pragma
                 Loop_Invariant
                   (for all K in Base .. C =>
                      not (for some M in 0 .. K =>
                             Compiled_Shape
                               (Nodes,
                                Nodes (Id).Right,
                                Code,
                                Base,
                                K,
                                Next,
                                M)
                             and then
                               Compiled_Shape
                                 (Nodes,
                                  Nodes (Id).Left,
                                  Code,
                                  K,
                                  Limit,
                                  M,
                                  Entry_State)));
            end loop;
            pragma Assert (False);

         when Repeat_Node =>
            for C in Base .. Limit loop
               if (for some M in 0 .. C =>
                     Tail_Shape
                       (Nodes,
                        Nodes (Id).Left,
                        Code,
                        Base,
                        C,
                        Next,
                        M,
                        (if Nodes (Id).Unlimited
                         then 0
                         else Nodes (Id).High - Nodes (Id).Low),
                        Nodes (Id).Unlimited)
                     and then
                       Copies_Shape
                         (Nodes,
                          Nodes (Id).Left,
                          Code,
                          C,
                          Limit,
                          M,
                          Entry_State,
                          Nodes (Id).Low))
               then
                  for M in 0 .. C loop
                     if Tail_Shape
                          (Nodes,
                           Nodes (Id).Left,
                           Code,
                           Base,
                           C,
                           Next,
                           M,
                           (if Nodes (Id).Unlimited
                            then 0
                            else Nodes (Id).High - Nodes (Id).Low),
                           Nodes (Id).Unlimited)
                       and then
                         Copies_Shape
                           (Nodes,
                            Nodes (Id).Left,
                            Code,
                            C,
                            Limit,
                            M,
                            Entry_State,
                            Nodes (Id).Low)
                     then
                        Cut := C;
                        Middle := M;
                        return;
                     end if;
                     pragma
                       Loop_Invariant
                         (for all J in 0 .. M =>
                            not (Tail_Shape
                                   (Nodes,
                                    Nodes (Id).Left,
                                    Code,
                                    Base,
                                    C,
                                    Next,
                                    J,
                                    (if Nodes (Id).Unlimited
                                     then 0
                                     else Nodes (Id).High - Nodes (Id).Low),
                                    Nodes (Id).Unlimited)
                                 and then
                                   Copies_Shape
                                     (Nodes,
                                      Nodes (Id).Left,
                                      Code,
                                      C,
                                      Limit,
                                      J,
                                      Entry_State,
                                      Nodes (Id).Low)));
                  end loop;
                  pragma Assert (False);
               end if;
               pragma
                 Loop_Invariant
                   (for all K in Base .. C =>
                      not (for some M in 0 .. K =>
                             Tail_Shape
                               (Nodes,
                                Nodes (Id).Left,
                                Code,
                                Base,
                                K,
                                Next,
                                M,
                                (if Nodes (Id).Unlimited
                                 then 0
                                 else Nodes (Id).High - Nodes (Id).Low),
                                Nodes (Id).Unlimited)
                             and then
                               Copies_Shape
                                 (Nodes,
                                  Nodes (Id).Left,
                                  Code,
                                  K,
                                  Limit,
                                  M,
                                  Entry_State,
                                  Nodes (Id).Low)));
            end loop;
            pragma Assert (False);

         when Alt_Node    =>
            for C in Base .. Limit - 1 loop
               if Compiled_Shape
                    (Nodes,
                     Nodes (Id).Left,
                     Code,
                     Base,
                     C,
                     Next,
                     Code (Limit).Next_1)
                 and then
                   Compiled_Shape
                     (Nodes,
                      Nodes (Id).Right,
                      Code,
                      C,
                      Limit - 1,
                      Next,
                      Code (Limit).Next_2)
               then
                  Cut := C;
                  Middle := 0;
                  return;
               end if;
               pragma
                 Loop_Invariant
                   (for all K in Base .. C =>
                      not (Compiled_Shape
                             (Nodes,
                              Nodes (Id).Left,
                              Code,
                              Base,
                              K,
                              Next,
                              Code (Limit).Next_1)
                           and then
                             Compiled_Shape
                               (Nodes,
                                Nodes (Id).Right,
                                Code,
                                K,
                                Limit - 1,
                                Next,
                                Code (Limit).Next_2)));
            end loop;
            pragma Assert (False);

         when others      =>
            null;
      end case;
      Cut := 0;
      Middle := 0;
      pragma Assert (False);
   end Shape_Parts;

   procedure Copies_Parts
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Positive;
      Cut, Middle                    : out State_Id)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then
         Copies_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count),
     Post  =>
       Cut in Base .. Limit
       and then Middle <= Cut
       and then
         Copies_Shape (Nodes, Id, Code, Base, Cut, Next, Middle, Count - 1)
       and then
         Compiled_Shape (Nodes, Id, Code, Cut, Limit, Middle, Entry_State)
   is
      --  These searches reason only about the shape certificates' quantifier
      --  structure: the witnesses come from Reveal_Shape's postcondition and
      --  are consumed by the frame and join lemmas' contracts. Pruning the
      --  recursive definitions keeps the nested existentials from being
      --  re-instantiated under each enclosing universal.
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Compiled_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Copies_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Optional_Shape);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Tail_Shape);
   begin
      Reveal_Copies (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count);
      for C in Base .. Limit loop
         if (for some M in 0 .. C =>
               Copies_Shape (Nodes, Id, Code, Base, C, Next, M, Count - 1)
               and then
                 Compiled_Shape (Nodes, Id, Code, C, Limit, M, Entry_State))
         then
            for M in 0 .. C loop
               if Copies_Shape (Nodes, Id, Code, Base, C, Next, M, Count - 1)
                 and then
                   Compiled_Shape (Nodes, Id, Code, C, Limit, M, Entry_State)
               then
                  Cut := C;
                  Middle := M;
                  return;
               end if;
               pragma
                 Loop_Invariant
                   (for all J in 0 .. M =>
                      not (Copies_Shape
                             (Nodes, Id, Code, Base, C, Next, J, Count - 1)
                           and then
                             Compiled_Shape
                               (Nodes, Id, Code, C, Limit, J, Entry_State)));
            end loop;
            pragma Assert (False);
         end if;
         pragma
           Loop_Invariant
             (for all K in Base .. C =>
                not (for some M in 0 .. K =>
                       Copies_Shape
                         (Nodes, Id, Code, Base, K, Next, M, Count - 1)
                       and then
                         Compiled_Shape
                           (Nodes, Id, Code, K, Limit, M, Entry_State)));
      end loop;
      Cut := 0;
      Middle := 0;
      pragma Assert (False);
   end Copies_Parts;

   procedure Optional_Parts
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Positive;
      Cut, Middle                    : out State_Id)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then
         Optional_Shape
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count),
     Post  =>
       Cut in Base .. Limit - 1
       and then Middle <= Cut
       and then
         Optional_Shape
           (Nodes, Id, Code, Base, Cut, Next, Code (Limit).Next_2, Count - 1)
       and then
         Compiled_Shape
           (Nodes,
            Id,
            Code,
            Cut,
            Limit - 1,
            Code (Limit).Next_2,
            Code (Limit).Next_1)
   is
   begin
      for C in Base .. Limit - 1 loop
         if Optional_Shape
              (Nodes, Id, Code, Base, C, Next, Code (Limit).Next_2, Count - 1)
           and then
             Compiled_Shape
               (Nodes,
                Id,
                Code,
                C,
                Limit - 1,
                Code (Limit).Next_2,
                Code (Limit).Next_1)
         then
            Cut := C;
            Middle := 0;
            return;
         end if;
         pragma
           Loop_Invariant
             (for all K in Base .. C =>
                not (Optional_Shape
                       (Nodes,
                        Id,
                        Code,
                        Base,
                        K,
                        Next,
                        Code (Limit).Next_2,
                        Count - 1)
                     and then
                       Compiled_Shape
                         (Nodes,
                          Id,
                          Code,
                          K,
                          Limit - 1,
                          Code (Limit).Next_2,
                          Code (Limit).Next_1)));
      end loop;
      Cut := 0;
      Middle := 0;
      pragma Assert (False);
   end Optional_Parts;

   procedure Lemma_Shape_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State),
     Post               =>
       (Entry_State = Next or Entry_State in Base + 1 .. Limit)
       and then Closed_Interval (Code, Base, Limit, Next),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(0), Decreases => Natural'(0));

   procedure Lemma_Copies_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Copies_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count),
     Post               =>
       (Entry_State = Next or Entry_State in Base + 1 .. Limit)
       and then Closed_Interval (Code, Base, Limit, Next),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count);

   procedure Lemma_Optional_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Optional_Shape
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count),
     Post               =>
       (Entry_State = Next or Entry_State in Base + 1 .. Limit)
       and then Closed_Interval (Code, Base, Limit, Next),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(1), Decreases => Count);

   procedure Lemma_Tail_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural;
      Unlimited                      : Boolean)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Tail_Shape
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count, Unlimited),
     Post               =>
       (Entry_State = Next or Entry_State in Base + 1 .. Limit)
       and then Closed_Interval (Code, Base, Limit, Next),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Natural'(2), Decreases => Count);

   procedure Lemma_Shape_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id)
   is
      Cut, Middle : State_Id := 0;
      N           : constant Node := Nodes (Id);
   begin
      Reveal_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State);
      if N.Kind in Concat_Node | Alt_Node | Repeat_Node then
         Shape_Parts
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Cut, Middle);
      end if;
      case N.Kind is
         when Concat_Node =>
            Lemma_Shape_Closed (Nodes, N.Right, Code, Base, Cut, Next, Middle);
            Lemma_Shape_Closed
              (Nodes, N.Left, Code, Cut, Limit, Middle, Entry_State);

         when Alt_Node    =>
            Lemma_Shape_Closed
              (Nodes, N.Left, Code, Base, Cut, Next, Code (Limit).Next_1);
            Lemma_Shape_Closed
              (Nodes,
               N.Right,
               Code,
               Cut,
               Limit - 1,
               Next,
               Code (Limit).Next_2);

         when Repeat_Node =>
            Lemma_Tail_Closed
              (Nodes,
               N.Left,
               Code,
               Base,
               Cut,
               Next,
               Middle,
               (if N.Unlimited then 0 else N.High - N.Low),
               N.Unlimited);
            Lemma_Copies_Closed
              (Nodes, N.Left, Code, Cut, Limit, Middle, Entry_State, N.Low);

         when others      =>
            null;
      end case;
   end Lemma_Shape_Closed;

   procedure Lemma_Copies_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural)
   is
      Cut, Middle : State_Id := 0;
   begin
      if Count > 0 then
         Copies_Parts
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Cut,
            Middle);
         Lemma_Copies_Closed
           (Nodes, Id, Code, Base, Cut, Next, Middle, Count - 1);
         Lemma_Shape_Closed (Nodes, Id, Code, Cut, Limit, Middle, Entry_State);
      end if;
   end Lemma_Copies_Closed;

   procedure Lemma_Optional_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural)
   is
      Cut, Unused : State_Id;
   begin
      if Count > 0 then
         Optional_Parts
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Cut,
            Unused);
         Lemma_Optional_Closed
           (Nodes, Id, Code, Base, Cut, Next, Code (Limit).Next_2, Count - 1);
         Lemma_Shape_Closed
           (Nodes,
            Id,
            Code,
            Cut,
            Limit - 1,
            Code (Limit).Next_2,
            Code (Limit).Next_1);
      end if;
   end Lemma_Optional_Closed;

   procedure Lemma_Tail_Closed
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Count                          : Natural;
      Unlimited                      : Boolean) is
   begin
      if Unlimited then
         Lemma_Shape_Closed
           (Nodes,
            Id,
            Code,
            Entry_State,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1);
      else
         Lemma_Optional_Closed
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Count);
      end if;
   end Lemma_Tail_Closed;

   --  Skipping an optional copy preserves matching with a larger upper bound.
   procedure Lemma_Optional_Widen
     (Nodes        : Tree;
      Id           : Live_Node;
      Text         : String;
      First, Last  : Natural;
      Small, Large : Natural)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then First <= Last
       and then Last <= Text'Length
       and then Small <= Large
       and then Large <= Max_Repetition
       and then
         Repeated_Matches (Nodes, Id, Text, First, Last, 0, Small, False),
     Post               =>
       Repeated_Matches (Nodes, Id, Text, First, Last, 0, Large, False),
     Subprogram_Variant => (Decreases => Small)
   is
   begin
      if First /= Last and Small /= Large then
         for M in First .. Last loop
            if Matches (Nodes, Nodes (Id).Left, Text, First, M)
              and then
                Repeated_Matches
                  (Nodes, Id, Text, M, Last, 0, Small - 1, False)
            then
               Lemma_Optional_Widen
                 (Nodes, Id, Text, M, Last, Small - 1, Large - 1);
               return;
            end if;
            pragma
              Loop_Invariant
                (for all K in First .. M =>
                   not (Matches (Nodes, Nodes (Id).Left, Text, First, K)
                        and then
                          Repeated_Matches
                            (Nodes, Id, Text, K, Last, 0, Small - 1, False)));
         end loop;
         pragma Assert (False);
      end if;
   end Lemma_Optional_Widen;

   procedure Lemma_Shape_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Post               => Matches (Nodes, Id, Text, First, Last),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(3),
        Decreases => Natural'(0),
        Decreases => Fuel);

   --  Mandatory copies followed by their optional or unbounded suffix.
   procedure Lemma_Copies_Tail_Sound
     (Nodes                                           : Tree;
      Id                                              : Live_Node;
      Code                                            : Code_Array;
      Tail_Base, Base, Limit, Stop, Next, Entry_State : State_Id;
      Count, High                                     : Natural;
      Unlimited                                       : Boolean;
      Text                                            : String;
      First, Last                                     : Natural;
      Fuel                                            : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then Count <= Max_Repetition
       and then High <= Max_Repetition
       and then (Unlimited or Count <= High)
       and then
         Tail_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Tail_Base,
            Base,
            Stop,
            Next,
            (if Unlimited then 0 else High - Count),
            Unlimited)
       and then
         Copies_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Fragment_Path (Code, Entry_State, Stop, Text, First, Last, Fuel),
     Post               =>
       Repeated_Matches (Nodes, Id, Text, First, Last, Count, High, Unlimited),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(2),
        Decreases => Count,
        Decreases => Fuel);

   procedure Lemma_Tail_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Unlimited                      : Boolean;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then High <= Max_Repetition
       and then
         Tail_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Unlimited)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Post               =>
       Repeated_Matches (Nodes, Id, Text, First, Last, 0, High, Unlimited),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(1),
        Decreases => High,
        Decreases => Fuel);

   procedure Lemma_Optional_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then High <= Max_Repetition
       and then
         Optional_Shape
           (Nodes, Nodes (Id).Left, Code, Base, Limit, Next, Entry_State, High)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Post               =>
       Repeated_Matches (Nodes, Id, Text, First, Last, 0, High, False),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(0),
        Decreases => High,
        Decreases => Fuel);

   procedure Lemma_Shape_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   is
      Cut, Middle : State_Id := 0;
      Position    : Natural;
      Prefix_Fuel : Big_Integer;
      N           : constant Node := Nodes (Id);
   begin
      Reveal_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State);
      if N.Kind in Concat_Node | Alt_Node | Repeat_Node then
         Shape_Parts
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Cut, Middle);
      end if;
      case N.Kind is
         when Concat_Node =>
            Lemma_Shape_Closed
              (Nodes, N.Left, Code, Cut, Limit, Middle, Entry_State);
            Lemma_Path_Decompose
              (Code,
               Limit,
               Cut,
               Entry_State,
               Middle,
               Next,
               Text,
               First,
               Last,
               Fuel,
               Position,
               Prefix_Fuel);
            Lemma_Shape_Sound
              (Nodes,
               N.Left,
               Code,
               Cut,
               Limit,
               Middle,
               Entry_State,
               Text,
               First,
               Position,
               Prefix_Fuel);
            Lemma_Shape_Sound
              (Nodes,
               N.Right,
               Code,
               Base,
               Cut,
               Next,
               Middle,
               Text,
               Position,
               Last,
               Fuel - Prefix_Fuel);

         when Alt_Node    =>
            if Fragment_Path
                 (Code, Code (Limit).Next_1, Next, Text, First, Last, Fuel - 1)
            then
               Lemma_Shape_Sound
                 (Nodes,
                  N.Left,
                  Code,
                  Base,
                  Cut,
                  Next,
                  Code (Limit).Next_1,
                  Text,
                  First,
                  Last,
                  Fuel - 1);
            else
               Lemma_Shape_Sound
                 (Nodes,
                  N.Right,
                  Code,
                  Cut,
                  Limit - 1,
                  Next,
                  Code (Limit).Next_2,
                  Text,
                  First,
                  Last,
                  Fuel - 1);
            end if;

         when Repeat_Node =>
            Lemma_Copies_Tail_Sound
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Limit,
               Next,
               Middle,
               Entry_State,
               N.Low,
               N.High,
               N.Unlimited,
               Text,
               First,
               Last,
               Fuel);

         when others      =>
            null;
      end case;
   end Lemma_Shape_Sound;

   procedure Lemma_Copies_Tail_Sound
     (Nodes                                           : Tree;
      Id                                              : Live_Node;
      Code                                            : Code_Array;
      Tail_Base, Base, Limit, Stop, Next, Entry_State : State_Id;
      Count, High                                     : Natural;
      Unlimited                                       : Boolean;
      Text                                            : String;
      First, Last                                     : Natural;
      Fuel                                            : Path_Steps)
   is
      Cut, Middle : State_Id := 0;
      Position    : Natural;
      Prefix_Fuel : Big_Integer;
   begin
      if Count = 0 then
         Lemma_Tail_Sound
           (Nodes,
            Id,
            Code,
            Tail_Base,
            Base,
            Stop,
            Next,
            High,
            Unlimited,
            Text,
            First,
            Last,
            Fuel);
      else
         Copies_Parts
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Cut,
            Middle);
         Lemma_Shape_Closed
           (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State);
         Lemma_Path_Decompose
           (Code,
            Limit,
            Cut,
            Entry_State,
            Middle,
            Stop,
            Text,
            First,
            Last,
            Fuel,
            Position,
            Prefix_Fuel);
         Lemma_Shape_Sound
           (Nodes,
            Nodes (Id).Left,
            Code,
            Cut,
            Limit,
            Middle,
            Entry_State,
            Text,
            First,
            Position,
            Prefix_Fuel);
         Lemma_Copies_Tail_Sound
           (Nodes,
            Id,
            Code,
            Tail_Base,
            Base,
            Cut,
            Stop,
            Next,
            Middle,
            Count - 1,
            (if Unlimited then High else High - 1),
            Unlimited,
            Text,
            Position,
            Last,
            Fuel - Prefix_Fuel);
      end if;
   end Lemma_Copies_Tail_Sound;

   procedure Lemma_Tail_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Unlimited                      : Boolean;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   is
      Position    : Natural;
      Prefix_Fuel : Big_Integer;
   begin
      if not Unlimited then
         Lemma_Optional_Sound
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Text,
            First,
            Last,
            Fuel);
      elsif First /= Last then
         --  The exit branch cannot consume this nonempty span.
         Lemma_Shape_Closed
           (Nodes,
            Nodes (Id).Left,
            Code,
            Entry_State,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1);
         Lemma_Path_Decompose
           (Code,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1,
            Entry_State,
            Next,
            Text,
            First,
            Last,
            Fuel - 1,
            Position,
            Prefix_Fuel);
         Lemma_Shape_Sound
           (Nodes,
            Nodes (Id).Left,
            Code,
            Entry_State,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1,
            Text,
            First,
            Position,
            Prefix_Fuel);
         Lemma_Tail_Sound
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Unlimited,
            Text,
            Position,
            Last,
            Fuel - 1 - Prefix_Fuel);
      --  If the body was empty, the suffix already proves the goal.
      --  Otherwise Position is the advancing witness required by the model.
      end if;
   end Lemma_Tail_Sound;

   procedure Lemma_Optional_Sound
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : Path_Steps)
   is
      Cut, Unused : State_Id;
      Position    : Natural;
      Prefix_Fuel : Big_Integer;
   begin
      if First /= Last then
         Optional_Parts
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Cut,
            Unused);
         if Fragment_Path
              (Code, Code (Limit).Next_2, Next, Text, First, Last, Fuel - 1)
         then
            Lemma_Optional_Sound
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Next,
               Code (Limit).Next_2,
               High - 1,
               Text,
               First,
               Last,
               Fuel - 1);
            Lemma_Optional_Widen
              (Nodes, Id, Text, First, Last, High - 1, High);
         else
            Lemma_Shape_Closed
              (Nodes,
               Nodes (Id).Left,
               Code,
               Cut,
               Limit - 1,
               Code (Limit).Next_2,
               Code (Limit).Next_1);
            Lemma_Path_Decompose
              (Code,
               Limit - 1,
               Cut,
               Code (Limit).Next_1,
               Code (Limit).Next_2,
               Next,
               Text,
               First,
               Last,
               Fuel - 1,
               Position,
               Prefix_Fuel);
            Lemma_Shape_Sound
              (Nodes,
               Nodes (Id).Left,
               Code,
               Cut,
               Limit - 1,
               Code (Limit).Next_2,
               Code (Limit).Next_1,
               Text,
               First,
               Position,
               Prefix_Fuel);
            Lemma_Optional_Sound
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Next,
               Code (Limit).Next_2,
               High - 1,
               Text,
               Position,
               Last,
               Fuel - 1 - Prefix_Fuel);
         end if;
      end if;
   end Lemma_Optional_Sound;

   procedure Repetition_Middle
     (Nodes                  : Tree;
      Id                     : Live_Node;
      Text                   : String;
      First, Last, Low, High : Natural;
      Unlimited              : Boolean;
      Middle                 : out Natural)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then First <= Last
       and then Last <= Text'Length
       and then Low <= Max_Repetition
       and then High <= Max_Repetition
       and then (Unlimited or Low <= High)
       and then (Low > 0 or First < Last)
       and then
         Repeated_Matches (Nodes, Id, Text, First, Last, Low, High, Unlimited),
     Post  =>
       Middle in First .. Last
       and then (if Low = 0 and Unlimited then Middle > First)
       and then Matches (Nodes, Nodes (Id).Left, Text, First, Middle)
       and then
         Repeated_Matches
           (Nodes,
            Id,
            Text,
            Middle,
            Last,
            (if Low > 0 then Low - 1 else 0),
            (if Unlimited then High else High - 1),
            Unlimited)
   is
   begin
      for M in First .. Last loop
         if (Low > 0 or not Unlimited or M > First)
           and then Matches (Nodes, Nodes (Id).Left, Text, First, M)
           and then
             Repeated_Matches
               (Nodes,
                Id,
                Text,
                M,
                Last,
                (if Low > 0 then Low - 1 else 0),
                (if Unlimited then High else High - 1),
                Unlimited)
         then
            Middle := M;
            return;
         end if;
         pragma
           Loop_Invariant
             (for all K in First .. M =>
                not ((Low > 0 or not Unlimited or K > First)
                     and then Matches (Nodes, Nodes (Id).Left, Text, First, K)
                     and then
                       Repeated_Matches
                         (Nodes,
                          Id,
                          Text,
                          K,
                          Last,
                          (if Low > 0 then Low - 1 else 0),
                          (if Unlimited then High else High - 1),
                          Unlimited)));
      end loop;
      Middle := First;
      pragma Assert (False);
   end Repetition_Middle;

   procedure Lemma_Shape_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then
         Compiled_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State)
       and then First <= Last
       and then Last <= Text'Length
       and then Matches (Nodes, Id, Text, First, Last),
     Post               =>
       Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(3),
        Decreases => Natural'(0),
        Decreases => Last - First);

   procedure Lemma_Copies_Tail_Complete
     (Nodes                                           : Tree;
      Id                                              : Live_Node;
      Code                                            : Code_Array;
      Tail_Base, Base, Limit, Stop, Next, Entry_State : State_Id;
      Count, High                                     : Natural;
      Unlimited                                       : Boolean;
      Text                                            : String;
      First, Last                                     : Natural;
      Fuel                                            : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then Count <= Max_Repetition
       and then High <= Max_Repetition
       and then (Unlimited or Count <= High)
       and then
         Tail_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Tail_Base,
            Base,
            Stop,
            Next,
            (if Unlimited then 0 else High - Count),
            Unlimited)
       and then
         Copies_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Repeated_Matches
           (Nodes, Id, Text, First, Last, Count, High, Unlimited),
     Post               =>
       Fragment_Path (Code, Entry_State, Stop, Text, First, Last, Fuel),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(2),
        Decreases => Count,
        Decreases => Last - First);

   procedure Lemma_Tail_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Unlimited                      : Boolean;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then High <= Max_Repetition
       and then
         Tail_Shape
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Unlimited)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Repeated_Matches (Nodes, Id, Text, First, Last, 0, High, Unlimited),
     Post               =>
       Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(1),
        Decreases => High,
        Decreases => Last - First);

   procedure Lemma_Optional_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Nodes (Id).Kind = Repeat_Node
       and then High <= Max_Repetition
       and then
         Optional_Shape
           (Nodes, Nodes (Id).Left, Code, Base, Limit, Next, Entry_State, High)
       and then First <= Last
       and then Last <= Text'Length
       and then
         Repeated_Matches (Nodes, Id, Text, First, Last, 0, High, False),
     Post               =>
       Fragment_Path (Code, Entry_State, Next, Text, First, Last, Fuel),
     Subprogram_Variant =>
       (Decreases => Id,
        Decreases => Natural'(0),
        Decreases => High,
        Decreases => Last - First);

   procedure Lemma_Shape_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   is
      Cut, Middle           : State_Id := 0;
      Left_Fuel, Right_Fuel : Big_Integer;
      N                     : constant Node := Nodes (Id);
   begin
      Reveal_Shape (Nodes, Id, Code, Base, Limit, Next, Entry_State);
      if N.Kind in Concat_Node | Alt_Node | Repeat_Node then
         Shape_Parts
           (Nodes, Id, Code, Base, Limit, Next, Entry_State, Cut, Middle);
      end if;
      case N.Kind is
         when Concat_Node =>
            for M in First .. Last loop
               if Matches (Nodes, N.Left, Text, First, M)
                 and then Matches (Nodes, N.Right, Text, M, Last)
               then
                  Lemma_Shape_Complete
                    (Nodes,
                     N.Left,
                     Code,
                     Cut,
                     Limit,
                     Middle,
                     Entry_State,
                     Text,
                     First,
                     M,
                     Left_Fuel);
                  Lemma_Shape_Complete
                    (Nodes,
                     N.Right,
                     Code,
                     Base,
                     Cut,
                     Next,
                     Middle,
                     Text,
                     M,
                     Last,
                     Right_Fuel);
                  Lemma_Shape_Closed
                    (Nodes, N.Left, Code, Cut, Limit, Middle, Entry_State);
                  Lemma_Path_Compose
                    (Code,
                     Limit,
                     Cut,
                     Entry_State,
                     Middle,
                     Next,
                     Text,
                     First,
                     M,
                     Last,
                     Left_Fuel,
                     Right_Fuel);
                  Fuel := Left_Fuel + Right_Fuel;
                  return;
               end if;
               pragma
                 Loop_Invariant
                   (for all K in First .. M =>
                      not (Matches (Nodes, N.Left, Text, First, K)
                           and then Matches (Nodes, N.Right, Text, K, Last)));
            end loop;
            Fuel := 0;
            pragma Assert (False);

         when Alt_Node    =>
            if Matches (Nodes, N.Left, Text, First, Last) then
               Lemma_Shape_Complete
                 (Nodes,
                  N.Left,
                  Code,
                  Base,
                  Cut,
                  Next,
                  Code (Limit).Next_1,
                  Text,
                  First,
                  Last,
                  Left_Fuel);
            else
               Lemma_Shape_Complete
                 (Nodes,
                  N.Right,
                  Code,
                  Cut,
                  Limit - 1,
                  Next,
                  Code (Limit).Next_2,
                  Text,
                  First,
                  Last,
                  Left_Fuel);
            end if;
            Fuel := Left_Fuel + 1;

         when Repeat_Node =>
            Lemma_Copies_Tail_Complete
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Limit,
               Next,
               Middle,
               Entry_State,
               N.Low,
               N.High,
               N.Unlimited,
               Text,
               First,
               Last,
               Fuel);

         when Empty_Node  =>
            Fuel := 0;

         when others      =>
            Fuel := 1;
      end case;
   end Lemma_Shape_Complete;

   procedure Lemma_Copies_Tail_Complete
     (Nodes                                           : Tree;
      Id                                              : Live_Node;
      Code                                            : Code_Array;
      Tail_Base, Base, Limit, Stop, Next, Entry_State : State_Id;
      Count, High                                     : Natural;
      Unlimited                                       : Boolean;
      Text                                            : String;
      First, Last                                     : Natural;
      Fuel                                            : out Path_Steps)
   is
      Cut, Middle           : State_Id;
      Position              : Natural;
      Left_Fuel, Right_Fuel : Big_Integer;
   begin
      if Count = 0 then
         Lemma_Tail_Complete
           (Nodes,
            Id,
            Code,
            Tail_Base,
            Base,
            Stop,
            Next,
            High,
            Unlimited,
            Text,
            First,
            Last,
            Fuel);
      else
         Copies_Parts
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            Count,
            Cut,
            Middle);
         Repetition_Middle
           (Nodes, Id, Text, First, Last, Count, High, Unlimited, Position);
         Lemma_Shape_Complete
           (Nodes,
            Nodes (Id).Left,
            Code,
            Cut,
            Limit,
            Middle,
            Entry_State,
            Text,
            First,
            Position,
            Left_Fuel);
         Lemma_Copies_Tail_Complete
           (Nodes,
            Id,
            Code,
            Tail_Base,
            Base,
            Cut,
            Stop,
            Next,
            Middle,
            Count - 1,
            (if Unlimited then High else High - 1),
            Unlimited,
            Text,
            Position,
            Last,
            Right_Fuel);
         Lemma_Shape_Closed
           (Nodes, Nodes (Id).Left, Code, Cut, Limit, Middle, Entry_State);
         Lemma_Path_Compose
           (Code,
            Limit,
            Cut,
            Entry_State,
            Middle,
            Stop,
            Text,
            First,
            Position,
            Last,
            Left_Fuel,
            Right_Fuel);
         Fuel := Left_Fuel + Right_Fuel;
      end if;
   end Lemma_Copies_Tail_Complete;

   procedure Lemma_Tail_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Unlimited                      : Boolean;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   is
      Position              : Natural;
      Left_Fuel, Right_Fuel : Big_Integer;
   begin
      if not Unlimited then
         Lemma_Optional_Complete
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Text,
            First,
            Last,
            Fuel);
      elsif First = Last then
         Fuel := 1;
      else
         Repetition_Middle
           (Nodes, Id, Text, First, Last, 0, High, Unlimited, Position);
         Lemma_Shape_Complete
           (Nodes,
            Nodes (Id).Left,
            Code,
            Entry_State,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1,
            Text,
            First,
            Position,
            Left_Fuel);
         Lemma_Tail_Complete
           (Nodes,
            Id,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Unlimited,
            Text,
            Position,
            Last,
            Right_Fuel);
         Lemma_Shape_Closed
           (Nodes,
            Nodes (Id).Left,
            Code,
            Entry_State,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1);
         Lemma_Path_Compose
           (Code,
            Limit,
            Entry_State,
            Code (Entry_State).Next_1,
            Entry_State,
            Next,
            Text,
            First,
            Position,
            Last,
            Left_Fuel,
            Right_Fuel);
         Fuel := Left_Fuel + Right_Fuel + 1;
      end if;
   end Lemma_Tail_Complete;

   procedure Lemma_Optional_Complete
     (Nodes                          : Tree;
      Id                             : Live_Node;
      Code                           : Code_Array;
      Base, Limit, Next, Entry_State : State_Id;
      High                           : Natural;
      Text                           : String;
      First, Last                    : Natural;
      Fuel                           : out Path_Steps)
   is
      Cut, Unused           : State_Id;
      Position              : Natural;
      Left_Fuel, Right_Fuel : Big_Integer;
   begin
      if High = 0 then
         Fuel := 0;
      else
         Optional_Parts
           (Nodes,
            Nodes (Id).Left,
            Code,
            Base,
            Limit,
            Next,
            Entry_State,
            High,
            Cut,
            Unused);
         if First = Last then
            Lemma_Optional_Complete
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Next,
               Code (Limit).Next_2,
               High - 1,
               Text,
               First,
               Last,
               Right_Fuel);
            Fuel := Right_Fuel + 1;
         else
            Repetition_Middle
              (Nodes, Id, Text, First, Last, 0, High, False, Position);
            Lemma_Shape_Complete
              (Nodes,
               Nodes (Id).Left,
               Code,
               Cut,
               Limit - 1,
               Code (Limit).Next_2,
               Code (Limit).Next_1,
               Text,
               First,
               Position,
               Left_Fuel);
            Lemma_Optional_Complete
              (Nodes,
               Id,
               Code,
               Base,
               Cut,
               Next,
               Code (Limit).Next_2,
               High - 1,
               Text,
               Position,
               Last,
               Right_Fuel);
            Lemma_Shape_Closed
              (Nodes,
               Nodes (Id).Left,
               Code,
               Cut,
               Limit - 1,
               Code (Limit).Next_2,
               Code (Limit).Next_1);
            Lemma_Path_Compose
              (Code,
               Limit - 1,
               Cut,
               Code (Limit).Next_1,
               Code (Limit).Next_2,
               Next,
               Text,
               First,
               Position,
               Last,
               Left_Fuel,
               Right_Fuel);
            Fuel := Left_Fuel + Right_Fuel + 1;
         end if;
      end if;
   end Lemma_Optional_Complete;
   function Tree_Compiled
     (Nodes : Tree; Root : Live_Node; Self : Program) return Boolean
   is (Self.Count >= 1
       and then Self.Code (1).Op = Accept_State
       and then
         Compiled_Shape
           (Nodes, Root, Self.Code, 1, Self.Count, 1, Self.Start));


   procedure Compile_Tree
     (Nodes  : Tree;
      Root   : Live_Node;
      Result : out Program;
      Status : out Compile_Status)
   is
      Expansions : Natural range 0 .. 65_536 := 0;
      procedure Emit
        (Op    : Opcode;
         A, B  : State_Id;
         Id    : out State_Id;
         Bytes : Byte_Set := [others => False])
      with
        Pre  =>
          not Result.Valid
          and Links_Valid (Result)
          and A <= Result.Count
          and B <= Result.Count,
        Post =>
          not Result.Valid
          and (if Status'Old /= Success then Status = Status'Old)
          and
            (if Status'Old = Success
             then Status in Success | State_Limit | Expansion_Limit)
          and Links_Valid (Result)
          and Result.Count >= Result.Count'Old
          and Id <= Result.Count
          and (if Status = Success then Id > 0)
      is
         pragma
           Postcondition
             (Static =>
                (for all K in 1 .. Result.Count'Old =>
                   Result.Code (K) = Result.Code'Old (K))
                and (if Id /= 0 then Id > Result.Count'Old)
                and
                  (if Status = Success
                   then
                     Id = Result.Count
                     and Result.Count = Result.Count'Old + 1
                     and Result.Code (Id) = Instruction'(Op, Bytes, A, B)));
      begin
         Id := 0;
         if Status /= Success then
            return;
         end if;
         if Result.Count = Max_States then
            Status := State_Limit;
            return;
         end if;
         Result.Count := Result.Count + 1;
         Result.Code (Result.Count) := (Op, Bytes, A, B);
         Id := Result.Count;
      end Emit;

      procedure Build
        (Id : Live_Node; Next : State_Id; Entry_State : out State_Id)
      with
        Subprogram_Variant => (Decreases => Id),
        Pre                =>
          not Result.Valid and Links_Valid (Result) and Next <= Result.Count,
        Post               =>
          not Result.Valid
          and (if Status'Old /= Success then Status = Status'Old)
          and
            (if Status'Old = Success
             then Status in Success | State_Limit | Expansion_Limit)
          and Links_Valid (Result)
          and Result.Count >= Result.Count'Old
          and Entry_State <= Result.Count
          and (if Status = Success and Next > 0 then Entry_State > 0)
      is
         pragma Precondition (Static => Tree_Valid (Nodes));
         pragma
           Postcondition
             (Static =>
                (for all K in 1 .. Result.Count'Old =>
                   Result.Code (K) = Result.Code'Old (K))
                and
                  (if Status = Success
                   then
                     (Entry_State = Next or Entry_State > Result.Count'Old)
                     and Fragment_Closed (Result, Result.Count'Old, Next)
                     and Compiled_Shape
                       (Nodes, Id, Result.Code, Result.Count'Old, Result.Count,
                        Next, Entry_State)
                     and
                       (if Nodes (Id).Kind in Empty_Node .. End_Node
                        then
                          Leaf_Compiled
                            (Nodes (Id),
                             Result,
                             Result.Count'Old,
                             Next,
                             Entry_State))));
         Base    : constant State_Id := Result.Count
         with Ghost => Static;
         A, B, S : State_Id;
         N       : Node;
      begin
         Entry_State := 0;
         if Status /= Success then
            return;
         end if;
         if Expansions = 65_536 then
            Status := Expansion_Limit;
            return;
         end if;
         Expansions := Expansions + 1;
         N := Nodes (Id);
         case N.Kind is
            when Empty_Node  =>
               Entry_State := Next;

            when Bytes_Node  =>
               Emit (Consume, Next, 0, Entry_State, N.Bytes);

            when Start_Node  =>
               Emit (At_Start, Next, 0, Entry_State);

            when End_Node    =>
               Emit (At_End, Next, 0, Entry_State);

            when Concat_Node =>
               Build (N.Right, Next, A);
               declare
                  Cut : constant State_Id := Result.Count with Ghost => Static;
                  Right_Code : constant Code_Array := Result.Code with Ghost => Static;
               begin
                  Build (N.Left, A, Entry_State);
                  if Status = Success then
                     Lemma_Shape_Frame
                       (Nodes, N.Right, Right_Code, Result.Code, Base, Cut, Next, A);
                     Lemma_Concat_Join
                       (Nodes, Id, Result.Code, Base, Cut, Result.Count, Next, A, Entry_State);
                  end if;
               end;

            when Alt_Node    =>
               Build (N.Left, Next, A);
               declare
                  Cut : constant State_Id := Result.Count with Ghost => Static;
                  Left_Code : constant Code_Array := Result.Code with Ghost => Static;
               begin
                  Build (N.Right, Next, B);
                  declare
                     Right_Last : constant State_Id := Result.Count with Ghost => Static;
                     Right_Code : constant Code_Array := Result.Code with Ghost => Static;
                  begin
                     Emit (Split, A, B, Entry_State);
                     if Status = Success then
                        Lemma_Shape_Frame
                          (Nodes, N.Left, Left_Code, Result.Code, Base, Cut, Next, A);
                        Lemma_Shape_Frame
                          (Nodes, N.Right, Right_Code, Result.Code, Cut, Right_Last, Next, B);
                     end if;
                  end;
               end;

            when Repeat_Node =>
               A := Next;
               if N.Unlimited then
                  Emit (Split, 0, Next, S);
                  Build (N.Left, S, B);
                  declare
                     Body_Code : constant Code_Array := Result.Code with Ghost => Static;
                  begin
                     if S /= 0 then
                        Result.Code (S).Next_1 := B;
                     end if;
                     if Status = Success then
                        Lemma_Shape_Frame
                          (Nodes, N.Left, Body_Code, Result.Code, S, Result.Count, S, B);
                     end if;
                  end;
                  A := S;
               else
                  for K in 1 .. N.High - N.Low loop
                     pragma
                       Loop_Invariant
                         (not Result.Valid and Links_Valid (Result));
                     pragma
                       Loop_Invariant
                         (Result.Count >= Result.Count'Loop_Entry);
                     pragma
                       Loop_Invariant
                         (Static =>
                            (for all J in 1 .. Result.Count'Loop_Entry =>
                               Result.Code (J) = Result.Code'Loop_Entry (J)));
                     pragma
                       Loop_Invariant
                         (Status in Success | State_Limit | Expansion_Limit);
                  pragma Loop_Invariant
                    (if Status'Loop_Entry /= Success then Status = Status'Loop_Entry);
                     pragma
                       Loop_Invariant
                         (Static =>
                            (if Status = Success
                             then
                               (A = Next or A > Base)
                               and Fragment_Closed (Result, Base, Next)));
                     pragma Loop_Invariant (A <= Result.Count);
                     pragma
                       Loop_Invariant
                         (if Status = Success and Next > 0 then A > 0);
                     pragma Loop_Invariant
                       (Static => (if Status = Success then Optional_Shape
                         (Nodes, N.Left, Result.Code, Base, Result.Count, Next, A, K - 1)));
                     declare
                        Previous_Code : constant Code_Array := Result.Code with Ghost => Static;
                        Cut : constant State_Id := Result.Count with Ghost => Static;
                        Previous_Entry : constant State_Id := A with Ghost => Static;
                     begin
                        Build (N.Left, A, B);
                        declare
                           Body_Code : constant Code_Array := Result.Code with Ghost => Static;
                           Body_Last : constant State_Id := Result.Count with Ghost => Static;
                        begin
                           Emit (Split, B, A, S);
                           if Status = Success then
                              Lemma_Optional_Frame
                                (Nodes, N.Left, Previous_Code, Result.Code,
                                 Base, Cut, Next, Previous_Entry, K - 1);
                              Lemma_Shape_Frame
                                (Nodes, N.Left, Body_Code, Result.Code,
                                 Cut, Body_Last, Previous_Entry, B);
                           end if;
                        end;
                     end;
                     A := S;
                     pragma Assert (Static => (if Status = Success then Optional_Shape
                       (Nodes, N.Left, Result.Code, Base, Result.Count, Next, A, K)));
                  end loop;
               end if;
               pragma Assert (Static => (if Status = Success then Tail_Shape
                 (Nodes, N.Left, Result.Code, Base, Result.Count, Next, A,
                  (if N.Unlimited then 0 else N.High - N.Low), N.Unlimited)));
               declare
                  Tail_Last : constant State_Id := Result.Count with Ghost => Static;
                  Tail_Entry : constant State_Id := A with Ghost => Static;
                  Tail_Code : constant Code_Array := Result.Code with Ghost => Static;
               begin
                  if Status = Success then
                     Lemma_Tail_Frame
                       (Nodes, N.Left, Result.Code, Tail_Code, Base, Tail_Last,
                        Next, Tail_Entry, (if N.Unlimited then 0 else N.High - N.Low), N.Unlimited);
                  end if;
               for K in 1 .. N.Low loop
                  pragma
                    Loop_Invariant (not Result.Valid and Links_Valid (Result));
                  pragma
                    Loop_Invariant (Result.Count >= Result.Count'Loop_Entry);
                  pragma
                    Loop_Invariant
                      (Static =>
                         (for all J in 1 .. Result.Count'Loop_Entry =>
                            Result.Code (J) = Result.Code'Loop_Entry (J)));
                  pragma
                    Loop_Invariant
                      (Status in Success | State_Limit | Expansion_Limit);
                  pragma Loop_Invariant
                    (if Status'Loop_Entry /= Success then Status = Status'Loop_Entry);
                  pragma
                    Loop_Invariant
                      (Static =>
                         (if Status = Success
                          then
                            (A = Next or A > Base)
                            and Fragment_Closed (Result, Base, Next)));
                  pragma Loop_Invariant (A <= Result.Count);
                  pragma
                    Loop_Invariant
                      (if Status = Success and Next > 0 then A > 0);
                  pragma Loop_Invariant
                    (Static => (if Status = Success then Copies_Shape
                      (Nodes, N.Left, Result.Code, Tail_Last, Result.Count, Tail_Entry, A, K - 1)));
                  declare
                     Previous_Code : constant Code_Array := Result.Code with Ghost => Static;
                     Cut : constant State_Id := Result.Count with Ghost => Static;
                     Previous_Entry : constant State_Id := A with Ghost => Static;
                  begin
                     Build (N.Left, A, B);
                     if Status = Success then
                        Lemma_Copies_Frame
                          (Nodes, N.Left, Previous_Code, Result.Code,
                           Tail_Last, Cut, Tail_Entry, Previous_Entry, K - 1);
                        Lemma_Copies_Join
                          (Nodes, N.Left, Result.Code, Tail_Last, Cut, Result.Count,
                           Tail_Entry, Previous_Entry, B, K);
                     end if;
                  end;
                  A := B;
                  pragma Assert (Static => (if Status = Success then Copies_Shape
                    (Nodes, N.Left, Result.Code, Tail_Last, Result.Count, Tail_Entry, A, K)));
               end loop;
                  if Status = Success then
                     Lemma_Tail_Frame
                       (Nodes, N.Left, Tail_Code, Result.Code, Base, Tail_Last,
                        Next, Tail_Entry, (if N.Unlimited then 0 else N.High - N.Low), N.Unlimited);
                     Lemma_Repeat_Join
                       (Nodes, Id, Result.Code, Base, Tail_Last, Result.Count, Next, Tail_Entry, A);
                  end if;
               end;
               Entry_State := A;
         end case;
      end Build;

   begin
      Result := (others => <>);
      Status := Success;
      declare
         Final, Entry_State : State_Id;
      begin
         Emit (Accept_State, 0, 0, Final);
         Build (Root, Final, Entry_State);
         pragma Assert (Expansions <= 65_536);
         Result.Start := Entry_State;
      end;
      Result.Valid := Status = Success;
   end Compile_Tree;
   function Is_Valid (Self : Program) return Boolean
   is (Self.Valid);
   function State_Count (Self : Program) return Natural
   is (Self.Count);

   type State_Set is array (State_Id) of Boolean;
   type Links is array (State_Id) of State_Id;

   function Consumes_To
     (Self   : Program;
      Before : State_Set;
      Byte   : Character;
      Source : Live_State;
      Target : State_Id) return Boolean
   is (Before (Source)
       and then Self.Code (Source).Op = Consume
       and then Self.Code (Source).Bytes (Byte)
       and then Self.Code (Source).Next_1 = Target)
   with Ghost;

   --  Exact one-byte NFA transition: each destination is present iff some
   --  active consuming instruction accepts this byte and points there.
   procedure Advance
     (Self   : Program;
      Before : State_Set;
      Byte   : Character;
      After  : out State_Set)
   with
     Global => null,
     Always_Terminates,
     Post   =>
       (for all Target in 0 .. Self.Count =>
          After (Target)
          = (for some Source in 1 .. Self.Count =>
               Consumes_To (Self, Before, Byte, Source, Target)))
   is
      pragma
        Postcondition
          (Static =>
             (for all Target in State_Id =>
                After (Target)
                = (for some Source in 1 .. Self.Count =>
                     Consumes_To (Self, Before, Byte, Source, Target))));
   begin
      After := [others => False];
      for Id in 1 .. Self.Count loop
         if Before (Id)
           and then Self.Code (Id).Op = Consume
           and then Self.Code (Id).Bytes (Byte)
         then
            After (Self.Code (Id).Next_1) := True;
         end if;
         pragma
           Loop_Invariant
             (Static =>
                (for all Target in State_Id =>
                   After (Target)
                   = (for some Source in 1 .. Id =>
                        Consumes_To (Self, Before, Byte, Source, Target))));
      end loop;
   end Advance;

   function Epsilon_Edge
     (Self              : Program;
      Source            : Live_State;
      Target            : State_Id;
      At_First, At_Last : Boolean) return Boolean
   is (Target /= 0
       and then
         (case Self.Code (Source).Op is
            when Split    =>
              Target = Self.Code (Source).Next_1
              or Target = Self.Code (Source).Next_2,
            when At_Start => At_First and Target = Self.Code (Source).Next_1,
            when At_End   => At_Last and Target = Self.Code (Source).Next_1,
            when others   => False))
   with Ghost;

   --  Declarative bounded-path semantics, independent of the worklist.
   --  Steps counts epsilon edges, with anchors evaluated at this text boundary.
   function Epsilon_Reach
     (Self              : Program;
      Seeds             : State_Set;
      At_First, At_Last : Boolean;
      Target            : State_Id;
      Steps             : Natural) return Boolean
   is (Target in 1 .. Self.Count
       and then
         (Seeds (Target)
          or else
            (Steps > 0
             and then
               (for some Source in 1 .. Self.Count =>
                  Epsilon_Edge (Self, Source, Target, At_First, At_Last)
                  and then
                    Epsilon_Reach
                      (Self, Seeds, At_First, At_Last, Source, Steps - 1)))))
   with Ghost => Static, Subprogram_Variant => (Decreases => Steps);

   --  Ada array equality concerns the declared index range. Establish that
   --  the recursive relation depends only on elements in that range too.
   procedure Lemma_Reach_Extensional
     (Self              : Program;
      Left, Right       : State_Set;
      At_First, At_Last : Boolean;
      Steps             : Natural)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Steps),
     Pre                => Left = Right,
     Post               =>
       (for all Id in State_Id =>
          Epsilon_Reach (Self, Left, At_First, At_Last, Id, Steps)
          = Epsilon_Reach (Self, Right, At_First, At_Last, Id, Steps))
   is
   begin
      if Steps > 0 then
         Lemma_Reach_Extensional
           (Self, Left, Right, At_First, At_Last, Steps - 1);
      end if;
   end Lemma_Reach_Extensional;

   function Epsilon_Closed
     (Self : Program; Reached : State_Set; At_First, At_Last : Boolean)
      return Boolean
   is (for all Source in 1 .. Self.Count =>
         (if Reached (Source)
          then
            (for all Target in 1 .. Self.Count =>
               (if Epsilon_Edge (Self, Source, Target, At_First, At_Last)
                then Reached (Target)))))
   with Ghost => Static;

   procedure Lemma_Reach_Monotone
     (Self              : Program;
      Seeds             : State_Set;
      At_First, At_Last : Boolean;
      Small, Large      : Natural)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Small),
     Pre                => Small <= Large,
     Post               =>
       (for all Target in 1 .. Self.Count =>
          (if Epsilon_Reach (Self, Seeds, At_First, At_Last, Target, Small)
           then Epsilon_Reach (Self, Seeds, At_First, At_Last, Target, Large)))
   is
   begin
      if Small > 0 and then Small < Large then
         Lemma_Reach_Monotone
           (Self, Seeds, At_First, At_Last, Small - 1, Large - 1);
      end if;
   end Lemma_Reach_Monotone;

   --  A closed superset of the seeds contains every finite epsilon path.
   procedure Lemma_Closed_Reach
     (Self              : Program;
      Seeds, Reached    : State_Set;
      At_First, At_Last : Boolean;
      Steps             : Natural)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Steps),
     Pre                =>
       Epsilon_Closed (Self, Reached, At_First, At_Last)
       and
         (for all Id in 1 .. Self.Count => (if Seeds (Id) then Reached (Id))),
     Post               =>
       (for all Target in 1 .. Self.Count =>
          (if Epsilon_Reach (Self, Seeds, At_First, At_Last, Target, Steps)
           then Reached (Target)))
   is
   begin
      if Steps > 0 then
         Lemma_Closed_Reach
           (Self, Seeds, Reached, At_First, At_Last, Steps - 1);
      end if;
   end Lemma_Closed_Reach;

   function Cardinality (Items : State_Set; Last : State_Id) return Natural
   is (if Last = 0
       then 0
       else Cardinality (Items, Last - 1) + Boolean'Pos (Items (Last)))
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Last),
     Post               => Cardinality'Result <= Last;

   procedure Lemma_Empty_Count (Items : State_Set; Last : State_Id)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Last),
     Pre                => (for all K in 1 .. Last => not Items (K)),
     Post               => Cardinality (Items, Last) = 0
   is
   begin
      if Last > 0 then
         Lemma_Empty_Count (Items, Last - 1);
      end if;
   end Lemma_Empty_Count;

   procedure Lemma_Add_Count
     (Before, After : State_Set; Id : Live_State; Last : State_Id)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Last),
     Pre                =>
       not Before (Id)
       and After (Id)
       and (for all K in State_Id => (if K /= Id then Before (K) = After (K))),
     Post               =>
       Cardinality (After, Last)
       = Cardinality (Before, Last) + (if Id <= Last then 1 else 0)
   is
   begin
      if Last > 0 then
         Lemma_Add_Count (Before, After, Id, Last - 1);
      end if;
   end Lemma_Add_Count;

   procedure Lemma_Count_Missing
     (Items : State_Set; Id : Live_State; Last : State_Id)
   with
     Ghost              => Static,
     Subprogram_Variant => (Decreases => Last),
     Pre                => Id <= Last and not Items (Id),
     Post               => Cardinality (Items, Last) < Last
   is
   begin
      if Id < Last then
         Lemma_Count_Missing (Items, Id, Last - 1);
      end if;
   end Lemma_Count_Missing;

   function Outside_Empty (Self : Program; Items : State_Set) return Boolean
   is (for all Id in State_Id =>
         (if Id not in 1 .. Self.Count then not Items (Id)))
   with Ghost => Static;

   procedure Closure
     (Self              : Program;
      Seeds             : State_Set;
      At_First, At_Last : Boolean;
      Reached           : out State_Set)
   with
     Global => null,
     Always_Terminates,
     Pre    => Links_Valid (Self),
     Post   =>
       not Reached (0)
       and (for all Id in 1 .. Self.Count => (if Seeds (Id) then Reached (Id)))
   is
      pragma
        Postcondition
          (Static =>
             Outside_Empty (Self, Reached)
             and Epsilon_Closed (Self, Reached, At_First, At_Last)
             and
               (for all Id in State_Id =>
                  Reached (Id)
                  = Epsilon_Reach
                      (Self, Seeds, At_First, At_Last, Id, Self.Count)));
      --  Append-only worklist. Each reached state has exactly one slot;
      --  processed slots form a prefix. No linked-list acyclicity assumption.
      Pending : Links := [others => 0];
      Tail    : State_Id := 0;
      Done    : State_Id := 0;
      S       : State_Id;
      Rank    : Links := [others => 0]
      with Ghost => Static;
      type Depth_Array is array (State_Id) of Natural;
      Depth   : Depth_Array := [others => 0]
      with Ghost => Static;
      Limit   : Natural range 0 .. Max_States := 0
      with Ghost => Static;

      function Certified return Boolean
      is (for all Id in 1 .. Self.Count =>
            (if Reached (Id)
             then
               Depth (Id) <= Limit
               and then
                 Epsilon_Reach
                   (Self, Seeds, At_First, At_Last, Id, Depth (Id))))
      with Ghost => Static;

      function Queue_Valid return Boolean
      is (Done <= Tail
          and then Tail <= Self.Count
          and then Tail = Cardinality (Reached, Self.Count)
          and then
            (for all I in 1 .. Tail =>
               Pending (I) in 1 .. Self.Count
               and then Reached (Pending (I))
               and then Rank (Pending (I)) = I)
          and then
            (for all Id in 1 .. Self.Count =>
               (if Reached (Id)
                then
                  Rank (Id) in 1 .. Tail and then Pending (Rank (Id)) = Id)))
      with Ghost => Static;

      function Processed_Closed return Boolean
      is (for all I in 1 .. Done =>
            (for all Target in 1 .. Self.Count =>
               (if Epsilon_Edge (Self, Pending (I), Target, At_First, At_Last)
                then Reached (Target))))
      with Ghost => Static, Pre => Queue_Valid;

      procedure Push (Id : State_Id; From : State_Id)
      with
        Pre  =>
          (Static =>
             Outside_Empty (Self, Reached)
             and Certified
             and Queue_Valid
             and Id <= Self.Count
             and
               (Id = 0
                or else Seeds (Id)
                or else
                  (From in 1 .. Self.Count
                   and then Reached (From)
                   and then Depth (From) < Limit
                   and then
                     Epsilon_Edge (Self, From, Id, At_First, At_Last)))),
        Post =>
          (Static =>
             Certified
             and Queue_Valid
             and Outside_Empty (Self, Reached)
             and Done = Done'Old
             and Tail >= Tail'Old
             and (for all I in 1 .. Tail'Old => Pending (I) = Pending'Old (I))
             and
               (for all K in 1 .. Self.Count =>
                  (if Reached'Old (K)
                   then Reached (K) and Depth (K) = Depth'Old (K)))
             and (if Id /= 0 then Reached (Id)))
      is
         Before : constant State_Set := Reached
         with Ghost => Static;
      begin
         if Id /= 0 and then not Reached (Id) then
            Lemma_Count_Missing (Reached, Id, Self.Count);
            if Seeds (Id) then
               Depth (Id) := 0;
            else
               Depth (Id) := Depth (From) + 1;
            end if;
            Tail := Tail + 1;
            Pending (Tail) := Id;
            Rank (Id) := Tail;
            Reached (Id) := True;
            Lemma_Add_Count (Before, Reached, Id, Self.Count);
         end if;
      end Push;
   begin
      Reached := [others => False];
      Lemma_Empty_Count (Reached, Self.Count);
      for Id in 1 .. Self.Count loop
         if Seeds (Id) then
            Push (Id, 0);
         end if;
         pragma Loop_Invariant (Static => Certified and Queue_Valid);
         pragma
           Loop_Invariant
             (Static =>
                Outside_Empty (Self, Reached) and Limit = 0 and Done = 0);
         pragma
           Loop_Invariant
             (Static =>
                (for all K in 1 .. Id => (if Seeds (K) then Reached (K))));
      end loop;
      for Iteration in 1 .. Self.Count loop
         pragma Loop_Invariant (Static => Certified and Queue_Valid);
         pragma Loop_Invariant (Static => Processed_Closed);
         pragma Loop_Invariant (Static => Outside_Empty (Self, Reached));
         pragma
           Loop_Invariant
             (Static => Limit = Iteration - 1 and Done = Iteration - 1);
         pragma
           Loop_Invariant
             (Static =>
                (for all K in 1 .. Self.Count =>
                   (if Seeds (K) then Reached (K))));
         exit when Done = Tail;
         S := Pending (Iteration);
         Limit := Iteration;
         case Self.Code (S).Op is
            when Split    =>
               Push (Self.Code (S).Next_1, S);
               Push (Self.Code (S).Next_2, S);

            when At_Start =>
               if At_First then
                  Push (Self.Code (S).Next_1, S);
               end if;

            when At_End   =>
               if At_Last then
                  Push (Self.Code (S).Next_1, S);
               end if;

            when others   =>
               null;
         end case;
         Done := Iteration;
      end loop;
      pragma Assert (Static => Done = Tail);
      pragma
        Assert (Static => Epsilon_Closed (Self, Reached, At_First, At_Last));
      Lemma_Closed_Reach (Self, Seeds, Reached, At_First, At_Last, Self.Count);
      for Id in 1 .. Self.Count loop
         if Reached (Id) then
            Lemma_Reach_Monotone
              (Self, Seeds, At_First, At_Last, Depth (Id), Self.Count);
         end if;
         pragma
           Loop_Invariant
             (Static =>
                (for all K in 1 .. Id =>
                   (if Reached (K)
                    then
                      Epsilon_Reach
                        (Self, Seeds, At_First, At_Last, K, Self.Count))));
      end loop;
   end Closure;

   --  Set-based NFA semantics. These definitions neither call Advance nor
   --  Closure nor Run; byte edges, epsilon paths, and text positions are
   --  specified independently of the executable simulator.
   function Model_Closure
     (Self : Program; Seeds : State_Set; At_First, At_Last : Boolean)
      return State_Set
   with
     Ghost => Static,
     Post  =>
       (for all Id in State_Id =>
          Model_Closure'Result (Id)
          = Epsilon_Reach (Self, Seeds, At_First, At_Last, Id, Self.Count))
   is
   begin
      return
        [for Id in State_Id =>
           Epsilon_Reach (Self, Seeds, At_First, At_Last, Id, Self.Count)];
   end Model_Closure;

   function Model_Step
     (Self : Program; Before : State_Set; Byte : Character; Restart : Boolean)
      return State_Set
   with
     Ghost => Static,
     Post  =>
       (for all Target in State_Id =>
          Model_Step'Result (Target)
          = ((Restart and Target = Self.Start)
             or else
               (for some Source in 1 .. Self.Count =>
                  Consumes_To (Self, Before, Byte, Source, Target))))
   is
   begin
      return
        [for Target in State_Id =>
           (Restart and Target = Self.Start)
           or else
             (for some Source in 1 .. Self.Count =>
                Consumes_To (Self, Before, Byte, Source, Target))];
   end Model_Step;

   function Model_Start (Self : Program) return State_Set
   with
     Ghost => Static,
     Post  =>
       (for all Id in State_Id => Model_Start'Result (Id) = (Id = Self.Start))
   is
   begin
      return [for Id in State_Id => Id = Self.Start];
   end Model_Start;

   function Model_States
     (Self : Program; Text : String; Whole : Boolean; Offset : Natural)
      return State_Set
   with
     Ghost              => Static,
     Pre                => Offset <= Text'Length,
     Subprogram_Variant => (Decreases => Offset),
     Post               =>
       Model_States'Result
       = (if Offset = 0
          then Model_Closure (Self, Model_Start (Self), True, Text'Length = 0)
          else
            Model_Closure
              (Self,
               Model_Step
                 (Self,
                  Model_States (Self, Text, Whole, Offset - 1),
                  Text (Text'First + (Offset - 1)),
                  not Whole),
               False,
               Offset = Text'Length))
   is
   begin
      if Offset = 0 then
         return
           Model_Closure (Self, Model_Start (Self), True, Text'Length = 0);
      else
         return
           Model_Closure
             (Self,
              Model_Step
                (Self,
                 Model_States (Self, Text, Whole, Offset - 1),
                 Text (Text'First + (Offset - 1)),
                 not Whole),
              False,
              Offset = Text'Length);
      end if;
   end Model_States;

   --  Reuse the proved closure algorithm to establish properties of the
   --  independently defined model. This lemma is erased with other ghosts.
   procedure Lemma_Model_Closure_Properties
     (Self : Program; Seeds : State_Set; At_First, At_Last : Boolean)
   with
     Ghost => Static,
     Pre   => Links_Valid (Self),
     Post  =>
       Epsilon_Closed
         (Self,
          Model_Closure (Self, Seeds, At_First, At_Last),
          At_First,
          At_Last)
       and
         (for all Id in 1 .. Self.Count =>
            (if Seeds (Id)
             then Model_Closure (Self, Seeds, At_First, At_Last) (Id)))
   is
      Reached : State_Set;
   begin
      Closure (Self, Seeds, At_First, At_Last, Reached);
      pragma Assert (Reached = Model_Closure (Self, Seeds, At_First, At_Last));
   end Lemma_Model_Closure_Properties;

   procedure Lemma_Model_Edge
     (Self           : Program;
      Text           : String;
      Whole          : Boolean;
      Offset         : Natural;
      Source, Target : Live_State)
   with
     Ghost => Static,
     Pre   =>
       Links_Valid (Self)
       and then Offset <= Text'Length
       and then Source <= Self.Count
       and then Target <= Self.Count
       and then Model_States (Self, Text, Whole, Offset) (Source)
       and then
         Epsilon_Edge (Self, Source, Target, Offset = 0, Offset = Text'Length),
     Post  => Model_States (Self, Text, Whole, Offset) (Target)
   is
   begin
      if Offset = 0 then
         Lemma_Model_Closure_Properties
           (Self, Model_Start (Self), True, Text'Length = 0);
      else
         Lemma_Model_Closure_Properties
           (Self,
            Model_Step
              (Self,
               Model_States (Self, Text, Whole, Offset - 1),
               Text (Text'First + (Offset - 1)),
               not Whole),
            False,
            Offset = Text'Length);
      end if;
   end Lemma_Model_Edge;

   procedure Lemma_Model_Consume
     (Self           : Program;
      Text           : String;
      Whole          : Boolean;
      Offset         : Natural;
      Source, Target : Live_State)
   with
     Ghost => Static,
     Pre   =>
       Links_Valid (Self)
       and then Offset < Text'Length
       and then Source <= Self.Count
       and then Target <= Self.Count
       and then
         Consumes_To
           (Self,
            Model_States (Self, Text, Whole, Offset),
            Text (Text'First + Offset),
            Source,
            Target),
     Post  => Model_States (Self, Text, Whole, Offset + 1) (Target)
   is
   begin
      Lemma_Model_Closure_Properties
        (Self,
         Model_Step
           (Self,
            Model_States (Self, Text, Whole, Offset),
            Text (Text'First + Offset),
            not Whole),
         False,
         Offset + 1 = Text'Length);
   end Lemma_Model_Consume;

   procedure Lemma_Path_States
     (Self              : Program;
      Entry_State, Stop : Live_State;
      Text              : String;
      Whole             : Boolean;
      First, Last       : Natural;
      Fuel              : Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Links_Valid (Self)
       and then Entry_State <= Self.Count
       and then Stop <= Self.Count
       and then First <= Last
       and then Last <= Text'Length
       and then Model_States (Self, Text, Whole, First) (Entry_State)
       and then
         Fragment_Path (Self.Code, Entry_State, Stop, Text, First, Last, Fuel),
     Post               => Model_States (Self, Text, Whole, Last) (Stop),
     Subprogram_Variant => (Decreases => Fuel)
   is
      Target : State_Id;
   begin
      if Entry_State /= Stop then
         case Self.Code (Entry_State).Op is
            when Consume             =>
               Target := Self.Code (Entry_State).Next_1;
               Lemma_Model_Consume
                 (Self, Text, Whole, First, Entry_State, Target);
               Lemma_Path_States
                 (Self, Target, Stop, Text, Whole, First + 1, Last, Fuel - 1);

            when Split               =>
               if Fragment_Path
                    (Self.Code,
                     Self.Code (Entry_State).Next_1,
                     Stop,
                     Text,
                     First,
                     Last,
                     Fuel - 1)
               then
                  Target := Self.Code (Entry_State).Next_1;
               else
                  Target := Self.Code (Entry_State).Next_2;
               end if;
               Lemma_Model_Edge
                 (Self, Text, Whole, First, Entry_State, Target);
               Lemma_Path_States
                 (Self, Target, Stop, Text, Whole, First, Last, Fuel - 1);

            when At_Start | At_End   =>
               Target := Self.Code (Entry_State).Next_1;
               Lemma_Model_Edge
                 (Self, Text, Whole, First, Entry_State, Target);
               Lemma_Path_States
                 (Self, Target, Stop, Text, Whole, First, Last, Fuel - 1);

            when Dead | Accept_State =>
               null;
         end case;
      end if;
   end Lemma_Path_States;

   function Boundary_Seeds
     (Self : Program; Text : String; Whole : Boolean; Offset : Natural)
      return State_Set
   is (if Offset = 0
       then Model_Start (Self)
       else
         Model_Step
           (Self,
            Model_States (Self, Text, Whole, Offset - 1),
            Text (Text'First + (Offset - 1)),
            not Whole))
   with Ghost => Static, Pre => Offset <= Text'Length;

   procedure Lemma_Model_Seeds
     (Self : Program; Text : String; Whole : Boolean; Offset : Natural)
   with
     Ghost => Static,
     Pre   => Offset <= Text'Length,
     Post  =>
       (for all Id in State_Id =>
          Model_States (Self, Text, Whole, Offset) (Id)
          = Epsilon_Reach
              (Self,
               Boundary_Seeds (Self, Text, Whole, Offset),
               Offset = 0,
               Offset = Text'Length,
               Id,
               Self.Count))
   is
   begin
      if Offset = 0 then
         Lemma_Reach_Extensional
           (Self,
            Boundary_Seeds (Self, Text, Whole, Offset),
            Model_Start (Self),
            True,
            Text'Length = 0,
            Self.Count);
      else
         Lemma_Reach_Extensional
           (Self,
            Boundary_Seeds (Self, Text, Whole, Offset),
            Model_Step
              (Self,
               Model_States (Self, Text, Whole, Offset - 1),
               Text (Text'First + (Offset - 1)),
               not Whole),
            False,
            Offset = Text'Length,
            Self.Count);
      end if;
   end Lemma_Model_Seeds;

   function Reverse_Budget
     (Self : Program; Offset, Epsilon_Steps : Natural) return Path_Steps
   is (To_Big_Integer (Offset)
       * (To_Big_Integer (Self.Count) + 1)
       + To_Big_Integer (Epsilon_Steps))
   with Ghost => Static, Pre => Epsilon_Steps <= Self.Count;

   --  Reconstruct a prefix backwards while carrying an already valid suffix
   --  to an accepting state. The accepting endpoint cannot occur inside the
   --  prefix because it has no outgoing instructions.
   procedure Lemma_Reach_Prepend
     (Self                        : Program;
      Source, Stop                : Live_State;
      Text                        : String;
      Whole                       : Boolean;
      Offset, Last, Epsilon_Steps : Natural;
      Fuel                        : Path_Steps;
      First                       : out Natural;
      Total_Fuel                  : out Path_Steps)
   with
     Ghost              => Static,
     Pre                =>
       Internal_Valid (Self)
       and then Self.Valid
       and then Source <= Self.Count
       and then Stop <= Self.Count
       and then Self.Code (Stop).Op = Accept_State
       and then Offset <= Last
       and then Last <= Text'Length
       and then Epsilon_Steps <= Self.Count
       and then
         Epsilon_Reach
           (Self,
            Boundary_Seeds (Self, Text, Whole, Offset),
            Offset = 0,
            Offset = Text'Length,
            Source,
            Epsilon_Steps)
       and then
         Fragment_Path (Self.Code, Source, Stop, Text, Offset, Last, Fuel),
     Post               =>
       First <= Offset
       and then (if Whole then First = 0)
       and then
         Total_Fuel <= Fuel + Reverse_Budget (Self, Offset, Epsilon_Steps)
       and then
         Fragment_Path
           (Self.Code, Self.Start, Stop, Text, First, Last, Total_Fuel),
     Subprogram_Variant => (Decreases => Offset, Decreases => Epsilon_Steps)
   is
      Seeds : constant State_Set := Boundary_Seeds (Self, Text, Whole, Offset);
   begin
      if Seeds (Source) then
         if Offset = 0 or else (not Whole and Source = Self.Start) then
            First := Offset;
            Total_Fuel := Fuel;
            return;
         end if;
         for Pred in 1 .. Self.Count loop
            if Consumes_To
                 (Self,
                  Model_States (Self, Text, Whole, Offset - 1),
                  Text (Text'First + (Offset - 1)),
                  Pred,
                  Source)
            then
               pragma
                 Assert
                   (Fragment_Path
                      (Self.Code,
                       Pred,
                       Stop,
                       Text,
                       Offset - 1,
                       Last,
                       Fuel + 1));
               Lemma_Model_Seeds (Self, Text, Whole, Offset - 1);
               Lemma_Reach_Prepend
                 (Self,
                  Pred,
                  Stop,
                  Text,
                  Whole,
                  Offset - 1,
                  Last,
                  Self.Count,
                  Fuel + 1,
                  First,
                  Total_Fuel);
               return;
            end if;
            pragma
              Loop_Invariant
                (for all K in 1 .. Pred =>
                   not Consumes_To
                         (Self,
                          Model_States (Self, Text, Whole, Offset - 1),
                          Text (Text'First + (Offset - 1)),
                          K,
                          Source));
         end loop;
      else
         for Pred in 1 .. Self.Count loop
            if Epsilon_Edge
                 (Self, Pred, Source, Offset = 0, Offset = Text'Length)
              and then
                Epsilon_Reach
                  (Self,
                   Seeds,
                   Offset = 0,
                   Offset = Text'Length,
                   Pred,
                   Epsilon_Steps - 1)
            then
               pragma
                 Assert
                   (Fragment_Path
                      (Self.Code, Pred, Stop, Text, Offset, Last, Fuel + 1));
               Lemma_Reach_Prepend
                 (Self,
                  Pred,
                  Stop,
                  Text,
                  Whole,
                  Offset,
                  Last,
                  Epsilon_Steps - 1,
                  Fuel + 1,
                  First,
                  Total_Fuel);
               return;
            end if;
            pragma
              Loop_Invariant
                (for all K in 1 .. Pred =>
                   not (Epsilon_Edge
                          (Self, K, Source, Offset = 0, Offset = Text'Length)
                        and then
                          Epsilon_Reach
                            (Self,
                             Seeds,
                             Offset = 0,
                             Offset = Text'Length,
                             K,
                             Epsilon_Steps - 1)));
         end loop;
      end if;
      First := 0;
      Total_Fuel := 0;
      pragma Assert (False);
   end Lemma_Reach_Prepend;

   function Accepting (Self : Program; Items : State_Set) return Boolean
   is (for some Id in 1 .. Self.Count =>
         Items (Id) and Self.Code (Id).Op = Accept_State)
   with Ghost => Static;

   function NFA_Accepts
     (Self : Program; Text : String; Whole : Boolean) return Boolean
   is (Self.Valid
       and then
         (if Whole
          then Accepting (Self, Model_States (Self, Text, Whole, Text'Length))
          else
            (for some Offset in 0 .. Text'Length =>
               Accepting (Self, Model_States (Self, Text, Whole, Offset)))));

   procedure Lemma_Model_Entry
     (Self : Program; Text : String; Whole : Boolean; Offset : Natural)
   with
     Ghost => Static,
     Pre   =>
       Internal_Valid (Self)
       and then Self.Valid
       and then Offset <= Text'Length
       and then (not Whole or Offset = 0),
     Post  => Model_States (Self, Text, Whole, Offset) (Self.Start)
   is
   begin
      if Offset = 0 then
         Lemma_Model_Closure_Properties
           (Self, Model_Start (Self), True, Text'Length = 0);
      else
         Lemma_Model_Closure_Properties
           (Self,
            Model_Step
              (Self,
               Model_States (Self, Text, Whole, Offset - 1),
               Text (Text'First + (Offset - 1)),
               not Whole),
            False,
            Offset = Text'Length);
      end if;
   end Lemma_Model_Entry;

   procedure Lemma_Path_Accepts
     (Self        : Program;
      Stop        : Live_State;
      Text        : String;
      Whole       : Boolean;
      First, Last : Natural;
      Fuel        : Path_Steps)
   with
     Ghost => Static,
     Pre   =>
       Internal_Valid (Self)
       and then Self.Valid
       and then Stop <= Self.Count
       and then Self.Code (Stop).Op = Accept_State
       and then First <= Last
       and then Last <= Text'Length
       and then (if Whole then First = 0 and Last = Text'Length)
       and then
         Fragment_Path (Self.Code, Self.Start, Stop, Text, First, Last, Fuel),
     Post  =>
       NFA_Accepts (Self, Text, Whole)
       and (if Whole then Full_Match (Self, Text) else Search (Self, Text))
   is
   begin
      Lemma_Model_Entry (Self, Text, Whole, First);
      Lemma_Path_States
        (Self, Self.Start, Stop, Text, Whole, First, Last, Fuel);
      pragma Assert (Accepting (Self, Model_States (Self, Text, Whole, Last)));
   end Lemma_Path_Accepts;

   procedure Lemma_Accepts_Path
     (Self        : Program;
      Text        : String;
      Whole       : Boolean;
      First, Last : out Natural;
      Stop        : out Live_State;
      Fuel        : out Path_Steps)
   with
     Ghost => Static,
     Pre   => Internal_Valid (Self) and then NFA_Accepts (Self, Text, Whole),
     Post  =>
       Stop <= Self.Count
       and then Self.Code (Stop).Op = Accept_State
       and then First <= Last
       and then Last <= Text'Length
       and then (if Whole then First = 0 and Last = Text'Length)
       and then Fuel <= Reverse_Budget (Self, Last, Self.Count)
       and then
         Fragment_Path (Self.Code, Self.Start, Stop, Text, First, Last, Fuel)
   is
   begin
      for Offset in 0 .. Text'Length loop
         if not Whole or else Offset = Text'Length then
            for Id in 1 .. Self.Count loop
               if Self.Code (Id).Op = Accept_State
                 and then Model_States (Self, Text, Whole, Offset) (Id)
               then
                  Lemma_Model_Seeds (Self, Text, Whole, Offset);
                  Lemma_Reach_Prepend
                    (Self,
                     Id,
                     Id,
                     Text,
                     Whole,
                     Offset,
                     Offset,
                     Self.Count,
                     0,
                     First,
                     Fuel);
                  Stop := Id;
                  Last := Offset;
                  return;
               end if;
               pragma
                 Loop_Invariant
                   (for all K in 1 .. Id =>
                      not (Self.Code (K).Op = Accept_State
                           and then
                             Model_States (Self, Text, Whole, Offset) (K)));
            end loop;
         end if;
         pragma
           Loop_Invariant
             (for all K in 0 .. Offset =>
                (if not Whole or K = Text'Length
                 then
                   not Accepting (Self, Model_States (Self, Text, Whole, K))));
      end loop;
      First := 0;
      Last := 0;
      Stop := 1;
      Fuel := 0;
      pragma Assert (False);
   end Lemma_Accepts_Path;


   procedure Tree_Match_Span
     (Nodes       : Tree;
      Root        : Live_Node;
      Text        : String;
      Whole       : Boolean;
      First, Last : out Natural)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Nodes) and then Tree_Accepts (Nodes, Root, Text, Whole),
     Post  =>
       First <= Last
       and then Last <= Text'Length
       and then (if Whole then First = 0 and Last = Text'Length)
       and then Matches (Nodes, Root, Text, First, Last)
   is
   begin
      if Whole then
         First := 0;
         Last := Text'Length;
         return;
      end if;
      for F in 0 .. Text'Length loop
         if (for some L in F .. Text'Length =>
               Matches (Nodes, Root, Text, F, L))
         then
            for L in F .. Text'Length loop
               if Matches (Nodes, Root, Text, F, L) then
                  First := F;
                  Last := L;
                  return;
               end if;
               pragma
                 Loop_Invariant
                   (for all K in F .. L =>
                      not Matches (Nodes, Root, Text, F, K));
            end loop;
            pragma Assert (False);
         end if;
         pragma
           Loop_Invariant
             (for all K in 0 .. F =>
                not (for some L in K .. Text'Length =>
                       Matches (Nodes, Root, Text, K, L)));
      end loop;
      First := 0;
      Last := 0;
      pragma Assert (False);
   end Tree_Match_Span;

   --  These premises are precisely the successful Compile_Tree guarantees.
   procedure Lemma_Compiler_Correct
     (Nodes : Tree;
      Root  : Live_Node;
      Self  : Program;
      Text  : String;
      Whole : Boolean)
   is
      First, Last : Natural;
      Stop        : Live_State;
      Fuel        : Big_Integer;
   begin
      if NFA_Accepts (Self, Text, Whole) then
         Lemma_Accepts_Path (Self, Text, Whole, First, Last, Stop, Fuel);
         Lemma_Shape_Closed
           (Nodes, Root, Self.Code, 1, Self.Count, 1, Self.Start);
         pragma Assert (Stop = 1);
         Lemma_Shape_Sound
           (Nodes,
            Root,
            Self.Code,
            1,
            Self.Count,
            1,
            Self.Start,
            Text,
            First,
            Last,
            Fuel);
         pragma
           Assert
             (for some L in First .. Text'Length =>
                Matches (Nodes, Root, Text, First, L));
      elsif Tree_Accepts (Nodes, Root, Text, Whole) then
         Tree_Match_Span (Nodes, Root, Text, Whole, First, Last);
         Lemma_Shape_Complete
           (Nodes,
            Root,
            Self.Code,
            1,
            Self.Count,
            1,
            Self.Start,
            Text,
            First,
            Last,
            Fuel);
         Lemma_Path_Accepts (Self, 1, Text, Whole, First, Last, Fuel);
      end if;
   end Lemma_Compiler_Correct;

   --  Apply the theorem to the actual compiler for an arbitrary supplied text.
   procedure Compile_Tree_For_Text
     (Nodes  : Tree;
      Root   : Live_Node;
      Text   : String;
      Whole  : Boolean;
      Result : out Program;
      Status : out Compile_Status)
   is
   begin
      Compile_Tree (Nodes, Root, Result, Status);
      if Status = Success then
         Lemma_Compiler_Correct (Nodes, Root, Result, Text, Whole);
      end if;
   end Compile_Tree_For_Text;
   function Run (Self : Program; Text : String; Whole : Boolean) return Boolean
   with
     Pre  => Internal_Valid (Self),
     Post => (Static => Run'Result = NFA_Accepts (Self, Text, Whole))
   is
      Current : State_Set;
      Seeds   : State_Set := [others => False];
      Initial : constant State_Set := Model_Start (Self)
      with Ghost => Static;
   begin
      if not Self.Valid then
         return False;
      end if;
      Seeds (Self.Start) := True;
      pragma Assert (Static => Seeds = Initial);
      Lemma_Reach_Extensional
        (Self, Seeds, Initial, True, Text'Length = 0, Self.Count);
      Closure (Self, Seeds, True, Text'Length = 0, Current);
      pragma
        Assert
          (Static =>
             Current = Model_Closure (Self, Initial, True, Text'Length = 0));
      pragma Assert (Static => Current = Model_States (Self, Text, Whole, 0));
      for Offset in 0 .. Text'Length loop
         pragma
           Loop_Invariant
             (Static => Current = Model_States (Self, Text, Whole, Offset));
         pragma
           Loop_Invariant
             (Static =>
                (if not Whole
                 then
                   (for all Earlier in 0 .. Offset =>
                      (if Earlier < Offset
                       then
                         not Accepting
                               (Self,
                                Model_States (Self, Text, Whole, Earlier))))));
         if not Whole or else Offset = Text'Length then
            for Id in 1 .. Self.Count loop
               if Current (Id) and then Self.Code (Id).Op = Accept_State then
                  return True;
               end if;
               pragma
                 Loop_Invariant
                   (Static =>
                      (for all K in 1 .. Id =>
                         not (Current (K)
                              and Self.Code (K).Op = Accept_State)));
            end loop;
         end if;
         exit when Offset = Text'Length;
         declare
            Expected_Seeds : constant State_Set :=
              Model_Step
                (Self,
                 Model_States (Self, Text, Whole, Offset),
                 Text (Text'First + Offset),
                 not Whole)
            with Ghost => Static;
         begin
            Advance (Self, Current, Text (Text'First + Offset), Seeds);
            if not Whole then
               Seeds (Self.Start) := True;
            end if;
            pragma Assert (Static => Seeds = Expected_Seeds);
            Lemma_Reach_Extensional
              (Self,
               Seeds,
               Expected_Seeds,
               False,
               Offset = Text'Length - 1,
               Self.Count);
            Closure (Self, Seeds, False, Offset = Text'Length - 1, Current);
            pragma
              Assert
                (Static =>
                   Current
                   = Model_Closure
                       (Self,
                        Expected_Seeds,
                        False,
                        Offset = Text'Length - 1));
            pragma
              Assert
                (Static =>
                   Current = Model_States (Self, Text, Whole, Offset + 1));
         end;
      end loop;
      return False;
   end Run;

   function Search (Self : Program; Text : String) return Boolean
   is (Run (Self, Text, False));
   function Full_Match (Self : Program; Text : String) return Boolean
   is (Run (Self, Text, True));
end Spark_Re_Trees.Matching;

--  Byte-oriented regular expressions. No allocation, I/O, or global state.
--  Instantiate to choose the storage budget; each compiled Program owns its NFA.

generic
   Max_Nodes : Positive := 512;
   Max_States : Positive := 4_096;
package Spark_Re with SPARK_Mode is
   Max_Pattern_Length : constant := 65_535;
   Max_Repetition     : constant := 255;
   type Compile_Status is
     (Success,
      Syntax_Error,
      Pattern_Too_Long,
      Node_Limit,
      State_Limit,
      Expansion_Limit);
   type Program is private;
   function Is_Valid (Self : Program) return Boolean
   with Global => null;
   function State_Count (Self : Program) return Natural
   with Global => null, Post => State_Count'Result <= Max_States;
   --  Every emitted edge stays within the compiled prefix, and successful
   --  programs have a live entry point. This does not specify pattern parsing.
   function Well_Formed (Self : Program) return Boolean
   with Ghost, Global => null;
   procedure Compile
     (Pattern : String; Result : out Program; Status : out Compile_Status)
   with
     Global => null,
     Always_Terminates,
     Post   => (Is_Valid (Result) = (Status = Success)) and Well_Formed (Result);
   --  Search accepts a substring; Full_Match accepts the entire byte string.
   --  Invalid programs return False. Anchors refer to the entire input string.
   function Search (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Search'Result);
   function Full_Match (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Full_Match'Result);
private
   subtype State_Id is Natural range 0 .. Max_States;
   subtype Live_State is State_Id range 1 .. Max_States;
   type Byte_Set is array (Character) of Boolean;
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
end Spark_Re;

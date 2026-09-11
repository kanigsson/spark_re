package body Spark_Re
  with SPARK_Mode
is
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
   type Frame is record
      Expr, Term, Atom : Node_Id := 0;
      Quantified       : Boolean := False;
   end record;
   type Frame_Array is array (Live_Node) of Frame;

   procedure Compile
     (Pattern : String; Result : out Program; Status : out Compile_Status)
   is
      Nodes      : Tree := [others => <>];
      Used       : Node_Id := 0;
      Frames     : Frame_Array := [others => <>];
      Top        : Live_Node := 1;
      Pos        : Natural := 0;
      Root       : Node_Id;
      Expansions : Natural range 0 .. 65_536 := 0;

      function Peek return Character
      is (if Pos < Pattern'Length
          then Pattern (Pattern'First + Pos)
          else Character'Val (0));

      procedure Add (N : Node; Id : out Node_Id) is
      begin
         Id := 0;
         if Status /= Success then
            return;
         end if;
         if Used = Max_Nodes then
            Status := Node_Limit;
            return;
         end if;
         Used := Used + 1;
         Nodes (Used) := N;
         Id := Used;
      end Add;

      procedure Flush_Atom is
         Id : Node_Id;
      begin
         if Frames (Top).Atom /= 0 then
            if Frames (Top).Term = 0 then
               Frames (Top).Term := Frames (Top).Atom;
            else
               Add
                 ((Kind   => Concat_Node,
                   Left   => Frames (Top).Term,
                   Right  => Frames (Top).Atom,
                   others => <>),
                  Id);
               Frames (Top).Term := Id;
            end if;
         end if;
         Frames (Top).Atom := 0;
         Frames (Top).Quantified := False;
      end Flush_Atom;

      procedure Flush_Term is
         Id : Node_Id;
      begin
         Flush_Atom;
         if Frames (Top).Term = 0 then
            Add ((Kind => Empty_Node, others => <>), Id);
            Frames (Top).Term := Id;
         end if;
         if Frames (Top).Expr = 0 then
            Frames (Top).Expr := Frames (Top).Term;
         else
            Add
              ((Kind   => Alt_Node,
                Left   => Frames (Top).Expr,
                Right  => Frames (Top).Term,
                others => <>),
               Id);
            Frames (Top).Expr := Id;
         end if;
         Frames (Top).Term := 0;
      end Flush_Term;

      procedure Number (Value : out Natural)
      with
        Pre  => Pos <= Pattern'Length,
        Post => Value <= Max_Repetition and Pos in Pos'Old .. Pattern'Length
      is
         Digit : Natural;
         Found : Boolean := False;
      begin
         Value := 0;
         while Pos < Pattern'Length and then Peek in '0' .. '9' loop
            pragma Loop_Invariant (Value <= Max_Repetition);
            pragma Loop_Invariant (Pos in Pos'Loop_Entry .. Pattern'Length);
            pragma Loop_Variant (Decreases => Pattern'Length - Pos);
            Found := True;
            Digit := Character'Pos (Peek) - Character'Pos ('0');
            if Value > (Max_Repetition - Digit) / 10 then
               Status := Syntax_Error;
               return;
            end if;
            Value := Value * 10 + Digit;
            Pos := Pos + 1;
         end loop;
         if not Found then
            Status := Syntax_Error;
         end if;
      end Number;

      procedure Class_Byte (C : out Character)
      with
        Pre  => Pos <= Pattern'Length,
        Post =>
          Pos in Pos'Old .. Pattern'Length
          and then (if Pos'Old < Pattern'Length then Pos > Pos'Old)
      is
      begin
         C := Peek;
         if Pos >= Pattern'Length then
            Status := Syntax_Error;
            return;
         end if;
         Pos := Pos + 1;
         if C = '\' then
            if Pos >= Pattern'Length then
               Status := Syntax_Error;
               return;
            end if;
            C := Peek;
            Pos := Pos + 1;
         elsif C = '[' and then Peek in ':' | '.' | '=' then
            Status := Syntax_Error;
         end if;
      end Class_Byte;

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
          and Links_Valid (Result)
          and Result.Count >= Result.Count'Old
          and Id <= Result.Count
          and (if Status = Success then Id > 0)
      is
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
        (Id : Node_Id; Next : State_Id; Entry_State : out State_Id)
      with
        Subprogram_Variant => (Decreases => Id),
        Pre                =>
          not Result.Valid and Links_Valid (Result) and Next <= Result.Count,
        Post               =>
          not Result.Valid
          and (if Status'Old /= Success then Status = Status'Old)
          and Links_Valid (Result)
          and Result.Count >= Result.Count'Old
          and Entry_State <= Result.Count
          and (if Status = Success and Next > 0 then Entry_State > 0)
      is
         A, B, S : State_Id;
         N       : Node;
      begin
         Entry_State := 0;
         if Status /= Success then
            return;
         end if;
         if Id = 0 then
            Status := Syntax_Error;
            return;
         end if;
         if Expansions = 65_536 then
            Status := Expansion_Limit;
            return;
         end if;
         Expansions := Expansions + 1;
         N := Nodes (Id);
         --  Check the tree ordering locally, including on every recursive edge.
         if N.Left >= Id or else N.Right >= Id then
            Status := Syntax_Error;
            return;
         end if;
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
               Build (N.Left, A, Entry_State);

            when Alt_Node    =>
               Build (N.Left, Next, A);
               Build (N.Right, Next, B);
               Emit (Split, A, B, Entry_State);

            when Repeat_Node =>
               A := Next;
               if N.Unlimited then
                  Emit (Split, 0, Next, S);
                  Build (N.Left, S, B);
                  if S /= 0 then
                     Result.Code (S).Next_1 := B;
                  end if;
                  A := S;
               elsif N.Low <= N.High then
                  for K in 1 .. N.High - N.Low loop
                     pragma
                       Loop_Invariant
                         (not Result.Valid and Links_Valid (Result));
                     pragma
                       Loop_Invariant
                         (Result.Count >= Result.Count'Loop_Entry);
                     pragma Loop_Invariant (A <= Result.Count);
                     pragma
                       Loop_Invariant
                         (if Status = Success and Next > 0 then A > 0);
                     Build (N.Left, A, B);
                     Emit (Split, B, A, S);
                     A := S;
                  end loop;
               end if;
               for K in 1 .. N.Low loop
                  pragma
                    Loop_Invariant (not Result.Valid and Links_Valid (Result));
                  pragma
                    Loop_Invariant (Result.Count >= Result.Count'Loop_Entry);
                  pragma Loop_Invariant (A <= Result.Count);
                  pragma
                    Loop_Invariant
                      (if Status = Success and Next > 0 then A > 0);
                  Build (N.Left, A, B);
                  A := B;
               end loop;
               Entry_State := A;
         end case;
      end Build;

   begin
      Result := (others => <>);
      Status := Success;
      if Pattern'Length > Max_Pattern_Length then
         Status := Pattern_Too_Long;
         return;
      end if;
      while Pos < Pattern'Length and then Status = Success loop
         pragma Loop_Invariant (Pos in Pos'Loop_Entry .. Pattern'Length);
         pragma Loop_Variant (Decreases => Pattern'Length - Pos);
         declare
            C  : constant Character := Peek;
            N  : Node;
            Id : Node_Id;
         begin
            Pos := Pos + 1;
            case C is
               when '('                   =>
                  Flush_Atom;
                  if Top = Max_Nodes then
                     Status := Node_Limit;
                  else
                     Top := Top + 1;
                     Frames (Top) := (others => <>);
                  end if;

               when ')'                   =>
                  if Top = 1 then
                     Status := Syntax_Error;
                  else
                     Flush_Term;
                     Id := Frames (Top).Expr;
                     Top := Top - 1;
                     Frames (Top).Atom := Id;
                  end if;

               when '|'                   =>
                  Flush_Term;

               when '*' | '+' | '?' | '{' =>
                  if Frames (Top).Atom = 0 or else Frames (Top).Quantified then
                     Status := Syntax_Error;
                  else
                     N.Kind := Repeat_Node;
                     N.Left := Frames (Top).Atom;
                     case C is
                        when '*'    =>
                           N.Unlimited := True;

                        when '+'    =>
                           N.Low := 1;
                           N.Unlimited := True;

                        when '?'    =>
                           N.High := 1;

                        when others =>
                           Number (N.Low);
                           N.High := N.Low;
                           if Peek = ',' and then Pos < Pattern'Length then
                              Pos := Pos + 1;
                              if Peek = '}' then
                                 N.Unlimited := True;
                              else
                                 Number (N.High);
                              end if;
                           end if;
                           if Pos >= Pattern'Length
                             or else Peek /= '}'
                             or else (not N.Unlimited and then N.High < N.Low)
                           then
                              Status := Syntax_Error;
                           else
                              Pos := Pos + 1;
                           end if;
                     end case;
                     Add (N, Id);
                     Frames (Top).Atom := Id;
                     Frames (Top).Quantified := True;
                  end if;

               when '}' | ']'             =>
                  Status := Syntax_Error;

               when others                =>
                  Flush_Atom;
                  N.Kind := Bytes_Node;
                  if C = '^' then
                     N.Kind := Start_Node;
                  elsif C = '$' then
                     N.Kind := End_Node;
                  elsif C = '.' then
                     N.Bytes := [others => True];
                  elsif C = '[' then
                     declare
                        Negated : Boolean := False;
                        First   : Boolean := True;
                        Lo, Hi  : Character;
                     begin
                        if Pos < Pattern'Length and then Peek = '^' then
                           Negated := True;
                           Pos := Pos + 1;
                        end if;
                        while Pos < Pattern'Length
                          and then Status = Success
                          and then (First or else Peek /= ']')
                        loop
                           pragma
                             Loop_Invariant
                               (Pos in Pos'Loop_Entry .. Pattern'Length);
                           pragma
                             Loop_Variant (Decreases => Pattern'Length - Pos);
                           Class_Byte (Lo);
                           Hi := Lo;
                           First := False;
                           if Pos < Pattern'Length
                             and then Peek = '-'
                             and then Pos < Pattern'Length - 1
                             and then Pattern (Pattern'First + Pos + 1) /= ']'
                           then
                              Pos := Pos + 1;
                              Class_Byte (Hi);
                              if Hi < Lo then
                                 Status := Syntax_Error;
                              end if;
                           end if;
                           for B in Lo .. Hi loop
                              N.Bytes (B) := True;
                           end loop;
                        end loop;
                        if Pos >= Pattern'Length or else Peek /= ']' then
                           Status := Syntax_Error;
                        else
                           Pos := Pos + 1;
                        end if;
                        if Negated then
                           for B in Character loop
                              N.Bytes (B) := not N.Bytes (B);
                           end loop;
                        end if;
                     end;
                  elsif C = '\' then
                     if Pos >= Pattern'Length then
                        Status := Syntax_Error;
                     elsif Peek
                           not in '\'
                                | '.'
                                | '^'
                                | '$'
                                | '|'
                                | '?'
                                | '*'
                                | '+'
                                | '('
                                | ')'
                                | '['
                                | ']'
                                | '{'
                                | '}'
                                | '-'
                     then
                        Status := Syntax_Error;
                     else
                        N.Bytes (Peek) := True;
                        Pos := Pos + 1;
                     end if;
                  else
                     N.Bytes (C) := True;
                  end if;
                  Add (N, Id);
                  Frames (Top).Atom := Id;
            end case;
         end;
      end loop;
      if Status = Success then
         if Top /= 1 then
            Status := Syntax_Error;
         else
            Flush_Term;
            Root := Frames (1).Expr;
            declare
               Final, Entry_State : State_Id;
            begin
               Emit (Accept_State, 0, 0, Final);
               Build (Root, Final, Entry_State);
               pragma Assert (Expansions <= 65_536);
               Result.Start := Entry_State;
            end;
         end if;
      end if;
      Result.Valid := Status = Success;
   end Compile;

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
             (for all Target in 0 .. Self.Count =>
                After (Target)
                = (for some Source in 1 .. Id =>
                     Consumes_To (Self, Before, Byte, Source, Target)));
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
      Pending : Links := [others => 0];
      Head    : State_Id := 0;
      S       : State_Id;
      type Depth_Array is array (State_Id) of Natural;
      Parents : Links := [others => 0]
      with Ghost;
      Depth   : Depth_Array := [others => 0]
      with Ghost;
      Limit   : Natural range 0 .. Max_States := 0
      with Ghost;

      --  A finite path certificate: every nonseed reached state has a reached
      --  epsilon predecessor of strictly smaller depth. Following predecessors
      --  must therefore terminate at a seed. Anchors are checked on each edge.
      function Certified return Boolean
      is (for all Id in 1 .. Self.Count =>
            (if Reached (Id)
             then
               (if Seeds (Id)
                then Depth (Id) = 0
                else
                  Parents (Id) in 1 .. Self.Count
                  and then Reached (Parents (Id))
                  and then Depth (Parents (Id)) < Depth (Id)
                  and then
                    Epsilon_Edge (Self, Parents (Id), Id, At_First, At_Last))))
      with Ghost;
      function Bounded_Depth return Boolean
      is (for all Id in 1 .. Self.Count =>
            (if Reached (Id) then Depth (Id) <= Limit))
      with Ghost;
      function Queue_Valid return Boolean
      is (Head <= Self.Count
          and then (Head = 0 or else Reached (Head))
          and then
            (for all Id in 1 .. Self.Count =>
               Pending (Id) <= Self.Count
               and then (Pending (Id) = 0 or else Reached (Pending (Id)))))
      with Ghost;

      procedure Push (Id : State_Id; From : State_Id)
      with
        Pre  =>
          not Reached (0)
          and Certified
          and Queue_Valid
          and Bounded_Depth
          and Id <= Self.Count
          and
            (Id = 0
             or else Seeds (Id)
             or else
               (From in 1 .. Self.Count
                and then Reached (From)
                and then Depth (From) < Limit
                and then Epsilon_Edge (Self, From, Id, At_First, At_Last))),
        Post =>
          Certified
          and Queue_Valid
          and Bounded_Depth
          and not Reached (0)
          and
            (for all K in 1 .. Self.Count =>
               (if Reached'Old (K)
                then Reached (K) and Depth (K) = Depth'Old (K)))
          and (if Id /= 0 then Reached (Id))
      is
      begin
         if Id /= 0 and then not Reached (Id) then
            if Seeds (Id) then
               Depth (Id) := 0;
               Parents (Id) := 0;
            else
               Depth (Id) := Depth (From) + 1;
               Parents (Id) := From;
            end if;
            Reached (Id) := True;
            Pending (Id) := Head;
            Head := Id;
         end if;
      end Push;
   begin
      Reached := [others => False];
      for Id in 1 .. Self.Count loop
         if Seeds (Id) then
            Push (Id, 0);
         end if;
         pragma Loop_Invariant (Certified and Queue_Valid and Bounded_Depth);
         pragma Loop_Invariant (not Reached (0));
         pragma Loop_Invariant (Limit = 0);
         pragma
           Loop_Invariant
             (for all K in 1 .. Id => (if Seeds (K) then Reached (K)));
      end loop;
      --  Each state is enqueued at most once. The fixed iteration budget also
      --  makes termination explicit for cyclic epsilon graphs such as (a*)*.
      for Iteration in 1 .. Self.Count loop
         pragma Loop_Invariant (Certified and Queue_Valid and Bounded_Depth);
         pragma Loop_Invariant (not Reached (0));
         pragma Loop_Invariant (Limit = Iteration - 1);
         pragma
           Loop_Invariant
             (for all K in 1 .. Self.Count => (if Seeds (K) then Reached (K)));
         exit when Head = 0;
         S := Head;
         Head := Pending (S);
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
      end loop;
      pragma Assert (Certified);
   end Closure;

   function Run (Self : Program; Text : String; Whole : Boolean) return Boolean
   with
     Pre  => Internal_Valid (Self),
     Post => (if not Self.Valid then not Run'Result)
   is
      Current : State_Set;
      Seeds   : State_Set := [others => False];
   begin
      if not Self.Valid then
         return False;
      end if;
      Seeds (Self.Start) := True;
      Closure (Self, Seeds, True, Text'Length = 0, Current);
      for Offset in 0 .. Text'Length loop
         if not Whole or else Offset = Text'Length then
            for Id in 1 .. Self.Count loop
               if Current (Id) and then Self.Code (Id).Op = Accept_State then
                  return True;
               end if;
            end loop;
         end if;
         exit when Offset = Text'Length;
         Advance (Self, Current, Text (Text'First + Offset), Seeds);
         if not Whole then
            Seeds (Self.Start) := True;
         end if;
         Closure (Self, Seeds, False, Offset = Text'Length - 1, Current);
      end loop;
      return False;
   end Run;

   function Search (Self : Program; Text : String) return Boolean
   is (Run (Self, Text, False));
   function Full_Match (Self : Program; Text : String) return Boolean
   is (Run (Self, Text, True));
end Spark_Re;

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
         pragma
           Postcondition
             (Static =>
                (for all K in 1 .. Result.Count'Old =>
                   Result.Code (K) = Result.Code'Old (K)));
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
                     pragma
                       Loop_Invariant
                         (Static =>
                            (for all J in 1 .. Result.Count'Loop_Entry =>
                               Result.Code (J) = Result.Code'Loop_Entry (J)));
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
                  pragma
                    Loop_Invariant
                      (Static =>
                         (for all J in 1 .. Result.Count'Loop_Entry =>
                            Result.Code (J) = Result.Code'Loop_Entry (J)));
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
end Spark_Re;

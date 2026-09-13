package body Spark_Re_Trees.Parsing
  with SPARK_Mode
is

   type Frame is record
      Expr, Term, Atom : Node_Id := 0;
      Quantified       : Boolean := False;
   end record;
   type Frame_Array is array (Live_Node) of Frame;

   --  Lexical grammar over half-open pattern spans. These definitions read
   --  pattern bytes directly; they never call the parser or its scanners.
   function Byte_At (Pattern : String; Pos : Natural) return Character
   is (Pattern (Pattern'First + Pos))
   with Pre => Pos < Pattern'Length;

   function Decimal_Digits
     (Pattern : String; First, Last : Natural) return Boolean
   is (for all K in First .. Last - 1 => Byte_At (Pattern, K) in '0' .. '9')
   with Ghost => Static, Pre => First <= Last and Last <= Pattern'Length;

   --  Saturation records overflow without imposing a machine-integer bound
   --  on the mathematical decimal numeral represented by the pattern.
   function Decimal_Value
     (Pattern : String; First, Last : Natural) return Natural
   is (if First = Last
       then 0
       else
         Natural'Min
           (Max_Repetition + 1,
            10
            * Decimal_Value (Pattern, First, Last - 1)
            + Character'Pos (Byte_At (Pattern, Last - 1))
            - Character'Pos ('0')))
   with
     Ghost              => Static,
     Pre                =>
       First <= Last
       and then Last <= Pattern'Length
       and then Decimal_Digits (Pattern, First, Last),
     Post               => Decimal_Value'Result <= Max_Repetition + 1,
     Subprogram_Variant => (Decreases => Last - First);

   function Number_Syntax
     (Pattern : String; First, Last, Value : Natural) return Boolean
   is (First < Last
       and then Last <= Pattern'Length
       and then Decimal_Digits (Pattern, First, Last)
       and then Decimal_Value (Pattern, First, Last) = Value
       and then Value <= Max_Repetition
       and then
         (Last = Pattern'Length
          or else Byte_At (Pattern, Last) not in '0' .. '9'))
   with Ghost => Static;

   function Number_Error
     (Pattern : String; First, Stop : Natural) return Boolean
   is ((First = Stop
        and then
          (Stop = Pattern'Length
           or else Byte_At (Pattern, Stop) not in '0' .. '9'))
       or else
         (Stop < Pattern'Length
          and then Decimal_Digits (Pattern, First, Stop + 1)
          and then Decimal_Value (Pattern, First, Stop + 1) > Max_Repetition))
   with Ghost => Static, Pre => First <= Stop and Stop <= Pattern'Length;

   function Numeral_End (Pattern : String; First : Natural) return Natural
   is (if First < Pattern'Length
         and then Byte_At (Pattern, First) in '0' .. '9'
       then Numeral_End (Pattern, First + 1)
       else First)
   with
     Ghost              => Static,
     Annotate           => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Pre                => First <= Pattern'Length,
     Post               =>
       Numeral_End'Result in First .. Pattern'Length
       and then Decimal_Digits (Pattern, First, Numeral_End'Result)
       and then
         (Numeral_End'Result = Pattern'Length
          or else Byte_At (Pattern, Numeral_End'Result) not in '0' .. '9'),
     Subprogram_Variant => (Decreases => Pattern'Length - First);

   procedure Lemma_Numeral_Step (Pattern : String; First : Natural)
   with
     Ghost => Static,
     Pre   => First <= Pattern'Length,
     Post  =>
       (if First < Pattern'Length
          and then Byte_At (Pattern, First) in '0' .. '9'
        then Numeral_End (Pattern, First) = Numeral_End (Pattern, First + 1)
        else Numeral_End (Pattern, First) = First)
   is
      pragma
        Annotate
          (GNATprove, Unhide_Info, "Expression_Function_Body", Numeral_End);
   begin
      null;
   end Lemma_Numeral_Step;

   function Numeral_Value (Pattern : String; First : Natural) return Natural
   is (Decimal_Value (Pattern, First, Numeral_End (Pattern, First)))
   with
     Ghost => Static,
     Pre   => First <= Pattern'Length,
     Post  => Numeral_Value'Result <= Max_Repetition + 1;

   function Numeral_Valid (Pattern : String; First : Natural) return Boolean
   is (First < Numeral_End (Pattern, First)
       and then Numeral_Value (Pattern, First) <= Max_Repetition)
   with Ghost => Static, Pre => First <= Pattern'Length;

   procedure Lemma_Decimal_Saturated
     (Pattern : String; First, Middle, Last : Natural)
   with
     Ghost              => Static,
     Pre                =>
       First <= Middle
       and then Middle <= Last
       and then Last <= Pattern'Length
       and then Decimal_Digits (Pattern, First, Last)
       and then Decimal_Value (Pattern, First, Middle) = Max_Repetition + 1,
     Post               =>
       Decimal_Value (Pattern, First, Last) = Max_Repetition + 1,
     Subprogram_Variant => (Decreases => Last - Middle)
   is
   begin
      if Middle < Last then
         Lemma_Decimal_Saturated (Pattern, First, Middle, Last - 1);
      end if;
   end Lemma_Decimal_Saturated;

   procedure Scan_Number
     (Pattern : String;
      Pos     : in out Natural;
      Value   : out Natural;
      Status  : out Compile_Status)
   with
     Pre  => Pos <= Pattern'Length,
     Post =>
       Value <= Max_Repetition
       and Pos in Pos'Old .. Pattern'Length
       and Status in Success | Syntax_Error
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Numeral_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then
                  Pos = Numeral_End (Pattern, Pos'Old)
                  and then Number_Syntax (Pattern, Pos'Old, Pos, Value)
                else Number_Error (Pattern, Pos'Old, Pos)));
      First  : constant Natural := Pos
      with Ghost => Static;
      Finish : constant Natural := Numeral_End (Pattern, Pos)
      with Ghost => Static;
      Digit  : Natural;
      Found  : Boolean := False;
   begin
      Status := Success;
      Value := 0;
      while Pos < Pattern'Length and then Byte_At (Pattern, Pos) in '0' .. '9'
      loop
         pragma Loop_Invariant (Value <= Max_Repetition);
         pragma Loop_Invariant (Pos in Pos'Loop_Entry .. Pattern'Length);
         pragma Loop_Invariant (Found = (Pos > Pos'Loop_Entry));
         pragma
           Loop_Invariant
             (Static =>
                Pos <= Finish
                and then Decimal_Digits (Pattern, First, Finish));
         pragma
           Loop_Invariant
             (Static =>
                Decimal_Digits (Pattern, First, Pos)
                and then Decimal_Value (Pattern, First, Pos) = Value);
         pragma Loop_Invariant (Static => Finish = Numeral_End (Pattern, Pos));
         pragma Loop_Variant (Decreases => Pattern'Length - Pos);
         Lemma_Numeral_Step (Pattern, Pos);
         pragma Assert (Static => Decimal_Digits (Pattern, First, Pos + 1));
         Found := True;
         Digit := Character'Pos (Byte_At (Pattern, Pos)) - Character'Pos ('0');
         if Value > (Max_Repetition - Digit) / 10 then
            Lemma_Decimal_Saturated (Pattern, First, Pos + 1, Finish);
            Status := Syntax_Error;
            return;
         end if;
         Value := Value * 10 + Digit;
         Pos := Pos + 1;
      end loop;
      Lemma_Numeral_Step (Pattern, Pos);
      if not Found then
         Status := Syntax_Error;
      end if;
   end Scan_Number;

   function Class_Unit_Valid (Pattern : String; First : Natural) return Boolean
   is (First < Pattern'Length
       and then
         (if Byte_At (Pattern, First) = '\'
          then First < Pattern'Length - 1
          else
            not (Byte_At (Pattern, First) = '['
                 and then First < Pattern'Length - 1
                 and then Byte_At (Pattern, First + 1) in ':' | '.' | '=')))
   with Ghost => Static, Pre => First <= Pattern'Length;

   function Class_Unit_End (Pattern : String; First : Natural) return Natural
   is (First + (if Byte_At (Pattern, First) = '\' then 2 else 1))
   with
     Ghost => Static,
     Pre   =>
       First <= Pattern'Length and then Class_Unit_Valid (Pattern, First),
     Post  => Class_Unit_End'Result in First + 1 .. Pattern'Length;

   function Class_Unit_Byte
     (Pattern : String; First : Natural) return Character
   is (Byte_At (Pattern, Class_Unit_End (Pattern, First) - 1))
   with
     Ghost => Static,
     Pre   =>
       First <= Pattern'Length and then Class_Unit_Valid (Pattern, First);

   procedure Scan_Class_Byte
     (Pattern : String;
      Pos     : in out Natural;
      C       : out Character;
      Status  : out Compile_Status)
   with
     Pre  => Pos <= Pattern'Length,
     Post =>
       Pos in Pos'Old .. Pattern'Length
       and then (if Pos'Old < Pattern'Length then Pos > Pos'Old)
       and then Status in Success | Syntax_Error
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Class_Unit_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then
                  Pos = Class_Unit_End (Pattern, Pos'Old)
                  and C = Class_Unit_Byte (Pattern, Pos'Old)));
   begin
      Status := Success;
      C := Character'Val (0);
      if Pos >= Pattern'Length then
         Status := Syntax_Error;
         return;
      end if;
      C := Byte_At (Pattern, Pos);
      Pos := Pos + 1;
      if C = '\' then
         if Pos >= Pattern'Length then
            Status := Syntax_Error;
            return;
         end if;
         C := Byte_At (Pattern, Pos);
         Pos := Pos + 1;
      elsif C = '['
        and then Pos < Pattern'Length
        and then Byte_At (Pattern, Pos) in ':' | '.' | '='
      then
         Status := Syntax_Error;
      end if;
   end Scan_Class_Byte;

   function Range_Follows (Pattern : String; Pos : Natural) return Boolean
   is (Pos < Pattern'Length
       and then Byte_At (Pattern, Pos) = '-'
       and then Pos < Pattern'Length - 1
       and then Byte_At (Pattern, Pos + 1) /= ']')
   with Pre => Pos <= Pattern'Length;

   function Class_Piece_Valid
     (Pattern : String; First : Natural) return Boolean
   is (Class_Unit_Valid (Pattern, First)
       and then
         (if Range_Follows (Pattern, Class_Unit_End (Pattern, First))
          then
            Class_Unit_Valid (Pattern, Class_Unit_End (Pattern, First) + 1)
            and then
              Class_Unit_Byte (Pattern, First)
              <= Class_Unit_Byte
                   (Pattern, Class_Unit_End (Pattern, First) + 1)))
   with Ghost => Static, Pre => First <= Pattern'Length;

   function Class_Piece_End (Pattern : String; First : Natural) return Natural
   is (if Range_Follows (Pattern, Class_Unit_End (Pattern, First))
       then Class_Unit_End (Pattern, Class_Unit_End (Pattern, First) + 1)
       else Class_Unit_End (Pattern, First))
   with
     Ghost => Static,
     Pre   =>
       First <= Pattern'Length and then Class_Piece_Valid (Pattern, First),
     Post  => Class_Piece_End'Result in First + 1 .. Pattern'Length;

   function Class_Piece_High
     (Pattern : String; First : Natural) return Character
   is (if Range_Follows (Pattern, Class_Unit_End (Pattern, First))
       then Class_Unit_Byte (Pattern, Class_Unit_End (Pattern, First) + 1)
       else Class_Unit_Byte (Pattern, First))
   with
     Ghost => Static,
     Pre   =>
       First <= Pattern'Length and then Class_Piece_Valid (Pattern, First);

   procedure Scan_Class_Piece
     (Pattern : String;
      Pos     : in out Natural;
      Lo, Hi  : out Character;
      Status  : out Compile_Status)
   with
     Pre  => Pos <= Pattern'Length,
     Post =>
       Pos in Pos'Old .. Pattern'Length
       and then (if Pos'Old < Pattern'Length then Pos > Pos'Old)
       and then Status in Success | Syntax_Error
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Class_Piece_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then
                  Pos = Class_Piece_End (Pattern, Pos'Old)
                  and Lo = Class_Unit_Byte (Pattern, Pos'Old)
                  and Hi = Class_Piece_High (Pattern, Pos'Old)));
   begin
      Scan_Class_Byte (Pattern, Pos, Lo, Status);
      Hi := Lo;
      if Status /= Success then
         return;
      end if;
      if Range_Follows (Pattern, Pos) then
         Pos := Pos + 1;
         Scan_Class_Byte (Pattern, Pos, Hi, Status);
         if Hi < Lo then
            Status := Syntax_Error;
         end if;
      end if;
   end Scan_Class_Piece;

   --  A class is a nonempty sequence of pieces followed by an unescaped ].
   --  Only the first piece can start with an unescaped ]. Each piece is one
   --  escaped/literal byte or an ordered range; named classes are excluded.
   function Class_Tail_Valid
     (Pattern : String; Pos : Natural; Initial : Boolean) return Boolean
   is (Pos < Pattern'Length
       and then
         (if not Initial and then Byte_At (Pattern, Pos) = ']'
          then True
          else
            Class_Piece_Valid (Pattern, Pos)
            and then
              Class_Tail_Valid
                (Pattern, Class_Piece_End (Pattern, Pos), False)))
   with
     Ghost              => Static,
     Pre                => Pos <= Pattern'Length,
     Subprogram_Variant => (Decreases => Pattern'Length - Pos);

   function Class_Tail_End
     (Pattern : String; Pos : Natural; Initial : Boolean) return Natural
   is (if not Initial and then Byte_At (Pattern, Pos) = ']'
       then Pos + 1
       else Class_Tail_End (Pattern, Class_Piece_End (Pattern, Pos), False))
   with
     Ghost              => Static,
     Pre                =>
       Pos <= Pattern'Length and then Class_Tail_Valid (Pattern, Pos, Initial),
     Post               => Class_Tail_End'Result in Pos + 1 .. Pattern'Length,
     Subprogram_Variant => (Decreases => Pattern'Length - Pos);

   function Class_Tail_Has
     (Pattern : String; Pos : Natural; Initial : Boolean; B : Character)
      return Boolean
   is (if not Initial and then Byte_At (Pattern, Pos) = ']'
       then False
       else
         B in Class_Unit_Byte (Pattern, Pos) .. Class_Piece_High (Pattern, Pos)
         or else
           Class_Tail_Has (Pattern, Class_Piece_End (Pattern, Pos), False, B))
   with
     Ghost              => Static,
     Pre                =>
       Pos <= Pattern'Length and then Class_Tail_Valid (Pattern, Pos, Initial),
     Subprogram_Variant => (Decreases => Pattern'Length - Pos);

   function Class_Negated (Pattern : String; First : Natural) return Boolean
   is (First < Pattern'Length - 1 and then Byte_At (Pattern, First + 1) = '^')
   with Ghost => Static, Pre => First < Pattern'Length;

   function Class_Body (Pattern : String; First : Natural) return Natural
   is (First + (if Class_Negated (Pattern, First) then 2 else 1))
   with
     Ghost => Static,
     Pre   => First < Pattern'Length,
     Post  => Class_Body'Result in First + 1 .. Pattern'Length;

   function Class_Valid (Pattern : String; First : Natural) return Boolean
   is (First < Pattern'Length
       and then Byte_At (Pattern, First) = '['
       and then Class_Tail_Valid (Pattern, Class_Body (Pattern, First), True))
   with Ghost => Static, Pre => First <= Pattern'Length;

   function Class_Syntax
     (Pattern : String; First, Last : Natural; Bytes : Byte_Set) return Boolean
   is (Class_Valid (Pattern, First)
       and then
         Last = Class_Tail_End (Pattern, Class_Body (Pattern, First), True)
       and then
         (for all B in Character =>
            Bytes (B)
            = (Class_Tail_Has (Pattern, Class_Body (Pattern, First), True, B)
               /= Class_Negated (Pattern, First))))
   with Ghost => Static, Pre => First <= Pattern'Length;

   procedure Scan_Class
     (Pattern : String;
      Pos     : in out Natural;
      Bytes   : out Byte_Set;
      Status  : out Compile_Status)
   with
     Pre  => Pos < Pattern'Length and then Byte_At (Pattern, Pos) = '[',
     Post =>
       Pos in Pos'Old + 1 .. Pattern'Length
       and Status in Success | Syntax_Error
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Class_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then Class_Syntax (Pattern, Pos'Old, Pos, Bytes)));
      Start   : constant Natural := Pos
      with Ghost => Static;
      Negated : Boolean := False;
      Initial : Boolean := True;
      Lo, Hi  : Character;
   begin
      Bytes := [others => False];
      Status := Success;
      Pos := Pos + 1;
      if Pos < Pattern'Length and then Byte_At (Pattern, Pos) = '^' then
         Negated := True;
         Pos := Pos + 1;
      end if;
      while Pos < Pattern'Length
        and then (Initial or else Byte_At (Pattern, Pos) /= ']')
      loop
         pragma Loop_Invariant (Pos in Pos'Loop_Entry .. Pattern'Length);
         pragma
           Loop_Invariant (Static => Negated = Class_Negated (Pattern, Start));
         pragma
           Loop_Invariant
             (Static =>
                Class_Valid (Pattern, Start)
                = Class_Tail_Valid (Pattern, Pos, Initial));
         pragma
           Loop_Invariant
             (Static =>
                (if Class_Valid (Pattern, Start)
                 then
                   Class_Tail_End (Pattern, Class_Body (Pattern, Start), True)
                   = Class_Tail_End (Pattern, Pos, Initial)
                   and then
                     (for all B in Character =>
                        Class_Tail_Has
                          (Pattern, Class_Body (Pattern, Start), True, B)
                        = (Bytes (B)
                           or Class_Tail_Has (Pattern, Pos, Initial, B)))));
         pragma Loop_Variant (Decreases => Pattern'Length - Pos);
         declare
            Before    : constant Natural := Pos
            with Ghost => Static;
            Old_Bytes : constant Byte_Set := Bytes
            with Ghost => Static;
         begin
            Scan_Class_Piece (Pattern, Pos, Lo, Hi, Status);
            if Status /= Success then
               return;
            end if;
            Initial := False;
            for B in Lo .. Hi loop
               pragma
                 Loop_Invariant
                   (Static =>
                      (for all C in Character =>
                         Bytes (C)
                         = (Old_Bytes (C) or (C < B and C in Lo .. Hi))));
               Bytes (B) := True;
            end loop;
            pragma Assert (Static => Class_Piece_End (Pattern, Before) = Pos);
         end;
      end loop;
      if Pos >= Pattern'Length then
         Status := Syntax_Error;
      else
         Pos := Pos + 1;
         if Negated then
            for B in Character loop
               pragma
                 Loop_Invariant
                   (Static =>
                      (for all C in Character =>
                         Bytes (C)
                         = (Class_Tail_Has
                              (Pattern, Class_Body (Pattern, Start), True, C)
                            /= (C < B))));
               Bytes (B) := not Bytes (B);
            end loop;
         end if;
      end if;
   end Scan_Class;

   function Bounds_Valid (Pattern : String; First : Natural) return Boolean
   is (declare
         Sep : constant Natural := Numeral_End (Pattern, First);
       begin
         Numeral_Valid (Pattern, First)
         and then Sep < Pattern'Length
         and then
           (if Byte_At (Pattern, Sep) = '}'
            then True
            elsif Byte_At (Pattern, Sep) /= ','
              or else Sep = Pattern'Length - 1
            then False
            elsif Byte_At (Pattern, Sep + 1) = '}'
            then True
            else
              Numeral_Valid (Pattern, Sep + 1)
              and then Numeral_End (Pattern, Sep + 1) < Pattern'Length
              and then Byte_At (Pattern, Numeral_End (Pattern, Sep + 1)) = '}'
              and then
                Numeral_Value (Pattern, First)
                <= Decimal_Value
                     (Pattern, Sep + 1, Numeral_End (Pattern, Sep + 1))))
   with Ghost => Static, Pre => First <= Pattern'Length;
   --  Every digit span here is one that Numeral_End's postcondition already
   --  certifies, so match that certificate rather than expanding it per byte.
   pragma
     Annotate
       (GNATprove, Hide_Info, "Expression_Function_Body", Decimal_Digits);

   function Quantifier_Valid (Pattern : String; First : Natural) return Boolean
   is (First < Pattern'Length
       and then
         (case Byte_At (Pattern, First) is
            when '*' | '+' | '?' => True,
            when '{'             => Bounds_Valid (Pattern, First + 1),
            when others          => False))
   with Ghost => Static, Pre => First <= Pattern'Length;

   type Quantifier_Value is record
      Last      : Natural;
      Low, High : Natural range 0 .. Max_Repetition;
      Unlimited : Boolean;
   end record;

   function Quantifier_Model
     (Pattern : String; First : Natural) return Quantifier_Value
   is (case Byte_At (Pattern, First) is
         when '*'    => (First + 1, 0, 0, True),
         when '+'    => (First + 1, 1, 0, True),
         when '?'    => (First + 1, 0, 1, False),
         when others =>
           (declare
              Sep : constant Natural := Numeral_End (Pattern, First + 1);
              Low : constant Natural := Numeral_Value (Pattern, First + 1);
            begin
              (if Byte_At (Pattern, Sep) = '}'
               then (Sep + 1, Low, Low, False)
               elsif Byte_At (Pattern, Sep + 1) = '}'
               then (Sep + 2, Low, Low, True)
               else
                 (Numeral_End (Pattern, Sep + 1) + 1,
                  Low,
                  Decimal_Value
                    (Pattern, Sep + 1, Numeral_End (Pattern, Sep + 1)),
                  False))))
   with
     Ghost => Static,
     Pre   =>
       First <= Pattern'Length and then Quantifier_Valid (Pattern, First),
     Post  =>
       Quantifier_Model'Result.Last in First + 1 .. Pattern'Length
       and then
         (Quantifier_Model'Result.Unlimited
          or Quantifier_Model'Result.Low <= Quantifier_Model'Result.High);

   procedure Scan_Quantifier
     (Pattern : String;
      Pos     : in out Natural;
      N       : out Node;
      Status  : out Compile_Status)
   with
     Pre  =>
       Pos < Pattern'Length
       and then Byte_At (Pattern, Pos) in '*' | '+' | '?' | '{',
     Post =>
       Pos in Pos'Old + 1 .. Pattern'Length
       and then Status in Success | Syntax_Error
       and then N.Left = 0
       and then N.Right = 0
       and then N.Kind = Repeat_Node
       and then (if Status = Success then N.Unlimited or N.Low <= N.High)
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Quantifier_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then
                  Pos = Quantifier_Model (Pattern, Pos'Old).Last
                  and N.Low = Quantifier_Model (Pattern, Pos'Old).Low
                  and N.High = Quantifier_Model (Pattern, Pos'Old).High
                  and
                    N.Unlimited
                    = Quantifier_Model (Pattern, Pos'Old).Unlimited));
      First : constant Natural := Pos
      with Ghost => Static;
      C     : constant Character := Byte_At (Pattern, Pos);
   begin
      N := (Kind => Repeat_Node, others => <>);
      Status := Success;
      Pos := Pos + 1;
      case C is
         when '*'    =>
            N.Unlimited := True;

         when '+'    =>
            N.Low := 1;
            N.Unlimited := True;

         when '?'    =>
            N.High := 1;

         when others =>
            Scan_Number (Pattern, Pos, N.Low, Status);
            N.High := N.Low;
            if Status /= Success then
               pragma Assert (Static => not Quantifier_Valid (Pattern, First));
               return;
            end if;
            if Pos < Pattern'Length and then Byte_At (Pattern, Pos) = ',' then
               Pos := Pos + 1;
               if Pos < Pattern'Length and then Byte_At (Pattern, Pos) = '}'
               then
                  N.Unlimited := True;
               else
                  Scan_Number (Pattern, Pos, N.High, Status);
                  if Status /= Success then
                     pragma
                       Assert
                         (Static => not Quantifier_Valid (Pattern, First));
                     return;
                  end if;
               end if;
            end if;
            if Pos >= Pattern'Length
              or else Byte_At (Pattern, Pos) /= '}'
              or else (not N.Unlimited and then N.High < N.Low)
            then
               Status := Syntax_Error;
               pragma Assert (Static => not Quantifier_Valid (Pattern, First));
            else
               Pos := Pos + 1;
               pragma Assert (Static => Quantifier_Valid (Pattern, First));
            end if;
      end case;
   end Scan_Quantifier;

   function Escapable (C : Character) return Boolean
   is (C
       in '\'
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
        | '-');

   function Leaf_Valid (Pattern : String; First : Natural) return Boolean
   is (First < Pattern'Length
       and then
         (case Byte_At (Pattern, First) is
            when '['                                                 =>
              Class_Valid (Pattern, First),
            when '\'                                                 =>
              First < Pattern'Length - 1
              and then Escapable (Byte_At (Pattern, First + 1)),
            when '(' | ')' | '|' | '*' | '+' | '?' | '{' | '}' | ']' => False,
            when others                                              => True))
   with Ghost => Static, Pre => First <= Pattern'Length;

   function Leaf_Syntax
     (Pattern : String; First, Last : Natural; N : Node) return Boolean
   is (Leaf_Valid (Pattern, First)
       and then
         (case Byte_At (Pattern, First) is
            when '['    =>
              N.Kind = Bytes_Node
              and then Class_Syntax (Pattern, First, Last, N.Bytes),
            when '^'    => Last = First + 1 and N.Kind = Start_Node,
            when '$'    => Last = First + 1 and N.Kind = End_Node,
            when '.'    =>
              Last = First + 1
              and N.Kind = Bytes_Node
              and N.Bytes = Byte_Set'(others => True),
            when '\'    =>
              Last = First + 2
              and then N.Kind = Bytes_Node
              and then
                (for all B in Character =>
                   N.Bytes (B) = (B = Byte_At (Pattern, First + 1))),
            when others =>
              Last = First + 1
              and then N.Kind = Bytes_Node
              and then
                (for all B in Character =>
                   N.Bytes (B) = (B = Byte_At (Pattern, First)))))
   with Ghost => Static, Pre => First <= Pattern'Length;

   procedure Scan_Leaf
     (Pattern : String;
      Pos     : in out Natural;
      N       : out Node;
      Status  : out Compile_Status)
   with
     Pre  =>
       Pos < Pattern'Length
       and then
         Byte_At (Pattern, Pos)
         not in '(' | ')' | '|' | '*' | '+' | '?' | '{' | '}' | ']',
     Post =>
       Pos in Pos'Old + 1 .. Pattern'Length
       and then Status in Success | Syntax_Error
       and then N.Left = 0
       and then N.Right = 0
       and then N.Kind in Bytes_Node | Start_Node | End_Node
   is
      pragma
        Postcondition
          (Static =>
             (Status = Success) = Leaf_Valid (Pattern, Pos'Old)
             and then
               (if Status = Success
                then Leaf_Syntax (Pattern, Pos'Old, Pos, N)));
      C : constant Character := Byte_At (Pattern, Pos);
   begin
      N := (Kind => Bytes_Node, others => <>);
      Status := Success;
      if C = '[' then
         Scan_Class (Pattern, Pos, N.Bytes, Status);
      else
         Pos := Pos + 1;
         case C is
            when '^'    =>
               N.Kind := Start_Node;

            when '$'    =>
               N.Kind := End_Node;

            when '.'    =>
               N.Bytes := [others => True];

            when '\'    =>
               if Pos >= Pattern'Length
                 or else not Escapable (Byte_At (Pattern, Pos))
               then
                  Status := Syntax_Error;
               else
                  N.Bytes (Byte_At (Pattern, Pos)) := True;
                  Pos := Pos + 1;
               end if;

            when others =>
               N.Bytes (C) := True;
         end case;
      end if;
   end Scan_Leaf;

   function Quantifier_Syntax
     (Pattern : String; First, Last : Natural; N : Node) return Boolean
   is (Quantifier_Valid (Pattern, First)
       and then N.Kind = Repeat_Node
       and then Last = Quantifier_Model (Pattern, First).Last
       and then N.Low = Quantifier_Model (Pattern, First).Low
       and then N.High = Quantifier_Model (Pattern, First).High
       and then N.Unlimited = Quantifier_Model (Pattern, First).Unlimited)
   with Ghost => Static, Pre => First <= Pattern'Length;

   --  A derivation of an expression span in a supplied tree. The grammar
   --  independently states precedence and grouping, and makes no reference
   --  to parser frames, allocation order beyond Tree_Valid, or scanner calls.
   function Grammar
     (Pattern     : String;
      Nodes       : Tree;
      Id          : Live_Node;
      First, Last : Natural;
      Level       : Grammar_Level) return Boolean
   is (case Level is
         when Atom_Grammar   =>
           Leaf_Syntax (Pattern, First, Last, Nodes (Id))
           or else
             (Last - First >= 2
              and then Byte_At (Pattern, First) = '('
              and then Byte_At (Pattern, Last - 1) = ')'
              and then
                Grammar
                  (Pattern, Nodes, Id, First + 1, Last - 1, Expr_Grammar)),
         when Factor_Grammar =>
           Grammar (Pattern, Nodes, Id, First, Last, Atom_Grammar)
           or else
             (Nodes (Id).Kind = Repeat_Node
              and then Last - First >= 2
              and then
                (for some Middle in First + 1 .. Last - 1 =>
                   Grammar
                     (Pattern,
                      Nodes,
                      Nodes (Id).Left,
                      First,
                      Middle,
                      Atom_Grammar)
                   and then
                     Quantifier_Syntax (Pattern, Middle, Last, Nodes (Id)))),
         when Term_Grammar   =>
           (First = Last and Nodes (Id).Kind = Empty_Node)
           or else Grammar (Pattern, Nodes, Id, First, Last, Factor_Grammar)
           or else
             (Nodes (Id).Kind = Concat_Node
              and then First < Last
              and then
                (for some Middle in First .. Last - 1 =>
                   Grammar
                     (Pattern,
                      Nodes,
                      Nodes (Id).Left,
                      First,
                      Middle,
                      Term_Grammar)
                   and then
                     Grammar
                       (Pattern,
                        Nodes,
                        Nodes (Id).Right,
                        Middle,
                        Last,
                        Factor_Grammar))),
         when Expr_Grammar   =>
           Grammar (Pattern, Nodes, Id, First, Last, Term_Grammar)
           or else
             (Nodes (Id).Kind = Alt_Node
              and then First < Last
              and then
                (for some Bar in First .. Last - 1 =>
                   Byte_At (Pattern, Bar) = '|'
                   and then
                     Grammar
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Bar,
                        Expr_Grammar)
                   and then
                     Grammar
                       (Pattern,
                        Nodes,
                        Nodes (Id).Right,
                        Bar + 1,
                        Last,
                        Term_Grammar))));

   --  Continuations consume maximal lexical tokens and track only unmatched
   --  parentheses and whether one postfix quantifier may follow. They do not
   --  inspect trees, parser frames, capacities, or executable scanner results.
   type Pending_Kind is (No_Atom, Plain_Atom, Repeated_Atom);

   function Pending (F : Frame) return Pending_Kind
   is (if F.Atom = 0
       then No_Atom
       elsif F.Quantified
       then Repeated_Atom
       else Plain_Atom)
   with Ghost => Static;

   function Leaf_End (Pattern : String; First : Natural) return Natural
   is (case Byte_At (Pattern, First) is
         when '['    =>
           Class_Tail_End (Pattern, Class_Body (Pattern, First), True),
         when '\'    => First + 2,
         when others => First + 1)
   with
     Ghost => Static,
     Pre   => First <= Pattern'Length and then Leaf_Valid (Pattern, First),
     Post  => Leaf_End'Result in First + 1 .. Pattern'Length;

   function Syntax_Continuation
     (Pattern : String; Pos, Depth : Natural; Pending : Pending_Kind)
      return Boolean
   is (if Pos = Pattern'Length
       then Depth = 0
       else
         (case Byte_At (Pattern, Pos) is
            when '('                   =>
              Syntax_Continuation (Pattern, Pos + 1, Depth + 1, No_Atom),
            when ')'                   =>
              Depth > 0
              and then
                Syntax_Continuation (Pattern, Pos + 1, Depth - 1, Plain_Atom),
            when '|'                   =>
              Syntax_Continuation (Pattern, Pos + 1, Depth, No_Atom),
            when '*' | '+' | '?' | '{' =>
              Pending = Plain_Atom
              and then Quantifier_Valid (Pattern, Pos)
              and then
                Syntax_Continuation
                  (Pattern,
                   Quantifier_Model (Pattern, Pos).Last,
                   Depth,
                   Repeated_Atom),
            when '}' | ']'             => False,
            when others                =>
              Leaf_Valid (Pattern, Pos)
              and then
                Syntax_Continuation
                  (Pattern, Leaf_End (Pattern, Pos), Depth, Plain_Atom)))
   with
     Ghost              => Static,
     Pre                => Depth <= Pos and Pos <= Pattern'Length,
     Subprogram_Variant => (Decreases => Pattern'Length - Pos);

   function Pattern_Valid (Pattern : String) return Boolean
   is (Syntax_Continuation (Pattern, 0, 0, No_Atom));

   --  Atom derivations leave a plain atom; factors may leave a repeated one;
   --  terms and expressions may also be empty. Universal continuation
   --  hypotheses let the induction compose spans without choosing a tree.
   function Can_Follow
     (Pattern : String; Pos, Depth : Natural; Level : Grammar_Level)
      return Boolean
   is (Syntax_Continuation (Pattern, Pos, Depth, Plain_Atom)
       and then
         (if Level /= Atom_Grammar
          then Syntax_Continuation (Pattern, Pos, Depth, Repeated_Atom))
       and then
         (if Level in Term_Grammar | Expr_Grammar
          then Syntax_Continuation (Pattern, Pos, Depth, No_Atom)))
   with Ghost => Static, Pre => Depth <= Pos and Pos <= Pattern'Length;

   procedure Lemma_Grammar_Continuation
     (Pattern            : String;
      Nodes              : Tree;
      Id                 : Live_Node;
      First, Last, Depth : Natural;
      Level              : Grammar_Level)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Nodes)
       and then Depth <= First
       and then First <= Last
       and then Last <= Pattern'Length
       and then Grammar (Pattern, Nodes, Id, First, Last, Level)
       and then Can_Follow (Pattern, Last, Depth, Level),
     Post               =>
       (for all Pending in Pending_Kind =>
          Syntax_Continuation (Pattern, First, Depth, Pending)),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Last - First, Decreases => Level)
   is
   begin
      case Level is
         when Atom_Grammar   =>
            if not Leaf_Syntax (Pattern, First, Last, Nodes (Id)) then
               pragma
                 Assert
                   (Can_Follow (Pattern, Last - 1, Depth + 1, Expr_Grammar));
               Lemma_Grammar_Continuation
                 (Pattern,
                  Nodes,
                  Id,
                  First + 1,
                  Last - 1,
                  Depth + 1,
                  Expr_Grammar);
            else
               pragma Assert (Last = Leaf_End (Pattern, First));
            end if;

         when Factor_Grammar =>
            if Grammar (Pattern, Nodes, Id, First, Last, Atom_Grammar) then
               Lemma_Grammar_Continuation
                 (Pattern, Nodes, Id, First, Last, Depth, Atom_Grammar);
            else
               for Middle in First + 1 .. Last - 1 loop
                  if Grammar
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Middle,
                        Atom_Grammar)
                    and then
                      Quantifier_Syntax (Pattern, Middle, Last, Nodes (Id))
                  then
                     pragma
                       Assert
                         (Can_Follow (Pattern, Middle, Depth, Atom_Grammar));
                     Lemma_Grammar_Continuation
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Middle,
                        Depth,
                        Atom_Grammar);
                     return;
                  end if;
                  pragma
                    Loop_Invariant
                      (for all K in First + 1 .. Middle =>
                         not (Grammar
                                (Pattern,
                                 Nodes,
                                 Nodes (Id).Left,
                                 First,
                                 K,
                                 Atom_Grammar)
                              and then
                                Quantifier_Syntax
                                  (Pattern, K, Last, Nodes (Id))));
               end loop;
            end if;

         when Term_Grammar   =>
            if First = Last and then Nodes (Id).Kind = Empty_Node then
               null;
            elsif Grammar (Pattern, Nodes, Id, First, Last, Factor_Grammar)
            then
               Lemma_Grammar_Continuation
                 (Pattern, Nodes, Id, First, Last, Depth, Factor_Grammar);
            else
               for Middle in First .. Last - 1 loop
                  if Grammar
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Middle,
                        Term_Grammar)
                    and then
                      Grammar
                        (Pattern,
                         Nodes,
                         Nodes (Id).Right,
                         Middle,
                         Last,
                         Factor_Grammar)
                  then
                     Lemma_Grammar_Continuation
                       (Pattern,
                        Nodes,
                        Nodes (Id).Right,
                        Middle,
                        Last,
                        Depth,
                        Factor_Grammar);
                     Lemma_Grammar_Continuation
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Middle,
                        Depth,
                        Term_Grammar);
                     return;
                  end if;
                  pragma
                    Loop_Invariant
                      (for all K in First .. Middle =>
                         not (Grammar
                                (Pattern,
                                 Nodes,
                                 Nodes (Id).Left,
                                 First,
                                 K,
                                 Term_Grammar)
                              and then
                                Grammar
                                  (Pattern,
                                   Nodes,
                                   Nodes (Id).Right,
                                   K,
                                   Last,
                                   Factor_Grammar)));
               end loop;
            end if;

         when Expr_Grammar   =>
            if Grammar (Pattern, Nodes, Id, First, Last, Term_Grammar) then
               Lemma_Grammar_Continuation
                 (Pattern, Nodes, Id, First, Last, Depth, Term_Grammar);
            else
               for Bar in First .. Last - 1 loop
                  if Byte_At (Pattern, Bar) = '|'
                    and then
                      Grammar
                        (Pattern,
                         Nodes,
                         Nodes (Id).Left,
                         First,
                         Bar,
                         Expr_Grammar)
                    and then
                      Grammar
                        (Pattern,
                         Nodes,
                         Nodes (Id).Right,
                         Bar + 1,
                         Last,
                         Term_Grammar)
                  then
                     Lemma_Grammar_Continuation
                       (Pattern,
                        Nodes,
                        Nodes (Id).Right,
                        Bar + 1,
                        Last,
                        Depth,
                        Term_Grammar);
                     pragma
                       Assert (Can_Follow (Pattern, Bar, Depth, Expr_Grammar));
                     Lemma_Grammar_Continuation
                       (Pattern,
                        Nodes,
                        Nodes (Id).Left,
                        First,
                        Bar,
                        Depth,
                        Expr_Grammar);
                     return;
                  end if;
                  pragma
                    Loop_Invariant
                      (for all K in First .. Bar =>
                         not (Byte_At (Pattern, K) = '|'
                              and then
                                Grammar
                                  (Pattern,
                                   Nodes,
                                   Nodes (Id).Left,
                                   First,
                                   K,
                                   Expr_Grammar)
                              and then
                                Grammar
                                  (Pattern,
                                   Nodes,
                                   Nodes (Id).Right,
                                   K + 1,
                                   Last,
                                   Term_Grammar)));
               end loop;
            end if;
      end case;
   end Lemma_Grammar_Continuation;

   procedure Lemma_Grammar_Valid
     (Pattern : String; Nodes : Tree; Id : Live_Node) is
   begin
      Lemma_Grammar_Continuation
        (Pattern, Nodes, Id, 0, Pattern'Length, 0, Expr_Grammar);
   end Lemma_Grammar_Valid;

   procedure Lemma_Grammar_Frame
     (Pattern       : String;
      Before, After : Tree;
      Limit         : Node_Id;
      Id            : Live_Node;
      First, Last   : Natural;
      Level         : Grammar_Level)
   with
     Ghost              => Static,
     Pre                =>
       Tree_Valid (Before)
       and then Tree_Valid (After)
       and then Id <= Limit
       and then First <= Last
       and then Last <= Pattern'Length
       and then (for all K in 1 .. Limit => Before (K) = After (K)),
     Post               =>
       Grammar (Pattern, Before, Id, First, Last, Level)
       = Grammar (Pattern, After, Id, First, Last, Level),
     Subprogram_Variant =>
       (Decreases => Id, Decreases => Last - First, Decreases => Level)
   is
   begin
      pragma Assert (Before (Id) = After (Id));
      case Level is
         when Atom_Grammar   =>
            if Last - First >= 2 then
               Lemma_Grammar_Frame
                 (Pattern,
                  Before,
                  After,
                  Limit,
                  Id,
                  First + 1,
                  Last - 1,
                  Expr_Grammar);
            end if;
            pragma
              Assert
                (Grammar (Pattern, Before, Id, First, Last, Level)
                 = Grammar (Pattern, After, Id, First, Last, Level));

         when Factor_Grammar =>
            Lemma_Grammar_Frame
              (Pattern, Before, After, Limit, Id, First, Last, Atom_Grammar);
            if Before (Id).Kind = Repeat_Node and then Last - First >= 2 then
               for Middle in First + 1 .. Last - 1 loop
                  pragma
                    Loop_Invariant
                      (for all K in First + 1 .. Middle - 1 =>
                         Grammar
                           (Pattern,
                            Before,
                            Before (Id).Left,
                            First,
                            K,
                            Atom_Grammar)
                         = Grammar
                             (Pattern,
                              After,
                              After (Id).Left,
                              First,
                              K,
                              Atom_Grammar));
                  Lemma_Grammar_Frame
                    (Pattern,
                     Before,
                     After,
                     Limit,
                     Before (Id).Left,
                     First,
                     Middle,
                     Atom_Grammar);
               end loop;
            end if;
            pragma
              Assert
                (Grammar (Pattern, Before, Id, First, Last, Level)
                 = Grammar (Pattern, After, Id, First, Last, Level));

         when Term_Grammar   =>
            Lemma_Grammar_Frame
              (Pattern, Before, After, Limit, Id, First, Last, Factor_Grammar);
            if Before (Id).Kind = Concat_Node and then First < Last then
               for Middle in First .. Last - 1 loop
                  pragma
                    Loop_Invariant
                      (for all K in First .. Middle - 1 =>
                         Grammar
                           (Pattern,
                            Before,
                            Before (Id).Left,
                            First,
                            K,
                            Term_Grammar)
                         = Grammar
                             (Pattern,
                              After,
                              After (Id).Left,
                              First,
                              K,
                              Term_Grammar)
                         and
                           Grammar
                             (Pattern,
                              Before,
                              Before (Id).Right,
                              K,
                              Last,
                              Factor_Grammar)
                           = Grammar
                               (Pattern,
                                After,
                                After (Id).Right,
                                K,
                                Last,
                                Factor_Grammar));
                  Lemma_Grammar_Frame
                    (Pattern,
                     Before,
                     After,
                     Limit,
                     Before (Id).Left,
                     First,
                     Middle,
                     Term_Grammar);
                  Lemma_Grammar_Frame
                    (Pattern,
                     Before,
                     After,
                     Limit,
                     Before (Id).Right,
                     Middle,
                     Last,
                     Factor_Grammar);
               end loop;
            end if;
            pragma
              Assert
                (Grammar (Pattern, Before, Id, First, Last, Level)
                 = Grammar (Pattern, After, Id, First, Last, Level));

         when Expr_Grammar   =>
            Lemma_Grammar_Frame
              (Pattern, Before, After, Limit, Id, First, Last, Term_Grammar);
            if Before (Id).Kind = Alt_Node and then First < Last then
               for Bar in First .. Last - 1 loop
                  pragma
                    Loop_Invariant
                      (for all K in First .. Bar - 1 =>
                         Grammar
                           (Pattern,
                            Before,
                            Before (Id).Left,
                            First,
                            K,
                            Expr_Grammar)
                         = Grammar
                             (Pattern,
                              After,
                              After (Id).Left,
                              First,
                              K,
                              Expr_Grammar));
                  pragma
                    Loop_Invariant
                      (for all K in First .. Bar - 1 =>
                         Grammar
                           (Pattern,
                            Before,
                            Before (Id).Right,
                            K + 1,
                            Last,
                            Term_Grammar)
                         = Grammar
                             (Pattern,
                              After,
                              After (Id).Right,
                              K + 1,
                              Last,
                              Term_Grammar));
                  Lemma_Grammar_Frame
                    (Pattern,
                     Before,
                     After,
                     Limit,
                     Before (Id).Left,
                     First,
                     Bar,
                     Expr_Grammar);
                  Lemma_Grammar_Frame
                    (Pattern,
                     Before,
                     After,
                     Limit,
                     Before (Id).Right,
                     Bar + 1,
                     Last,
                     Term_Grammar);
               end loop;
            end if;
            pragma
              Assert
                (Grammar (Pattern, Before, Id, First, Last, Level)
                 = Grammar (Pattern, After, Id, First, Last, Level));
      end case;
   end Lemma_Grammar_Frame;

   type Frame_Span is record
      First, Term_First, Term_Last : Natural := 0;
   end record;
   type Frame_Spans is array (Live_Node) of Frame_Span;

   function Frame_Syntax
     (Pattern : String;
      Nodes   : Tree;
      F       : Frame;
      S       : Frame_Span;
      Last    : Natural) return Boolean
   is (S.First <= S.Term_First
       and then S.Term_First <= S.Term_Last
       and then S.Term_Last <= Last
       and then Last <= Pattern'Length
       and then
         (if F.Expr = 0
          then S.Term_First = S.First
          else
            S.First < S.Term_First
            and then Byte_At (Pattern, S.Term_First - 1) = '|'
            and then
              Grammar
                (Pattern,
                 Nodes,
                 F.Expr,
                 S.First,
                 S.Term_First - 1,
                 Expr_Grammar))
       and then
         (if F.Term = 0
          then S.Term_Last = S.Term_First
          else
            Grammar
              (Pattern,
               Nodes,
               F.Term,
               S.Term_First,
               S.Term_Last,
               Term_Grammar))
       and then
         (if F.Atom = 0
          then S.Term_Last = Last
          else
            Grammar
              (Pattern,
               Nodes,
               F.Atom,
               S.Term_Last,
               Last,
               (if F.Quantified then Factor_Grammar else Atom_Grammar))))
   with Ghost => Static, Pre => Tree_Valid (Nodes);

   procedure Lemma_Frame_Syntax_Frame
     (Pattern       : String;
      Before, After : Tree;
      Limit         : Node_Id;
      F             : Frame;
      S             : Frame_Span;
      Last          : Natural)
   with
     Ghost => Static,
     Pre   =>
       Tree_Valid (Before)
       and then Tree_Valid (After)
       and then F.Expr <= Limit
       and then F.Term <= Limit
       and then F.Atom <= Limit
       and then (for all K in 1 .. Limit => Before (K) = After (K))
       and then Frame_Syntax (Pattern, Before, F, S, Last),
     Post  => Frame_Syntax (Pattern, After, F, S, Last)
   is
   begin
      if F.Expr /= 0 then
         Lemma_Grammar_Frame
           (Pattern,
            Before,
            After,
            Limit,
            F.Expr,
            S.First,
            S.Term_First - 1,
            Expr_Grammar);
      end if;
      if F.Term /= 0 then
         Lemma_Grammar_Frame
           (Pattern,
            Before,
            After,
            Limit,
            F.Term,
            S.Term_First,
            S.Term_Last,
            Term_Grammar);
      end if;
      if F.Atom /= 0 then
         Lemma_Grammar_Frame
           (Pattern,
            Before,
            After,
            Limit,
            F.Atom,
            S.Term_Last,
            Last,
            (if F.Quantified then Factor_Grammar else Atom_Grammar));
      end if;
   end Lemma_Frame_Syntax_Frame;

   procedure Parse
     (Pattern : String;
      Nodes   : out Tree;
      Root    : out Node_Id;
      Status  : out Compile_Status)
   is
      Used   : Node_Id := 0;
      Frames : Frame_Array := [others => <>];
      Top    : Live_Node := 1;
      Pos    : Natural := 0;
      Cursor : Natural := 0
      with Ghost => Static;
      Spans  : Frame_Spans := [others => <>]
      with Ghost => Static;

      function Peek return Character
      is (if Pos < Pattern'Length
          then Pattern (Pattern'First + Pos)
          else Character'Val (0));

      function Frames_Valid return Boolean
      is (for all F in Live_Node =>
            Frames (F).Expr <= Used
            and Frames (F).Term <= Used
            and Frames (F).Atom <= Used)
      with Ghost => Static;

      function Frames_Syntax
        (T : Tree; Include_Top : Boolean := True) return Boolean
      is ((for all F in 1 .. Top =>
             Spans (F).First <= Cursor
             and then
               (if F < Top
                then Frames (F).Atom = 0 and not Frames (F).Quantified)
             and then
               (if F = 1
                then Spans (F).First = 0
                else
                  Spans (F).First > Spans (F - 1).First
                  and then Byte_At (Pattern, Spans (F).First - 1) = '('))
          and then
            (for all F in 1 .. (if Include_Top then Top else Top - 1) =>
               Frame_Syntax
                 (Pattern,
                  T,
                  Frames (F),
                  Spans (F),
                  (if F = Top then Cursor else Spans (F + 1).First - 1))))
      with Ghost => Static, Pre => Tree_Valid (T) and Cursor <= Pattern'Length;

      procedure Preserve_Frames (Before : Tree; Limit : Node_Id)
      with
        Ghost => Static,
        Pre   =>
          Tree_Valid (Before)
          and then Tree_Valid (Nodes)
          and then Cursor <= Pattern'Length
          and then
            (for all F in 1 .. Top =>
               Frames (F).Expr <= Limit
               and Frames (F).Term <= Limit
               and Frames (F).Atom <= Limit)
          and then (for all K in 1 .. Limit => Before (K) = Nodes (K))
          and then Frames_Syntax (Before),
        Post  => Frames_Syntax (Nodes)
      is
      begin
         for F in 1 .. Top loop
            pragma
              Loop_Invariant
                (for all K in 1 .. F - 1 =>
                   Frame_Syntax
                     (Pattern,
                      Nodes,
                      Frames (K),
                      Spans (K),
                      (if K = Top then Cursor else Spans (K + 1).First - 1)));
            Lemma_Frame_Syntax_Frame
              (Pattern,
               Before,
               Nodes,
               Limit,
               Frames (F),
               Spans (F),
               (if F = Top then Cursor else Spans (F + 1).First - 1));
         end loop;
      end Preserve_Frames;

      procedure Add (N : Node; Id : out Node_Id) is
         pragma
           Precondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then Cursor <= Pattern'Length
                and then
                  (if Status = Success
                   then Node_Valid (N, Used) and then Frames_Syntax (Nodes)));
         pragma
           Postcondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then (if Status = Success then Frames_Syntax (Nodes))
                and then Used >= Used'Old
                and then Id <= Used
                and then
                  (if Status = Success
                   then Id = Used and Used = Used'Old + 1 and Nodes (Id) = N)
                and then
                  (for all K in 1 .. Used'Old => Nodes (K) = Nodes'Old (K))
                and then (if Status'Old /= Success then Status = Status'Old)
                and then
                  (if Status'Old = Success
                   then Status in Success | Node_Limit));
         Before : constant Tree := Nodes
         with Ghost => Static;
         Limit  : constant Node_Id := Used
         with Ghost => Static;
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
         Preserve_Frames (Before, Limit);
         Id := Used;
      end Add;

      procedure Flush_Atom is
         pragma
           Precondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then Cursor <= Pattern'Length
                and then (if Status = Success then Frames_Syntax (Nodes)));
         pragma
           Postcondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then Used >= Used'Old
                and then (if Status'Old /= Success then Status = Status'Old)
                and then
                  (if Status'Old = Success then Status in Success | Node_Limit)
                and then Frames (Top).Atom = 0
                and then not Frames (Top).Quantified
                and then Frames (Top).Expr = Frames'Old (Top).Expr
                and then Spans (Top).First = Spans'Old (Top).First
                and then Spans (Top).Term_First = Spans'Old (Top).Term_First
                and then Spans (Top).Term_Last = Cursor
                and then
                  (for all F in Live_Node =>
                     (if F /= Top
                      then
                        Frames (F) = Frames'Old (F)
                        and Spans (F) = Spans'Old (F)))
                and then (if Status = Success then Frames_Syntax (Nodes)));
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
               pragma
                 Assert
                   (Static =>
                      (if Status = Success
                       then
                         Grammar
                           (Pattern,
                            Nodes,
                            Id,
                            Spans (Top).Term_First,
                            Cursor,
                            Term_Grammar)));
               Frames (Top).Term := Id;
            end if;
         end if;
         Frames (Top).Atom := 0;
         Frames (Top).Quantified := False;
         Spans (Top).Term_Last := Cursor;
      end Flush_Atom;

      procedure Flush_Term is
         pragma
           Precondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then Cursor <= Pattern'Length
                and then (if Status = Success then Frames_Syntax (Nodes)));
         pragma
           Postcondition
             (Static =>
                Tree_Valid (Nodes)
                and then Frames_Valid
                and then Used >= Used'Old
                and then (if Status'Old /= Success then Status = Status'Old)
                and then
                  (if Status'Old = Success then Status in Success | Node_Limit)
                and then Spans (Top).First = Spans'Old (Top).First
                and then
                  (for all F in Live_Node =>
                     (if F /= Top
                      then
                        Frames (F) = Frames'Old (F)
                        and Spans (F) = Spans'Old (F)))
                and then Frames (Top).Atom = 0
                and then Frames (Top).Term = 0
                and then not Frames (Top).Quantified
                and then
                  (if Status = Success
                   then
                     Frames (Top).Expr /= 0
                     and then Frames_Syntax (Nodes, False)
                     and then
                       Grammar
                         (Pattern,
                          Nodes,
                          Frames (Top).Expr,
                          Spans (Top).First,
                          Cursor,
                          Expr_Grammar)));
         Id : Node_Id;
      begin
         Flush_Atom;
         if Frames (Top).Term = 0 then
            Add ((Kind => Empty_Node, others => <>), Id);
            Frames (Top).Term := Id;
         end if;
         pragma
           Assert (Static => (if Status = Success then Frames_Syntax (Nodes)));
         if Frames (Top).Expr = 0 then
            Frames (Top).Expr := Frames (Top).Term;
         else
            Add
              ((Kind   => Alt_Node,
                Left   => Frames (Top).Expr,
                Right  => Frames (Top).Term,
                others => <>),
               Id);
            pragma
              Assert
                (Static =>
                   (if Status = Success
                    then
                      Grammar
                        (Pattern,
                         Nodes,
                         Id,
                         Spans (Top).First,
                         Cursor,
                         Expr_Grammar)));
            Frames (Top).Expr := Id;
         end if;
         Frames (Top).Term := 0;
      end Flush_Term;

   begin
      Nodes := [others => <>];
      Root := 0;
      Status := Success;
      if Pattern'Length > Max_Pattern_Length then
         Status := Pattern_Too_Long;
         return;
      end if;
      pragma Assert (Static => Frames_Syntax (Nodes));
      while Pos < Pattern'Length and then Status = Success loop
         pragma Loop_Invariant (Pos in Pos'Loop_Entry .. Pattern'Length);
         pragma Loop_Invariant (Static => Tree_Valid (Nodes) and Frames_Valid);
         pragma Loop_Invariant (Static => Cursor = Pos);
         pragma Loop_Invariant (Static => Top - 1 <= Cursor);
         pragma
           Loop_Invariant
             (Static => Status in Success | Syntax_Error | Node_Limit);
         pragma
           Loop_Invariant
             (Static =>
                (if Pattern_Valid (Pattern)
                 then
                   Status /= Syntax_Error
                   and then
                     (if Status = Success
                      then
                        Syntax_Continuation
                          (Pattern,
                           Cursor,
                           Top - 1,
                           Pending (Frames (Top))))));
         pragma
           Loop_Invariant
             (Static => (if Status = Success then Frames_Syntax (Nodes)));
         pragma Loop_Variant (Decreases => Pattern'Length - Pos);
         declare
            C            : constant Character := Peek;
            N            : Node;
            Id           : Node_Id;
            Token_Status : Compile_Status;
         begin
            pragma Assert (Static => C = Byte_At (Pattern, Cursor));
            Pos := Pos + 1;
            case C is
               when '('                   =>
                  Flush_Atom;
                  if Top = Max_Nodes then
                     Status := Node_Limit;
                  else
                     Top := Top + 1;
                     Frames (Top) := (others => <>);
                     Spans (Top) := (Pos, Pos, Pos);
                  end if;

                  Cursor := Pos;
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success then Frames_Syntax (Nodes)));

               when ')'                   =>
                  if Top = 1 then
                     Status := Syntax_Error;
                  else
                     Flush_Term;
                     Id := Frames (Top).Expr;
                     Top := Top - 1;
                     pragma
                       Assert
                         (Static =>
                            (if Status = Success
                             then
                               Grammar
                                 (Pattern,
                                  Nodes,
                                  Id,
                                  Spans (Top).Term_Last,
                                  Pos,
                                  Atom_Grammar)));
                     Frames (Top).Atom := Id;
                  end if;

                  Cursor := Pos;
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success then Frames_Syntax (Nodes)));

               when '|'                   =>
                  Flush_Term;
                  Spans (Top).Term_First := Pos;
                  Spans (Top).Term_Last := Pos;

                  Cursor := Pos;
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success then Frames_Syntax (Nodes)));

               when '*' | '+' | '?' | '{' =>
                  if Frames (Top).Atom = 0 or else Frames (Top).Quantified then
                     Status := Syntax_Error;
                  else
                     Pos := Pos - 1;
                     Scan_Quantifier (Pattern, Pos, N, Status);
                     N.Left := Frames (Top).Atom;
                     Add (N, Id);
                     pragma
                       Assert
                         (Static =>
                            (if Status = Success
                             then
                               Grammar
                                 (Pattern,
                                  Nodes,
                                  Id,
                                  Spans (Top).Term_Last,
                                  Pos,
                                  Factor_Grammar)));
                     Frames (Top).Atom := Id;
                     Frames (Top).Quantified := True;
                  end if;

                  Cursor := Pos;
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success then Frames_Syntax (Nodes)));

               when '}' | ']'             =>
                  Status := Syntax_Error;

               when others                =>
                  Flush_Atom;
                  Pos := Pos - 1;
                  Scan_Leaf (Pattern, Pos, N, Token_Status);
                  if Token_Status /= Success then
                     Status := Token_Status;
                  end if;
                  Add (N, Id);
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success
                          then
                            Grammar
                              (Pattern,
                               Nodes,
                               Id,
                               Cursor,
                               Pos,
                               Atom_Grammar)));
                  Frames (Top).Atom := Id;
                  Cursor := Pos;
                  pragma
                    Assert
                      (Static =>
                         (if Status = Success then Frames_Syntax (Nodes)));

            end case;
            Cursor := Pos;
            pragma Assert (Static => Top - 1 <= Cursor);
            pragma
              Assert
                (Static =>
                   (if Pattern_Valid (Pattern)
                    then
                      Status /= Syntax_Error
                      and then
                        (if Status = Success
                         then
                           Syntax_Continuation
                             (Pattern,
                              Cursor,
                              Top - 1,
                              Pending (Frames (Top))))));
            pragma
              Assert
                (Static => (if Status = Success then Frames_Syntax (Nodes)));
         end;
      end loop;
      pragma
        Assert (Static => (if Status = Success then Frames_Syntax (Nodes)));
      if Status = Success then
         if Top /= 1 then
            Status := Syntax_Error;
         else
            Flush_Term;
            pragma Assert (Static => Spans (1).First = 0);
            Root := Frames (1).Expr;
            pragma Assert (Root <= Used);

         end if;
      end if;
   end Parse;

   procedure Parse_Complete
     (Pattern : String;
      Witness : Tree;
      Id      : Live_Node;
      Nodes   : out Tree;
      Root    : out Node_Id;
      Status  : out Compile_Status) is
   begin
      Lemma_Grammar_Valid (Pattern, Witness, Id);
      Parse (Pattern, Nodes, Root, Status);
   end Parse_Complete;
end Spark_Re_Trees.Parsing;

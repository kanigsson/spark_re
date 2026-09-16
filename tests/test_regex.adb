with Ada.Text_IO;
with Regex;
with Spark_Re;
with Spark_Re_Trees;
with Spark_Re_Trees.Matching;
with Spark_Re_Trees.Matching.Testing;

procedure Test_Regex is
   use type Regex.Compile_Status;
   package Tiny is new Spark_Re (Max_Nodes => 4, Max_States => 3);
   package Test_Trees is new Spark_Re_Trees (512);
   package Test_Matching is new Test_Trees.Matching (4_096);
   package Rollover is new Test_Matching.Testing;

   procedure Check_Reuse is
      Code         : Regex.Program;
      Result       : Regex.Compile_Status;
      Found        : Boolean;
      Invalid_Work : Regex.Matcher (0);
   begin
      Regex.Initialize (Invalid_Work);
      Regex.Search_With (Code, "", Invalid_Work, Found);
      if Found then
         raise Program_Error with "invalid reused program accepted";
      end if;
      Regex.Compile ("a+", Code, Result);
      declare
         Work : Regex.Matcher (Regex.State_Count (Code));
         High : constant String (Integer'Last - 2 .. Integer'Last) := "aaa";
      begin
         Regex.Initialize (Work);
         Regex.Full_Match_With (Code, High, Work, Found);
         if not Found then
            raise Program_Error with "high-bound reused matching";
         end if;
         Regex.Compile ("b+", Code, Result);
         Regex.Search_With (Code, High, Work, Found);
         if Found then
            raise Program_Error with "stale states after recompilation";
         end if;
         Regex.Search_With (Code, "bbb", Work, Found);
         if not Found then
            raise Program_Error with "same-size program reuse";
         end if;
         Regex.Initialize (Work);
         Regex.Full_Match_With (Code, "", Work, Found);
         if Found then
            raise Program_Error with "explicit workspace reinitialization";
         end if;
      end;
      declare
         Small        : Tiny.Program;
         Small_Status : Tiny.Compile_Status;
      begin
         Tiny.Compile ("a", Small, Small_Status);
         if Small_Status /= Tiny.Success then
            raise Program_Error with "small-instance compilation";
         end if;
         declare
            Work : Tiny.Matcher (Tiny.State_Count (Small));
         begin
            Tiny.Initialize (Work);
            Tiny.Search_With (Small, "ba", Work, Found);
            if not Found then
               raise Program_Error with "small-instance reused search";
            end if;
            Tiny.Full_Match_With (Small, "ba", Work, Found);
            if Found then
               raise Program_Error with "small-instance reused whole match";
            end if;
         end;
      end;
   end Check_Reuse;
   P              : Regex.Program;
   Status         : Regex.Compile_Status;
   T              : Tiny.Program;
   TS             : Tiny.Compile_Status;
   procedure Check (Pattern, Text : String; Found, Whole : Boolean) is
   begin
      Regex.Compile (Pattern, P, Status);
      pragma Assert (Status = Regex.Success);
      pragma Assert (Regex.Search (P, Text) = Found);
      pragma Assert (Regex.Full_Match (P, Text) = Whole);
      declare
         Work   : Regex.Matcher (Regex.State_Count (P));
         Actual : Boolean;
      begin
         Regex.Initialize (Work);
         for Pass in 1 .. 2 loop
            Regex.Search_With (P, Text, Work, Actual);
            if Actual /= Found then
               raise Program_Error with "reused search result";
            end if;
            Regex.Full_Match_With (P, Text, Work, Actual);
            if Actual /= Whole then
               raise Program_Error with "reused whole-match result";
            end if;
         end loop;
      end;
   end Check;
   procedure Reject (Pattern : String) is
   begin
      Regex.Compile (Pattern, P, Status);
      pragma Assert (Status = Regex.Syntax_Error);
      pragma Assert (not Regex.Is_Valid (P));
      pragma Assert (not Regex.Search (P, "anything"));
   end Reject;
   Offset_Pattern : constant String (17 .. 19) := "a+b";
   Offset_Text    : constant String (Integer'Last - 2 .. Integer'Last) :=
     "aab";
begin
   Rollover.Check_Rollover;
   Check_Reuse;
   pragma Assert (not Regex.Search (P, "anything"));
   Check ("", "", True, True);
   Check ("", "a", True, False);
   Check ("a|bc", "xbcx", True, False);
   Check ("(ab|c)+d?", "abcabd", True, True);
   Check ("(a*)*", "aaa", True, True);
   Check ("(a?)*b", "aaa", False, False);
   Check ("(^|a)*b$", "xaaab", True, False);
   Check ("(^$)*", "a", True, False);
   Check ("(a|$)*", "aa", True, True);
   Check ("a($|b)*", "ab", True, True);
   Check ("($a|^b)*", "b", True, True);
   Check ("($a|^b)*", "ba", True, False);
   Check ("($a|^b)+", "ab", False, False);
   Check ("(a?|b?)*c", "abbac", True, True);
   Check ("(a?|b?)*c", "abba", False, False);
   Check ("((^|$)|())*x", "x", True, True);
   --  Mandatory empty copies retain absolute anchor conditions.
   Check ("(^$){2,}", "", True, True);
   Check ("(^$){2,}", "a", False, False);
   Check ("a(^){2}", "a", False, False);
   Check ("a($){2}", "a", True, True);
   Check ("(a?){2,3}", "", True, True);
   Check ("(a?){2,3}", "aaa", True, True);
   Check ("(a?){2,3}", "aaaa", True, False);
   Check ("(^|a){2,}", "a", True, True);
   Check ("(^|a){2,}", "xa", True, False);
   Check ("a{2,4}", "aaa", True, True);
   Check ("a{2,}", "aaaaa", True, True);
   Check ("a{0}", "", True, True);
   Check ("[^a-c]+", "xyz", True, True);
   Check ("[]-]+", "]-", True, True);
   Check ("^ab$", "xab", False, False);
   Check ("^$", "", True, True);
   Check ("a$", "ab", False, False);
   Check ("()|a", "", True, True);
   Check (Offset_Pattern, Offset_Text, True, True);
   Check (".", [1 => ASCII.NUL], True, True);
   for Byte in Character loop
      --  Exercise every byte, including NUL, delimiters, high bytes and all
      --  class punctuation through the class escape path.
      Check ("[\" & Byte & "]", [1 => Byte], True, True);
      Check ("[^\" & Byte & "]", [1 => Byte], False, False);
      Check (".", [1 => Byte], True, True);
   end loop;
   Check ("|||", "", True, True);
   Check ("a||bc", "bc", True, True);
   Check ("(a|)b", "b", True, True);
   Check ("a()b", "ab", True, True);
   Check ("((|a)b|c)", "ab", True, True);
   Reject ("(|*)");
   Reject ("a{1}*");
   Reject ("(a))");
   Reject ("((a)");
   Tiny.Compile ("(((a)))", T, TS);
   pragma Assert (TS = Tiny.Success);
   pragma Assert (Tiny.Full_Match (T, "a"));
   Tiny.Compile ("((((a))))", T, TS);
   pragma Assert (TS = Tiny.Node_Limit);
   --  Lexical grammar boundaries: decimal saturation, leading zeros, and
   --  punctuation whose interpretation differs inside/outside a class.
   Check ("a{0002,0003}", "aaa", True, True);
   Check ("a{0002,}", "aaaa", True, True);
   Check ("a{255}", [1 .. 255 => 'a'], True, True);
   Check ("a{0,255}", "", True, True);
   Check ("a{" & String'(1 .. 300 => '0') & "2}", "aa", True, True);
   Check ("[a-cb-d]", "d", True, True);
   Check ("[^a-cb-d]", "d", False, False);
   Check ("[\--0]", "/", True, True);
   Check ("[\[-\]]", "\", True, True);
   Check ("[]]", "]", True, True);
   Check ("[-]", "-", True, True);
   Check ("[a-]", "-", True, True);
   Check ("[\^]", "^", True, True);
   Check ("\{", "{", True, True);
   for B in Character loop
      --  Raw byte order, including NUL and the highest byte, in a range.
      Check
        ("[\" & Character'First & "-\" & Character'Last & "]",
         [1 => B],
         True,
         True);
   end loop;
   Reject ("a{}");
   Reject ("a{,2}");
   Reject ("a{2,,3}");
   Reject ("a{2,1}");
   Reject ("a{256}");
   Reject ("a{0,256}");
   Reject ("a{0256,}");
   Reject ("a{" & String'(1 .. 300 => '9') & "}");
   Reject ("a{2x}");
   Reject ("a{2,3x}");
   Reject ("a{2,3");
   Reject ("[]");
   Reject ("[^");
   Reject ("[^]");
   Reject ("[a-\]");
   Reject ("[\]");
   Reject ("[b-a]");
   Reject ("[[.x.]]");
   Reject ("[[=x=]]");
   Reject ("[[:alpha:]]");
   Reject ("\a");
   Reject ("\");
   declare
      High_Class : constant String (Integer'Last - 4 .. Integer'Last) :=
        "[a-c]";
      High_Bound : constant String (Integer'Last - 5 .. Integer'Last) :=
        "a{2,3}";
      High_Bad   : constant String (Integer'Last - 1 .. Integer'Last) := "[\";
   begin
      Check (High_Class, "b", True, True);
      Check (High_Bound, "aa", True, True);
      Reject (High_Bad);
   end;
   Tiny.Compile ("abc.", T, TS);
   pragma Assert (TS = Tiny.Node_Limit);
   Tiny.Compile ("abc[", T, TS);
   pragma Assert (TS = Tiny.Syntax_Error);
   --  The epsilon closure fills all three available worklist slots.
   Tiny.Compile ("a*", T, TS);
   pragma Assert (TS = Tiny.Success and Tiny.State_Count (T) = 3);
   pragma Assert (Tiny.Full_Match (T, ""));
   pragma Assert (Tiny.Full_Match (T, "aaaa"));
   pragma Assert (not Tiny.Full_Match (T, "b"));
   Tiny.Compile ("(|a)", T, TS);
   pragma Assert (TS = Tiny.Success and Tiny.State_Count (T) = 3);
   pragma Assert (Tiny.Search (T, "b"));
   pragma Assert (not Tiny.Full_Match (T, "b"));
   pragma Assert (Tiny.Full_Match (T, "a"));
   --  Reuse slots across many generations, including an empty active set,
   --  converging byte transitions, nullable epsilon cycles, and late restart.
   Check ("^ab$", "acb", False, False);
   Check ("ab$", String'(1 .. 10_000 => 'x') & "ab", True, False);
   Check ("(a|a)*b", String'(1 .. 10_000 => 'a'), False, False);
   Check ("(a?|b?)*c$", String'(1 .. 10_000 => 'a') & "c", True, True);
   Check ("^a+$", String'(1 .. 10_000 => 'b'), False, False);
   Tiny.Compile ("a*", T, TS);
   pragma Assert (TS = Tiny.Success);
   pragma Assert (Tiny.Full_Match (T, String'(1 .. 10_000 => 'a')));
   pragma Assert (not Tiny.Full_Match (T, "ab"));
   pragma Assert (Tiny.Full_Match (T, "a"));
   declare
      High_Text : constant String (Integer'Last - 9_999 .. Integer'Last) :=
        [others => 'a'];
   begin
      Check ("^a+$", High_Text, True, True);
   end;
   --  Interior skipping must retain first/final anchors and continuations.
   Check ("$", String'(1 .. 10_000 => 'x'), True, False);
   Check ("^$", String'(1 .. 10_000 => 'x'), False, False);
   Check ("a*$", String'(1 .. 10_000 => 'x'), True, False);
   Check ("^a*$", String'(1 .. 10_000 => 'x'), False, False);
   Check ("^za", "z" & String'(1 .. 10_000 => 'x') & "za", False, False);
   Check ("^a|z", "x" & String'(1 .. 10_000 => 'a') & "z", True, False);
   Check ("(^|$)z", String'(1 .. 10_000 => 'x') & "z", False, False);
   Check ("z($|a)", String'(1 .. 10_000 => 'x') & "z", True, False);
   Check ("a$", String'(1 .. 10_000 => 'x') & "ax", False, False);
   Check ("ab", String'(1 .. 10_000 => 'x') & "aab", True, False);
   Check ("(ab|ac)d", String'(1 .. 10_000 => 'x') & "acdx", True, False);
   Check ("a.*z", "a" & String'(1 .. 10_000 => 'x') & "z", True, True);
   for Byte in Character loop
      declare
         Miss : constant Character := (if Byte = 'x' then 'y' else 'x');
      begin
         Check
           ("[\" & Byte & "]$", String'(1 .. 64 => Miss) & Byte, True, False);
      end;
   end loop;
   declare
      High_Skip  : String (Integer'Last - 10_000 .. Integer'Last) :=
        [others => 'x'];
      High_Empty : constant String (Integer'Last .. Integer'Last - 1) := "";
   begin
      High_Skip (Integer'Last) := 'z';
      Check ("z$", High_Skip, True, False);
      Check ("^$", High_Empty, True, True);
   end;
   Tiny.Compile ("abcd", T, TS);
   pragma Assert (TS = Tiny.Node_Limit);
   Tiny.Compile ("a{4}", T, TS);
   pragma Assert (TS = Tiny.State_Limit);
   pragma Assert (not Tiny.Is_Valid (T));
   pragma Assert (not Tiny.Search (T, "aaaa"));
   Regex.Compile ([1 .. Regex.Max_Pattern_Length + 1 => 'a'], P, Status);
   pragma Assert (Status = Regex.Pattern_Too_Long);
   Regex.Compile ("((){255}){255}", P, Status);
   pragma Assert (Status = Regex.Success);
   Regex.Compile ("(((){255}){255}){255}", P, Status);
   pragma Assert (Status = Regex.Expansion_Limit);
   Ada.Text_IO.Put_Line
     ("PASS: library contracts, offsets, capacities, and regex cases");
end Test_Regex;

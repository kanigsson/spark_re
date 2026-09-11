with Ada.Text_IO;
with Regex;
with Spark_Re;

procedure Test_Regex is
   use type Regex.Compile_Status;
   package Tiny is new Spark_Re (Max_Nodes => 4, Max_States => 3);
   use type Tiny.Compile_Status;
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
   end Check;
   Offset_Pattern : constant String (17 .. 19) := "a+b";
   Offset_Text    : constant String (Integer'Last - 2 .. Integer'Last) :=
     "aab";
begin
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

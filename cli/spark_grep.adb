with Ada.Command_Line;      use Ada.Command_Line;
with Ada.Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Text_IO.Text_Streams;
with Regex;
with Spark_Cli;

procedure Spark_Grep is
   use type Regex.Compile_Status;
   package IO renames Ada.Text_IO;
   package Files renames Ada.Streams.Stream_IO;
   Pattern                                         : Unbounded_String;
   Have_Pattern, End_Options                       : Boolean := False;
   Numbered, Invert, Count_Only, Quiet, List_Files : Boolean := False;
   Hide_Name, Show_Name, Whole, Fixed              : Boolean := False;
   Delimiter                                       : Character := ASCII.LF;
   File_Args                                       :
     array (1 .. Argument_Count) of Natural := [others => 0];
   File_Count                                      : Natural := 0;
   Code                                            : Regex.Program;
   Status                                          : Regex.Compile_Status;
   Any_Selected, Had_Error                         : Boolean := False;
   Index                                           : Positive := 1;

   procedure Error (Message : String) is
   begin
      IO.Put_Line (IO.Standard_Error, "spark-grep: " & Message);
      Had_Error := True;
      Set_Exit_Status (2);
   end Error;

   procedure Help is
   begin
      IO.Put_Line ("Usage: spark-grep [OPTIONS] PATTERN [FILE ...]");
      IO.Put_Line
        ("Byte-oriented extended regex; stdin if no files or FILE is -.");
      IO.Put_Line
        ("-E extended regex (default), -F literal, -e PATTERN (one only)");
      IO.Put_Line
        ("-n record numbers, -v invert, -c count, -q quiet, -l file names");
      IO.Put_Line
        ("-h hide names, -H show names, -x whole record, -z NUL records");
      IO.Put_Line
        ("-- ends options; --help; --version. Unknown options are errors.");
      IO.Put_Line
        ("No locale/Unicode folding, recursion, backreferences or lookaround.");
      IO.Put_Line
        ("Limits: 65535 pattern bytes, 512 AST nodes, 4096 states, repeats <=255.");
      IO.Put_Line
        ("Exit: 0 selected records, 1 none, 2 error. Output records end in delimiter.");
   end Help;

   procedure Set_Pattern (Value : String) is
   begin
      if Have_Pattern then
         Error ("multiple patterns are not supported");
      else
         Pattern := To_Unbounded_String (Value);
         Have_Pattern := True;
      end if;
   end Set_Pattern;

   function Image (N : Natural) return String is
      S : constant String := N'Image;
   begin
      return S (S'First + 1 .. S'Last);
   end Image;

   procedure Write (Value : String) is
   begin
      String'Write (IO.Text_Streams.Stream (IO.Standard_Output), Value);
   end Write;

   procedure Process_Input is
      Work : Regex.Matcher (Regex.State_Count (Code));
      procedure Filter (Name : String; Standard : Boolean) is
         File           : Files.File_Type;
         Line, Selected : Natural := 0;
         Prefix         : constant Boolean :=
           not Hide_Name and then (Show_Name or File_Count > 1);
         procedure Record_Line (Record_Text : String; Stop : out Boolean) is
            Matches : Boolean;
         begin
            if Whole then
               Regex.Full_Match_With (Code, Record_Text, Work, Matches);
            else
               Regex.Search_With (Code, Record_Text, Work, Matches);
            end if;
            Stop := False;
            Line := Line + 1;
            if Matches /= Invert then
               Any_Selected := True;
               Selected := Selected + 1;
               if Quiet then
                  Stop := True;
               elsif List_Files then
                  Write (Name & ASCII.LF);
                  Stop := True;
               elsif not Count_Only then
                  if Prefix then
                     Write (Name & ":");
                  end if;
                  if Numbered then
                     Write (Image (Line) & ":");
                  end if;
                  Write (Record_Text & Delimiter);
               end if;
            end if;
         end Record_Line;
      begin
         if Standard then
            Spark_Cli.Read_Records
              (IO.Text_Streams.Stream (IO.Standard_Input),
               Delimiter,
               Record_Line'Access);
         else
            Files.Open (File, Files.In_File, Name);
            Spark_Cli.Read_Records
              (Files.Stream (File), Delimiter, Record_Line'Access);
            Files.Close (File);
         end if;
         if Count_Only and then not Quiet and then not List_Files then
            if Prefix then
               Write (Name & ":");
            end if;
            Write (Image (Selected) & ASCII.LF);
         end if;
      exception
         when E : others =>
            if Files.Is_Open (File) then
               Files.Close (File);
            end if;
            Error (Name & ": " & Ada.Exceptions.Exception_Message (E));
      end Filter;
   begin
      Regex.Initialize (Work);
      if File_Count = 0 then
         Filter ("(standard input)", True);
      else
         for K in 1 .. File_Count loop
            declare
               Name : constant String := Argument (File_Args (K));
            begin
               Filter
                 ((if Name = "-" then "(standard input)" else Name),
                  Name = "-");
            end;
            exit when Quiet and then Any_Selected;
         end loop;
      end if;
   end Process_Input;

begin
   while Index <= Argument_Count loop
      declare
         Arg : constant String := Argument (Index);
      begin
         if not End_Options and then Arg = "--" then
            End_Options := True;
         elsif not End_Options and then Arg = "--help" then
            Help;
            return;
         elsif not End_Options and then Arg = "--version" then
            IO.Put_Line ("spark-grep 0.1.0");
            return;
         elsif not End_Options and then Arg'Length > 1 and then Arg (1) = '-'
         then
            for K in 2 .. Arg'Last loop
               case Arg (K) is
                  when 'E'    =>
                     Fixed := False;

                  when 'F'    =>
                     Fixed := True;

                  when 'n'    =>
                     Numbered := True;

                  when 'v'    =>
                     Invert := True;

                  when 'c'    =>
                     Count_Only := True;

                  when 'q'    =>
                     Quiet := True;

                  when 'l'    =>
                     List_Files := True;

                  when 'h'    =>
                     Hide_Name := True;
                     Show_Name := False;

                  when 'H'    =>
                     Show_Name := True;
                     Hide_Name := False;

                  when 'x'    =>
                     Whole := True;

                  when 'z'    =>
                     Delimiter := ASCII.NUL;

                  when 'e'    =>
                     if K < Arg'Last then
                        Set_Pattern (Arg (K + 1 .. Arg'Last));
                     elsif Index < Argument_Count then
                        Index := Index + 1;
                        Set_Pattern (Argument (Index));
                     else
                        Error ("-e needs a pattern");
                     end if;
                     exit;

                  when others =>
                     Error ("unknown option: " & Arg & " (see --help)");
                     exit;
               end case;
            end loop;
         elsif not Have_Pattern then
            Set_Pattern (Arg);
         else
            File_Count := File_Count + 1;
            File_Args (File_Count) := Index;
         end if;
      end;
      if Had_Error then
         return;
      end if;
      Index := Index + 1;
   end loop;
   if not Have_Pattern then
      Error ("missing pattern (see --help)");
      return;
   end if;
   if Fixed then
      declare
         Escaped : Unbounded_String;
      begin
         for C of To_String (Pattern) loop
            if C
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
            then
               Append (Escaped, '\');
            end if;
            Append (Escaped, C);
         end loop;
         Pattern := Escaped;
      end;
   end if;
   Regex.Compile (To_String (Pattern), Code, Status);
   if Status /= Regex.Success then
      Error ("pattern: " & Status'Image);
      return;
   end if;
   Process_Input;
   if Had_Error then
      Set_Exit_Status (2);
   elsif Any_Selected then
      Set_Exit_Status (Success);
   else
      Set_Exit_Status (1);
   end if;
exception
   when E : others =>
      Error (Ada.Exceptions.Exception_Message (E));
end Spark_Grep;

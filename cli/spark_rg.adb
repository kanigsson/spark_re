with Ada.Command_Line;      use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Streams;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Text_IO.Text_Streams;
with Dir_Walk;
with Gitignore;
with Regex;
with Spark_Cli;

--  A recursive front end over the same regex kernel as spark-grep: it finds
--  the files itself instead of being handed them, honouring gitignore files
--  the way ripgrep does. Like spark-grep it is deliberately a named subset,
--  not a drop-in replacement.

procedure Spark_Rg is
   use type Regex.Compile_Status;
   use type Gitignore.Decision;
   use type Ada.Directories.File_Kind;
   package IO renames Ada.Text_IO;
   package Files renames Ada.Streams.Stream_IO;

   Pattern                               : Unbounded_String;
   Have_Pattern, End_Options             : Boolean := False;
   Numbered                              : Boolean := True;
   Invert, Count_Only, Quiet, List_Files : Boolean := False;
   Hide_Name, Whole, Fixed               : Boolean := False;
   Scan_Binary                           : Boolean := False;
   Delimiter                             : Character := ASCII.LF;
   Walk_Options                          : Dir_Walk.Options;
   Globs                                 : Gitignore.Rule_Set;
   Have_Positive_Glob                    : Boolean := False;
   Path_Args                             :
     array (1 .. Argument_Count) of Natural := [others => 0];
   Path_Count                            : Natural := 0;
   Code                                  : Regex.Program;
   Status                                : Regex.Compile_Status;
   Any_Selected, Had_Error, Finished     : Boolean := False;
   Index                                 : Positive := 1;

   procedure Error (Message : String) is
   begin
      IO.Put_Line (IO.Standard_Error, "spark-rg: " & Message);
      Had_Error := True;
      Set_Exit_Status (2);
   end Error;

   procedure Warn (Message : String) is
   begin
      IO.Put_Line (IO.Standard_Error, "spark-rg: " & Message);
   end Warn;

   procedure Help is
   begin
      IO.Put_Line ("Usage: spark-rg [OPTIONS] PATTERN [PATH ...]");
      IO.Put_Line
        ("Recursive byte-oriented extended regex search; PATH defaults to '.'.");
      IO.Put_Line
        ("Directories are searched recursively, honouring .gitignore files.");
      IO.Put_Line
        ("-E extended regex (default), -F literal, -e PATTERN (one only)");
      IO.Put_Line
        ("-n record numbers (default), -N no numbers, -v invert, -x whole record");
      IO.Put_Line
        ("-c count, -q quiet, -l file names, -h hide names, -H show names");
      IO.Put_Line
        ("-z NUL records, -g GLOB filter paths (repeatable, !GLOB excludes)");
      IO.Put_Line
        ("--no-ignore, --hidden, -L/--follow, --max-depth N, --binary");
      IO.Put_Line
        ("-- ends options; --help; --version. Unknown options are errors.");
      IO.Put_Line ("No locale/Unicode folding, backreferences or lookaround.");
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

   procedure Add_Glob (Value : String) is
      Glob_Status : Gitignore.Glob_Re.Compile_Status;
   begin
      Gitignore.Add (Globs, Value, Glob_Status);
      if Glob_Status /= Gitignore.Glob_Re.Success then
         Error ("glob: " & Value & " (" & Glob_Status'Image & ")");
      elsif Value'Length = 0 or else Value (Value'First) /= '!' then
         Have_Positive_Glob := True;
      end if;
   end Add_Glob;

   function Image (N : Natural) return String is
      S : constant String := N'Image;
   begin
      return S (S'First + 1 .. S'Last);
   end Image;

   procedure Write (Value : String) is
   begin
      String'Write (IO.Text_Streams.Stream (IO.Standard_Output), Value);
   end Write;

   function Selected_By_Globs (Path : String) return Boolean is
      --  Explicit globs are matched against the path as it is reported. A
      --  negation always wins; otherwise positive globs, when any were given,
      --  restrict the search to what they select.
      Verdict : constant Gitignore.Decision :=
        Gitignore.Match (Globs, Path, Is_Dir => False);
   begin
      if Verdict = Gitignore.Negated then
         return False;
      elsif Have_Positive_Glob then
         return Verdict = Gitignore.Matched;
      else
         return True;
      end if;
   end Selected_By_Globs;

   function Looks_Binary (Name : String) return Boolean is
      --  The same heuristic as the usual tools: a NUL byte near the start.
      use Ada.Streams;
      File   : Files.File_Type;
      Buffer : Stream_Element_Array (1 .. 8_192);
      Last   : Stream_Element_Offset;
   begin
      Files.Open (File, Files.In_File, Name);
      Files.Read (File, Buffer, Last);
      Files.Close (File);
      return (for some K in 1 .. Last => Buffer (K) = 0);
   exception
      when others =>
         if Files.Is_Open (File) then
            Files.Close (File);
         end if;
         return False;
   end Looks_Binary;

   procedure Filter (Name : String; Standard : Boolean; Stop : out Boolean) is
      File           : Files.File_Type;
      Line, Selected : Natural := 0;
      Prefix         : constant Boolean := not Hide_Name;
      procedure Record_Line (Record_Text : String; Halt : out Boolean) is
         Matches : constant Boolean :=
           (if Whole
            then Regex.Full_Match (Code, Record_Text)
            else Regex.Search (Code, Record_Text));
      begin
         Halt := False;
         Line := Line + 1;
         if Matches /= Invert then
            Any_Selected := True;
            Selected := Selected + 1;
            if Quiet then
               Halt := True;
            elsif List_Files then
               Write (Name & ASCII.LF);
               Halt := True;
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
      Stop := False;
      if Standard then
         Spark_Cli.Read_Records
           (IO.Text_Streams.Stream (IO.Standard_Input),
            Delimiter,
            Record_Line'Access);
      else
         if not Scan_Binary and then Looks_Binary (Name) then
            return;
         end if;
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
      Stop := Quiet and then Any_Selected;
   exception
      when E : others =>
         if Files.Is_Open (File) then
            Files.Close (File);
         end if;
         Error (Name & ": " & Ada.Exceptions.Exception_Message (E));
   end Filter;

   procedure Visit (Path : String; Stop : out Boolean) is
   begin
      Stop := False;
      if Selected_By_Globs (Path) then
         Filter (Path, Standard => False, Stop => Stop);
      end if;
   end Visit;

   procedure Search_Argument (Name : String) is
      Stop : Boolean;
   begin
      if Name = "-" then
         Filter ("(standard input)", Standard => True, Stop => Stop);
         Finished := Stop;
      elsif Ada.Directories.Exists (Name)
        and then Ada.Directories.Kind (Name) = Ada.Directories.Directory
      then
         --  Paths below a named directory are reported the way the user
         --  named it, and below "." with no prefix at all.
         Dir_Walk.Walk
           (Root    => Name,
            Opts    => Walk_Options,
            Display =>
              (if Name = "."
               then ""
               elsif Name (Name'Last) = '/'
               then Name
               else Name & "/"),
            Visit   => Visit'Access,
            Warn    => Warn'Access);
         Finished := Quiet and then Any_Selected;
      else
         Visit (Name, Stop);
         Finished := Stop;
      end if;
   exception
      when E : others =>
         Error (Name & ": " & Ada.Exceptions.Exception_Message (E));
   end Search_Argument;

   function Next_Value (Option : String) return String is
   begin
      if Index < Argument_Count then
         Index := Index + 1;
         return Argument (Index);
      else
         Error (Option & " needs a value");
         return "";
      end if;
   end Next_Value;

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
            IO.Put_Line ("spark-rg 0.1.0");
            return;
         elsif not End_Options and then Arg = "--no-ignore" then
            Walk_Options.Respect_Ignore := False;
         elsif not End_Options and then Arg = "--hidden" then
            Walk_Options.Hidden := True;
         elsif not End_Options and then Arg = "--follow" then
            Walk_Options.Follow_Links := True;
         elsif not End_Options and then Arg = "--binary" then
            Scan_Binary := True;
         elsif not End_Options and then Arg = "--max-depth" then
            declare
               Value : constant String := Next_Value ("--max-depth");
            begin
               if not Had_Error then
                  Walk_Options.Max_Depth := Natural'Value (Value);
               end if;
            exception
               when others =>
                  Error ("--max-depth needs a number, not " & Value);
            end;
         elsif not End_Options and then Arg'Length > 1 and then Arg (1) = '-'
         then
            for K in 2 .. Arg'Last loop
               case Arg (K) is
                  when 'E'       =>
                     Fixed := False;

                  when 'F'       =>
                     Fixed := True;

                  when 'n'       =>
                     Numbered := True;

                  when 'N'       =>
                     Numbered := False;

                  when 'v'       =>
                     Invert := True;

                  when 'c'       =>
                     Count_Only := True;

                  when 'q'       =>
                     Quiet := True;

                  when 'l'       =>
                     List_Files := True;

                  when 'h'       =>
                     --  Names are shown by default, since a recursive search
                     --  reports matches from many files.
                     Hide_Name := True;

                  when 'H'       =>
                     Hide_Name := False;

                  when 'x'       =>
                     Whole := True;

                  when 'z'       =>
                     Delimiter := ASCII.NUL;

                  when 'L'       =>
                     Walk_Options.Follow_Links := True;

                  when 'e' | 'g' =>
                     declare
                        Is_Glob : constant Boolean := Arg (K) = 'g';
                        Value   : constant String :=
                          (if K < Arg'Last
                           then Arg (K + 1 .. Arg'Last)
                           else Next_Value (['-', Arg (K)]));
                     begin
                        if not Had_Error then
                           if Is_Glob then
                              Add_Glob (Value);
                           else
                              Set_Pattern (Value);
                           end if;
                        end if;
                     end;
                     exit;

                  when others    =>
                     Error ("unknown option: " & Arg & " (see --help)");
                     exit;
               end case;
            end loop;
         elsif not Have_Pattern then
            Set_Pattern (Arg);
         else
            Path_Count := Path_Count + 1;
            Path_Args (Path_Count) := Index;
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

   if Path_Count = 0 then
      Search_Argument (".");
   else
      for K in 1 .. Path_Count loop
         Search_Argument (Argument (Path_Args (K)));
         exit when Finished;
      end loop;
   end if;

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
end Spark_Rg;

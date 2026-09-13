with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Spark_Cli;

package body Gitignore is

   use type Glob_Re.Compile_Status;

   Punctuation : constant String := "\.^$|?*+()[]{}";
   --  The bytes the pattern language treats as operators outside a class.
   --  Everything else stands for itself and must not be escaped, since the
   --  language rejects escapes it does not recognize.

   function Escaped (C : Character) return String
   is (if (for some P of Punctuation => P = C) then ['\', C] else [1 => C]);

   function Is_Empty (Self : Rule_Set) return Boolean
   is (Self.Rules.Is_Empty);

   ---------------
   -- To_Regex  --
   ---------------

   function To_Regex (Glob : String) return String is
      Result   : Unbounded_String;
      Index    : Integer := Glob'First;
      Anchored : Boolean := False;

      function Double_Star_At (K : Integer) return Boolean
      is (K + 1 <= Glob'Last
          and then Glob (K) = '*'
          and then Glob (K + 1) = '*');

      procedure Append_Class is
         --  Copy one bracket expression. The two languages agree on ranges,
         --  on a literal ']' in first position and on backslash escapes; only
         --  the negation marker and a stray '^' need rewriting.
         Body_Text : Unbounded_String;
         Negated   : Boolean := False;
         K         : Integer := Index + 1;
      begin
         if K <= Glob'Last and then (Glob (K) = '!' or else Glob (K) = '^')
         then
            Negated := True;
            K := K + 1;
         end if;
         if K <= Glob'Last and then Glob (K) = ']' then
            Append (Body_Text, "\]");
            K := K + 1;
         end if;
         while K <= Glob'Last and then Glob (K) /= ']' loop
            if Glob (K) = '\' and then K < Glob'Last then
               Append (Body_Text, '\');
               Append (Body_Text, Glob (K + 1));
               K := K + 2;
            else
               if Glob (K) in '\' | '^' then
                  Append (Body_Text, '\');
               end if;
               Append (Body_Text, Glob (K));
               K := K + 1;
            end if;
         end loop;
         if K > Glob'Last then
            --  Unterminated, so the bracket stands for itself.
            Append (Result, "\[");
            Index := Index + 1;
         else
            Append
              (Result,
               "["
               & (if Negated then "^" else "")
               & To_String (Body_Text)
               & "]");
            Index := K + 1;
         end if;
      end Append_Class;

   begin
      --  A separator anywhere but at the end ties the glob to the directory
      --  holding the ignore file; otherwise it may match at any depth below.
      for K in Glob'Range loop
         if Glob (K) = '/' and then K < Glob'Last then
            Anchored := True;
         end if;
      end loop;

      Append (Result, "^");
      if Glob'Length > 0 and then Glob (Glob'First) = '/' then
         Index := Glob'First + 1;
      elsif not Anchored then
         Append (Result, "(.*/)?");
      end if;

      while Index <= Glob'Last loop
         if Glob (Index) = '\' and then Index < Glob'Last then
            Append (Result, Escaped (Glob (Index + 1)));
            Index := Index + 2;

         elsif Glob (Index) = '/' and then Double_Star_At (Index + 1) then
            --  A whole "**" segment spans any number of directories, so it
            --  absorbs the separators around it rather than one of them.
            if Index + 3 > Glob'Last then
               Append (Result, "/.*");
               Index := Index + 3;
            elsif Glob (Index + 3) = '/' then
               Append (Result, "/(.*/)?");
               Index := Index + 4;
            else
               Append (Result, "/");
               Index := Index + 1;
            end if;

         elsif Index = Glob'First
           and then Double_Star_At (Index)
           and then (Index + 2 > Glob'Last or else Glob (Index + 2) = '/')
         then
            if Index + 2 > Glob'Last then
               Append (Result, ".*");
               Index := Index + 2;
            else
               Append (Result, "(.*/)?");
               Index := Index + 3;
            end if;

         elsif Glob (Index) = '*' then
            Append (Result, "[^/]*");
            Index := Index + 1;

         elsif Glob (Index) = '?' then
            Append (Result, "[^/]");
            Index := Index + 1;

         elsif Glob (Index) = '[' then
            Append_Class;

         else
            Append (Result, Escaped (Glob (Index)));
            Index := Index + 1;
         end if;
      end loop;

      Append (Result, "$");
      return To_String (Result);
   end To_Regex;

   ---------
   -- Add --
   ---------

   procedure Add
     (Self    : in out Rule_Set;
      Pattern : String;
      Status  : out Glob_Re.Compile_Status)
   is
      Last     : Integer := Pattern'Last;
      First    : Integer := Pattern'First;
      Negated  : Boolean := False;
      Dir_Only : Boolean := False;
   begin
      Status := Glob_Re.Success;

      --  Unescaped trailing blanks are not part of the pattern.
      while Last >= First and then Pattern (Last) = ' ' loop
         declare
            Slashes : Natural := 0;
         begin
            while Last - Slashes - 1 >= First
              and then Pattern (Last - Slashes - 1) = '\'
            loop
               Slashes := Slashes + 1;
            end loop;
            exit when Slashes mod 2 = 1;
            Last := Last - 1;
         end;
      end loop;

      if First > Last or else Pattern (First) = '#' then
         return;
      end if;

      if Pattern (First) = '!' then
         Negated := True;
         First := First + 1;
      end if;

      if Last >= First and then Pattern (Last) = '/' then
         Dir_Only := True;
         Last := Last - 1;
      end if;

      if First > Last then
         return;
      end if;

      declare
         New_Rule : Rule :=
           (Negated => Negated, Dir_Only => Dir_Only, others => <>);
      begin
         Glob_Re.Compile
           (To_Regex (Pattern (First .. Last)), New_Rule.Code, Status);
         if Status = Glob_Re.Success then
            Self.Rules.Append (New_Rule);
         end if;
      end;
   end Add;

   ----------
   -- Load --
   ----------

   procedure Load
     (Self : in out Rule_Set;
      Path : String;
      Warn : not null access procedure (Message : String))
   is
      package Files renames Ada.Streams.Stream_IO;
      File   : Files.File_Type;
      Number : Natural := 0;

      procedure Rule_Line (Record_Text : String; Stop : out Boolean) is
         Last   : Integer := Record_Text'Last;
         Status : Glob_Re.Compile_Status;
      begin
         Stop := False;
         Number := Number + 1;
         if Last >= Record_Text'First and then Record_Text (Last) = ASCII.CR
         then
            Last := Last - 1;
         end if;
         Add (Self, Record_Text (Record_Text'First .. Last), Status);
         if Status /= Glob_Re.Success then
            Warn
              (Path
               & ":"
               & Number'Image
               & ": unsupported ignore pattern ("
               & Status'Image
               & ")");
         end if;
      end Rule_Line;

   begin
      Files.Open (File, Files.In_File, Path);
      Spark_Cli.Read_Records (Files.Stream (File), ASCII.LF, Rule_Line'Access);
      Files.Close (File);
   exception
      when E : others =>
         if Files.Is_Open (File) then
            Files.Close (File);
         end if;
         Warn (Path & ": " & Ada.Exceptions.Exception_Message (E));
   end Load;

   -----------
   -- Match --
   -----------

   function Match
     (Self : Rule_Set; Rel_Path : String; Is_Dir : Boolean) return Decision
   is
      Result : Decision := No_Match;
   begin
      for R of Self.Rules loop
         if (Is_Dir or else not R.Dir_Only)
           and then Glob_Re.Full_Match (R.Code, Rel_Path)
         then
            Result := (if R.Negated then Negated else Matched);
         end if;
      end loop;
      return Result;
   end Match;

end Gitignore;

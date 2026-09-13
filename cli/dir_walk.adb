with Ada.Containers.Vectors;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with GNAT.OS_Lib;
with Gitignore;

package body Dir_Walk is

   package Dirs renames Ada.Directories;
   use type Dirs.File_Kind;
   use type Gitignore.Decision;

   Ignore_File : constant String := ".gitignore";

   package Name_Vectors is new
     Ada.Containers.Vectors (Positive, Unbounded_String);

   package Name_Sorting is new Name_Vectors.Generic_Sorting ("<" => "<");

   type Ignore_Level is record
      Rules : Gitignore.Rule_Set;
      Base  : Unbounded_String;
      --  Path of the directory holding the file, relative to Root, either
      --  empty or ending in a separator.
   end record;

   package Level_Vectors is new
     Ada.Containers.Vectors (Positive, Ignore_Level);

   ----------
   -- Walk --
   ----------

   procedure Walk
     (Root    : String;
      Opts    : Options;
      Display : String;
      Visit   : not null access procedure (Path : String; Stop : out Boolean);
      Warn    : not null access procedure (Message : String))
   is
      Levels  : Level_Vectors.Vector;
      Stopped : Boolean := False;

      Root_Resolved : constant String :=
        GNAT.OS_Lib.Normalize_Pathname (Root, Resolve_Links => True);
      --  Links are detected one component at a time against an already
      --  resolved parent, so a starting point that itself lies behind a link
      --  is followed rather than refused.

      function Ignored (Rel_Path : String; Is_Dir : Boolean) return Boolean is
         --  Nearer ignore files override more distant ones, and within one
         --  file the last applicable rule decides.
         Result : Boolean := False;
      begin
         for Level of Levels loop
            declare
               Base : constant String := To_String (Level.Base);
            begin
               if Rel_Path'Length > Base'Length then
                  case Gitignore.Match
                         (Level.Rules,
                          Rel_Path
                            (Rel_Path'First + Base'Length .. Rel_Path'Last),
                          Is_Dir)
                  is
                     when Gitignore.Matched  =>
                        Result := True;

                     when Gitignore.Negated  =>
                        Result := False;

                     when Gitignore.No_Match =>
                        null;
                  end case;
               end if;
            end;
         end loop;
         return Result;
      end Ignored;

      procedure Descend (Rel_Dir : String; Resolved : String; Depth : Natural)
      is
         --  Rel_Dir is relative to Root and is empty or ends in a separator.
         Physical  : constant String := Root & "/" & Rel_Dir;
         --  Always ends in a separator, so entry names append directly.
         Pushed    : Boolean := False;
         Entries   : Name_Vectors.Vector;
         Search    : Dirs.Search_Type;
         Directory : Dirs.Directory_Entry_Type;
      begin
         if Opts.Respect_Ignore and then Dirs.Exists (Physical & Ignore_File)
         then
            declare
               Level : Ignore_Level;
            begin
               Gitignore.Load (Level.Rules, Physical & Ignore_File, Warn);
               if not Gitignore.Is_Empty (Level.Rules) then
                  Level.Base := To_Unbounded_String (Rel_Dir);
                  Levels.Append (Level);
                  Pushed := True;
               end if;
            end;
         end if;

         --  Collect and sort first, because directory order is not specified
         --  and the tool's output has to be reproducible.
         begin
            Dirs.Start_Search (Search, Physical, "");
            while Dirs.More_Entries (Search) loop
               Dirs.Get_Next_Entry (Search, Directory);
               declare
                  Name : constant String := Dirs.Simple_Name (Directory);
               begin
                  if Name /= "." and then Name /= ".." then
                     Entries.Append (To_Unbounded_String (Name));
                  end if;
               end;
            end loop;
            Dirs.End_Search (Search);
         exception
            when E : others =>
               if Dirs.More_Entries (Search) then
                  Dirs.End_Search (Search);
               end if;
               Warn (Physical & ": " & Ada.Exceptions.Exception_Message (E));
         end;
         Name_Sorting.Sort (Entries);

         for Item of Entries loop
            exit when Stopped or else Depth >= Opts.Max_Depth;
            declare
               Name     : constant String := To_String (Item);
               Rel_Path : constant String := Rel_Dir & Name;
               Full     : constant String := Physical & Name;
               Kind     : Dirs.File_Kind;
            begin
               if (Opts.Hidden or else Name (Name'First) /= '.')
                 and then not (Opts.Respect_Ignore and then Name = ".git")
               then
                  begin
                     Kind := Dirs.Kind (Full);
                  exception
                     when others =>
                        --  A broken link or an entry that vanished during the
                        --  traversal is not worth a diagnostic.
                        Kind := Dirs.Special_File;
                  end;

                  if Kind = Dirs.Directory then
                     declare
                        Plain : constant String := Resolved & "/" & Name;
                        Child : constant String :=
                          GNAT.OS_Lib.Normalize_Pathname
                            (Plain, Resolve_Links => True);
                     begin
                        if not Ignored (Rel_Path, Is_Dir => True)
                          and then Depth + 1 < Opts.Max_Depth
                          and then (if Opts.Follow_Links
                                    then Child /= ""
                                    else Child = Plain)
                        then
                           Descend (Rel_Path & "/", Child, Depth + 1);
                        end if;
                     end;
                  elsif Kind = Dirs.Ordinary_File
                    and then not Ignored (Rel_Path, Is_Dir => False)
                  then
                     Visit (Display & Rel_Path, Stopped);
                  end if;
               end if;
            end;
         end loop;

         if Pushed then
            Levels.Delete_Last;
         end if;
      end Descend;

   begin
      Descend ("", (if Root_Resolved = "" then Root else Root_Resolved), 0);
   end Walk;

end Dir_Walk;

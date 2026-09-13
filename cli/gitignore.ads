with Ada.Containers.Vectors;
with Spark_Re;
--  Gitignore rule sets for the recursive walker. Ordinary Ada, deliberately
--  outside the SPARK proof boundary: it reads files and uses dynamic storage.
--
--  Matching itself is delegated to the proved regex engine. Every glob is
--  translated into an equivalent anchored pattern over the whole candidate
--  path, so no second matching implementation exists to disagree with the
--  first. The translation is the only part that has to be trusted.

package Gitignore is

   --  Glob rules are short and expand to small automata, so they use a much
   --  smaller storage budget than the default instance. A compiled program is
   --  dominated by a per-instruction byte set and a rule set holds one program
   --  per rule, which makes the default budget far too large to hold per rule.
   --  This instantiation is not covered by the library proof run, as is true
   --  of all command line code.
   package Glob_Re is new Spark_Re (Max_Nodes => 128, Max_States => 512);

   type Decision is (No_Match, Matched, Negated);
   --  The verdict of a rule set: no rule applied, the last applicable rule
   --  selected the path, or the last applicable rule was a negation.

   type Rule_Set is private;

   function Is_Empty (Self : Rule_Set) return Boolean;

   procedure Add
     (Self    : in out Rule_Set;
      Pattern : String;
      Status  : out Glob_Re.Compile_Status);
   --  Append one gitignore-syntax rule, including a leading "!" negation and
   --  a trailing "/" directory restriction. Blank and comment lines are
   --  accepted and add nothing. A rule that exceeds the glob storage budget
   --  reports its status and is not added.

   procedure Load
     (Self : in out Rule_Set;
      Path : String;
      Warn : not null access procedure (Message : String));
   --  Append every rule of one ignore file, in file order. Rules that cannot
   --  be compiled are reported through Warn and skipped, so an exotic pattern
   --  costs precision rather than the whole traversal.

   function Match
     (Self : Rule_Set; Rel_Path : String; Is_Dir : Boolean) return Decision;
   --  Rel_Path is relative to the directory holding the ignore file and uses
   --  '/' separators, with no leading or trailing separator. The last rule
   --  that applies decides, and directory-only rules apply only when Is_Dir.

   function To_Regex (Glob : String) return String;
   --  The translation of one glob body, with negation and the directory
   --  marker already removed. Exposed so that it can be tested directly.

private

   type Rule is record
      Code     : Glob_Re.Program;
      Negated  : Boolean := False;
      Dir_Only : Boolean := False;
   end record;

   package Rule_Vectors is new Ada.Containers.Vectors (Positive, Rule);

   type Rule_Set is record
      Rules : Rule_Vectors.Vector;
   end record;

end Gitignore;

--  Byte-oriented regular expressions. No allocation, I/O, or global state.
--  Instantiate to choose the storage budget; each compiled Program owns its NFA.
--
--  This is a facade. The three layers it composes are proved independently:
--  Spark_Re_Trees (syntax trees and their span semantics), Spark_Re_Parsing
--  (pattern text to a grammar derivation), and Spark_Re_Matching (tree to NFA,
--  and the NFA simulator). Neither of the latter two refers to the other.

with Spark_Re_Common;
use type Spark_Re_Common.Compile_Status;
with Spark_Re_Trees;
with Spark_Re_Trees.Matching;

generic
   Max_Nodes : Positive := 512;
   Max_States : Positive := 4_096;
package Spark_Re with SPARK_Mode is
   Max_Pattern_Length : constant := Spark_Re_Common.Max_Pattern_Length;
   Max_Repetition     : constant := Spark_Re_Common.Max_Repetition;

   subtype Compile_Status is Spark_Re_Common.Compile_Status;
   function Success return Compile_Status renames Spark_Re_Common.Success;
   function Syntax_Error return Compile_Status
   renames Spark_Re_Common.Syntax_Error;
   function Pattern_Too_Long return Compile_Status
   renames Spark_Re_Common.Pattern_Too_Long;
   function Node_Limit return Compile_Status
   renames Spark_Re_Common.Node_Limit;
   function State_Limit return Compile_Status
   renames Spark_Re_Common.State_Limit;
   function Expansion_Limit return Compile_Status
   renames Spark_Re_Common.Expansion_Limit;

   type Program is private;
   function Is_Valid (Self : Program) return Boolean
   with Global => null;
   function State_Count (Self : Program) return Natural
   with Global => null, Post => State_Count'Result <= Max_States;
   --  Every emitted edge stays within the compiled prefix, and successful
   --  programs have a live entry point. This does not specify pattern parsing.
   function Well_Formed (Self : Program) return Boolean
   with Ghost, Global => null;
   procedure Compile
     (Pattern : String; Result : out Program; Status : out Compile_Status)
   with
     Global => null,
     Always_Terminates,
     Post   =>
       (Is_Valid (Result) = (Status = Success)) and Well_Formed (Result);
   --  Declarative semantics of the compiled NFA, including absolute anchors
   --  and restart at every text boundary for search. This does not specify
   --  which NFA Compile must construct for a given pattern.
   function NFA_Accepts
     (Self : Program; Text : String; Whole : Boolean) return Boolean
   with Ghost => Static, Global => null;
   --  Search accepts a substring; Full_Match accepts the entire byte string.
   --  Invalid programs return False. Anchors refer to the entire input string.
   function Search (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Search'Result);
   pragma
     Postcondition (Static => Search'Result = NFA_Accepts (Self, Text, False));
   function Full_Match (Self : Program; Text : String) return Boolean
   with
     Global => null,
     Post   => (if not Is_Valid (Self) then not Full_Match'Result);
   pragma
     Postcondition
       (Static => Full_Match'Result = NFA_Accepts (Self, Text, True));

   --  Allocate once at the compiled state count, then initialize before use.
   --  The workspace can be reused with any program of that same size.
   subtype Workspace_Capacity is Natural range 0 .. Max_States;
   type Matcher (Capacity : Workspace_Capacity) is limited private
   with Default_Initial_Condition => True;
   function Matcher_Valid (Work : Matcher) return Boolean
   with Ghost => Static, Global => null;
   procedure Initialize (Work : out Matcher)
   with Global => null, Post => (Static => Matcher_Valid (Work));

   procedure Search_With
     (Self  : Program;
      Text  : String;
      Work  : in out Matcher;
      Found : out Boolean)
   with Global => null, Pre => Work.Capacity = State_Count (Self);
   pragma Precondition (Static => Matcher_Valid (Work));
   pragma
     Postcondition
       (Static => Matcher_Valid (Work) and then Found = Search (Self, Text));

   procedure Full_Match_With
     (Self  : Program;
      Text  : String;
      Work  : in out Matcher;
      Found : out Boolean)
   with Global => null, Pre => Work.Capacity = State_Count (Self);
   pragma Precondition (Static => Matcher_Valid (Work));
   pragma
     Postcondition
       (Static =>
          Matcher_Valid (Work) and then Found = Full_Match (Self, Text));

   --  Pattern-only language semantics, independent of parsing, tree
   --  allocation, compilation, and simulation.
   function Pattern_Accepts
     (Pattern, Text : String; Whole : Boolean) return Boolean
   with Ghost => Static, Global => null;

   --  Apply the actual compilation operation and prove its result for any
   --  supplied text. Capacity failures remain explicit.
   procedure Compile_For_Text
     (Pattern, Text : String;
      Whole         : Boolean;
      Result        : out Program;
      Status        : out Compile_Status)
   with
     Ghost => Static,
     Post  =>
       Well_Formed (Result)
       and then (Is_Valid (Result) = (Status = Success))
       and then (if Status = Success
                 then
                   NFA_Accepts (Result, Text, Whole)
                   = Pattern_Accepts (Pattern, Text, Whole)
                   and then (if Whole
                             then Full_Match (Result, Text)
                             else Search (Result, Text))
                            = Pattern_Accepts (Pattern, Text, Whole));
private
   package Trees is new Spark_Re_Trees (Max_Nodes);
   package Matching is new Trees.Matching (Max_States);

   type Program is record
      Impl : Matching.Program;
   end record;

   type Matcher (Capacity : Workspace_Capacity) is limited record
      Impl : Matching.Matcher (Capacity);
   end record;

   function Well_Formed (Self : Program) return Boolean
   is (Matching.Well_Formed (Self.Impl));
end Spark_Re;

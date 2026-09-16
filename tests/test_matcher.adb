with Ada.Command_Line; use Ada.Command_Line;
with Ada.Text_IO;
with Ada.Text_IO.Text_Streams;
with Regex;
with Spark_Cli;

procedure Test_Matcher is
   use type Regex.Compile_Status;
   P         : Regex.Program;
   Status    : Regex.Compile_Status;
   Whole     : constant Boolean := Argument (1) = "whole";
   Delimiter : constant Character :=
     (if Argument (2) = "nul" then ASCII.NUL else ASCII.LF);
   Any_Found : Boolean := False;
begin
   Regex.Compile (Argument (3), P, Status);
   if Status /= Regex.Success then
      raise Program_Error with "test pattern did not compile";
   end if;
   declare
      Work : Regex.Matcher (Regex.State_Count (P));
      procedure Record_Line (Text : String; Stop : out Boolean) is
         Search_Result, Whole_Result, Again : Boolean;
      begin
         Stop := False;
         Regex.Search_With (P, Text, Work, Search_Result);
         Regex.Full_Match_With (P, Text, Work, Whole_Result);
         Regex.Search_With (P, Text, Work, Again);
         if Search_Result /= Regex.Search (P, Text)
           or else Whole_Result /= Regex.Full_Match (P, Text)
           or else Again /= Search_Result
         then
            raise Program_Error with "reused workspace differs from one-shot";
         end if;
         if (if Whole then Whole_Result else Search_Result) then
            Any_Found := True;
            String'Write
              (Ada.Text_IO.Text_Streams.Stream (Ada.Text_IO.Standard_Output),
               Text & Delimiter);
         end if;
      end Record_Line;
   begin
      Regex.Initialize (Work);
      Spark_Cli.Read_Records
        (Ada.Text_IO.Text_Streams.Stream (Ada.Text_IO.Standard_Input),
         Delimiter,
         Record_Line'Access);
   end;
   Set_Exit_Status (if Any_Found then Success else Failure);
end Test_Matcher;

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package body Spark_Cli is
   procedure Read_Records
     (Input     : not null access Ada.Streams.Root_Stream_Type'Class;
      Delimiter : Character;
      Process   :
        not null access procedure (Record_Text : String; Stop : out Boolean))
   is
      use Ada.Streams;
      Block   : Stream_Element_Array (1 .. 65_536);
      Last    : Stream_Element_Offset;
      Pending : Unbounded_String;
      Stop    : Boolean;
   begin
      loop
         Read (Input.all, Block, Last);
         exit when Last < Block'First;
         for I in Block'First .. Last loop
            if Character'Val (Block (I)) = Delimiter then
               Process (To_String (Pending), Stop);
               if Stop then
                  return;
               end if;
               Pending := Null_Unbounded_String;
            else
               Append (Pending, Character'Val (Block (I)));
            end if;
         end loop;
      end loop;
      if Length (Pending) > 0 then
         Process (To_String (Pending), Stop);
      end if;
   end Read_Records;
end Spark_Cli;

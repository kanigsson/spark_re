with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package body Spark_Cli is
   procedure Read_Records
     (Input     : not null access Ada.Streams.Root_Stream_Type'Class;
      Delimiter : Character;
      Process   :
        not null access procedure (Record_Text : String; Stop : out Boolean))
   is
      use Ada.Streams;
      pragma
        Compile_Time_Error
          (Stream_Element'Size /= Character'Size,
           "record framing assumes byte-sized stream elements");
      Block_Size : constant := 65_536;
      --  Records are framed in place: Block is an overlay of Text, so a whole
      --  record within one block reaches the handler as a slice, with no
      --  intermediate copy.
      Text       : String (1 .. Block_Size);
      Block      : Stream_Element_Array (1 .. Block_Size)
      with Address => Text'Address, Import;
      --  Holds the head of a record straddling a block boundary, which is the
      --  only case that needs a copy.
      Pending    : Unbounded_String;
      Last       : Stream_Element_Offset;
      Filled     : Natural;
      Start      : Positive;
      Stop       : Boolean;

      procedure Emit (Tail : String) is
      begin
         if Length (Pending) = 0 then
            Process (Tail, Stop);
         else
            Append (Pending, Tail);
            Process (To_String (Pending), Stop);
            Pending := Null_Unbounded_String;
         end if;
      end Emit;
   begin
      loop
         Read (Input.all, Block, Last);
         exit when Last < Block'First;
         Filled := Natural (Last);
         Start := 1;
         for I in 1 .. Filled loop
            if Text (I) = Delimiter then
               Emit (Text (Start .. I - 1));
               if Stop then
                  return;
               end if;
               Start := I + 1;
            end if;
         end loop;
         if Start <= Filled then
            Append (Pending, Text (Start .. Filled));
         end if;
      end loop;
      if Length (Pending) > 0 then
         Process (To_String (Pending), Stop);
      end if;
   end Read_Records;
end Spark_Cli;

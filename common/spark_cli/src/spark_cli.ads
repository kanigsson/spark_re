with Ada.Streams;
--  Ordinary Ada I/O support, deliberately outside the SPARK proof boundary.

package Spark_Cli is
   procedure Read_Records
     (Input     : not null access Ada.Streams.Root_Stream_Type'Class;
      Delimiter : Character;
      Process   :
        not null access procedure (Record_Text : String; Stop : out Boolean));
   --  Delimiter bytes are removed. Emit a final nonempty unterminated record,
   --  but no extra record after a trailing delimiter. Stop allows early exit.
   --
   --  Record_Text usually designates a slice of an internal buffer that is
   --  reused once the call returns. A handler that needs the bytes afterwards
   --  must copy them.
end Spark_Cli;

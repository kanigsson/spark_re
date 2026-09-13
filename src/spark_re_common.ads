--  Limits and byte sets shared by the syntax-tree, parser and matcher layers.
--  This unit has no body and no dependencies; it exists so that those three
--  layers can be proved independently of one another.

package Spark_Re_Common with SPARK_Mode is
   Max_Pattern_Length : constant := 65_535;
   Max_Repetition     : constant := 255;

   type Compile_Status is
     (Success,
      Syntax_Error,
      Pattern_Too_Long,
      Node_Limit,
      State_Limit,
      Expansion_Limit);

   type Byte_Set is array (Character) of Boolean;
end Spark_Re_Common;

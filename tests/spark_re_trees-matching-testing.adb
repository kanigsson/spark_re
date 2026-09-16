package body Spark_Re_Trees.Matching.Testing is
   procedure Check_Rollover is
      P     : Program;
      Work  : Matcher (1);
      Found : Boolean;
   begin
      --  A consuming self-loop gives both success and failure without an
      --  interior restart cache: whole matching does not use that cache.
      P.Count := 1;
      P.Start := 1;
      P.Valid := True;
      P.Code (1) :=
        (Op => Consume, Bytes => [others => True], Next_1 => 1, Next_2 => 0);
      P.Restart.States (1) := True;
      P.Restart.Bytes := [others => True];
      Initialize (Work);
      --  The empty view remains valid when only its nonnegative epoch changes.
      Work.Current.Epoch := Generation'Last - 1;
      Work.Seeds.Epoch := Generation'Last - 1;
      Full_Match_With (P, "abc", Work, Found);
      if Found or else Work.Current.Epoch /= 2 or else Work.Seeds.Epoch /= 3
      then
         raise Program_Error with "generation rollover within a record";
      end if;
      Initialize (Work);
      Work.Current.Epoch := Generation'Last - 1;
      Work.Seeds.Epoch := Generation'Last - 1;
      Full_Match_With (P, "", Work, Found);
      if Found or else Work.Current.Epoch /= Generation'Last then
         raise Program_Error with "last generation at an empty record";
      end if;
      Full_Match_With (P, "a", Work, Found);
      if Found or else Work.Current.Epoch /= 1 or else Work.Seeds.Epoch /= 1
      then
         raise Program_Error with "generation rollover between records";
      end if;
      --  Early acceptance can leave a populated workspace at saturation.
      P.Code (1) := (Op => Accept_State, others => <>);
      P.Restart.Nullable := True;
      Initialize (Work);
      Work.Current.Epoch := Generation'Last - 1;
      Work.Seeds.Epoch := Generation'Last - 1;
      Search_With (P, "anything", Work, Found);
      if not Found then
         raise Program_Error with "early acceptance at saturation";
      end if;
      Full_Match_With (P, "a", Work, Found);
      if Found then
         raise Program_Error with "stale accepting state after rollover";
      end if;
   end Check_Rollover;
end Spark_Re_Trees.Matching.Testing;

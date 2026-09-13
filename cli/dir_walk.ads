--  Recursive directory traversal that honours gitignore files, in the manner
--  of ripgrep. Ordinary Ada, outside the SPARK proof boundary.

package Dir_Walk is

   type Options is record
      Respect_Ignore : Boolean := True;
      --  Apply .gitignore files found along the way, and skip .git.
      Hidden         : Boolean := False;
      --  Visit entries whose name begins with a dot.
      Follow_Links   : Boolean := False;
      --  Descend into directories reached through a symbolic link. Link
      --  cycles are then bounded only by Max_Depth.
      Max_Depth      : Natural := 64;
      --  Levels below the starting point, counted as ripgrep counts them:
      --  entries directly inside it are one level, and zero visits nothing.
   end record;

   procedure Walk
     (Root    : String;
      Opts    : Options;
      Display : String;
      Visit   : not null access procedure (Path : String; Stop : out Boolean);
      Warn    : not null access procedure (Message : String));
   --  Visit every file below Root in a deterministic order, sorted by name
   --  within each directory. Display prefixes the reported paths and is
   --  normally the directory as the user named it, or empty for the current
   --  directory. Visit may request an early stop, which unwinds the whole
   --  traversal. Directories that cannot be read are reported through Warn
   --  and skipped, so one unreadable subtree does not end the search.

end Dir_Walk;

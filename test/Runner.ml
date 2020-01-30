let () =
  Alcotest.run ~argv:[| "zpath" |] "LoopInvGen"
    (* FIXME: Find a way to pass command-line arguments within dune's runtest alias *)
    (let zpath = if (Array.length Sys.argv) > 1 then Sys.argv.(1) else ""
      in [ "Test_ArrayComponents", Test_ArrayComponents.all
         ; "Test_BFL", Test_BFL.all
         ; "Test_Expr", Test_Expr.all
         ; "Test_NormalForm", Test_NormalForm.all
         ; "Test_PIE", Test_PIE.all
         ; "Test_Synthesizer", Test_Synthesizer.all
         ; "Test_Unification", Test_Unification.all
         ; "Test_VPIE", (Test_VPIE.all ~zpath)
         ; "Test_ZProc", (Test_ZProc.all ~zpath)
         ])
let () =
  Alcotest.run ~argv:[| "zpath" |] "LoopInvGen"
    (let zpath = Sys.argv.(1)
      in [ "Test_BFL", Test_BFL.all
         ; "Test_PIE", Test_PIE.all
         ; "Test_VPIE", (Test_VPIE.all ~zpath)
         ; "Test_ZProc", (Test_ZProc.all ~zpath)
         ; "Test_Synthesizer", Test_Synthesizer.all
         ])
let () =
  Alcotest.run "PIE Modules" [
    "Test_BFL"    , Test_BFL.all    ;
    "Test_PIE"    , Test_PIE.all    ;
    "Test_ZProc"  , Test_ZProc.all  ;
    "Test_VPIE"   , Test_VPIE.all   ;
  ]
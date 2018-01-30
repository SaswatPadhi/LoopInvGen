implementation main()
{
  var a: int;
  var b: int;
  var x: int;
  var y: int;
  var z: int;


  anon0:
    assume a >= 0 && b >= 0;
    x := a;
    y := b;
    z := 0;
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} y != 0;
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} y mod 2 != 1;
    x := 2 * x;
    y := y div 2;
    goto anon5_LoopHead;

  anon6_Then:
    assume {:partition} y mod 2 == 1;
    z := z + x;
    y := y - 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} y == 0;
    assert z == a * b;
    return;
}


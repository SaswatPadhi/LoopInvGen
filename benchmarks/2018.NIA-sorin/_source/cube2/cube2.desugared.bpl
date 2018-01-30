implementation main()
{
  var n: int;
  var x: int;
  var y: int;
  var z: int;


  anon0:
    n := 0;
    x := 0;
    y := 1;
    z := 6;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} n < 100;
    n := n + 1;
    x := x + y;
    y := y + z;
    z := z + 6;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} 100 <= n;
    assert x == n * n * n;
    return;
}


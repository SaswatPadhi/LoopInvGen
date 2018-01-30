implementation main()
{
  var n: int;
  var s: int;
  var i: int;
  var j: int;


  anon0:
    assume 1 <= n && n <= 1000;
    s := 0;
    j := 0;
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= n;
    s := s + i;
    j := i;
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} n < i;
    assert 2 * s == n * (n + 1);
    return;
}


implementation main()
{
  var n: int;
  var sum: int;
  var i: int;


  anon0:
    assume 1 <= n && n <= 1000;
    sum := 0;
    i := 1;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= n;
    sum := sum + i;
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} n < i;
    assert 2 * sum == n * (n + 1);
    return;
}


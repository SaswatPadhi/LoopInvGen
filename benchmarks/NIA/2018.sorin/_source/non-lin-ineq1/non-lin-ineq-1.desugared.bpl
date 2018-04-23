implementation main()
{
  var i: int;
  var j: int;
  var k: int;


  anon0:
    i := 0;
    assume i * j <= k;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} j < 1000;
    i := i + 1;
    k := k + j;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} 1000 <= j;
    assert i * j <= k;
    return;
}

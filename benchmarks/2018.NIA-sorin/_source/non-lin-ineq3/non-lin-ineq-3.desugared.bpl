implementation main()
{
  var i: int;
  var k: int;


  anon0:
    i := 0;
    k := 0;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i < 1000;
    i := i + 1;
    k := k + i * i;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} 1000 <= i;
    assert 1000000 <= k;
    return;
}


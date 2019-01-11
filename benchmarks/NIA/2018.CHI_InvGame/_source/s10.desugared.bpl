implementation main()
{
  var i: int;
  var j: int;
  var k: int;


  anon0:
    j := 0;
    i := 10;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} j < 1000;
    i := i + k;
    j := j + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} 1000 <= j;
    assert i == 10 + k * j;
    return;
}


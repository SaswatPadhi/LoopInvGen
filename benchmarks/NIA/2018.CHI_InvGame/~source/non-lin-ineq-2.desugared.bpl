implementation main()
{
  var i: int;
  var j: int;
  var k: int;


  anon0:
    i := 0;
    assume j > 0;
    assume k > 0;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i < j * k;
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} j * k <= i;
    assert i == j * k;
    return;
}

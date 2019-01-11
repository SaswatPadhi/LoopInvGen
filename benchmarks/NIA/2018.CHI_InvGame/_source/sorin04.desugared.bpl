implementation main()
{
  var i: int;
  var a: int;
  var c: int;


  anon0:
    i := 0;
    a := 0;
    c := 0;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i < 10;
    c := c + 6 * a + 1;
    a := a + i + 1;
    i := i + 1;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} 10 <= i;
    assert c == i * i * i;
    return;
}


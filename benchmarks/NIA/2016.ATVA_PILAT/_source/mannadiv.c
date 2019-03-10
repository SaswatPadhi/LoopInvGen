/* Division algorithm from "Z. Manna, Mathematical Theory of Computation, McGraw-Hill, 1974" */

void division (int x1, int x2)
pre(  x1 >= 0   &&   x2 > 0  );
{
  int y1,y2,y3;

  y1 = 0;
  y2 = 0;
  y3 = x1;

  inv( y1* x2 + y2 + y3 == x1 );
  while(y3 != 0) {

    if (y2 + 1 == x2) {

      y1 = y1 + 1;
      y2 = 0;
      y3 = y3 - 1;
    }

    else {
      y2 = y2 + 1;
      y3 = y3 - 1;
    }
  }
}
post(  y2 == x1 % x2  &&  y1 == x1 / x2  );
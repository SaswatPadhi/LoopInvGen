{
  if(NR == 1) {
    header = $1
    next
  }

  data[i++] = $1
  sum += $1;

  if(min == "") min = max = $1;

  if($1 > max) max = $1;
  else if($1 < min) min = $1;
}
END {
  printf "MIN(%s) = %0.3f\n", header, min
  printf "MED(%s) = %0.3f\n", header, data[int((i-1)/2)]
  printf "AVG(%s) = %0.3f\n", header, sum/i
  printf "MAX(%s) = %0.3f\n", header, max
  printf "SUM(%s) = %0.3f\n", header, sum
}
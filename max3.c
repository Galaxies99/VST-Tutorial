int max3(int x, int y, int z)
{
  if (x < y)
    if (y < z)
      return z;
    else
      return y;
  else
    if (x < z)
      return z;
    else
      return x;
}
//C hello world example
#include <stdio.h>

int Fibonacci(int);

int main()
{
  int n, first = 0, second = 1, next = 0, c;

  printf("\nWhich Fibonacci number? ");
  scanf("%d", &n);

  if(n==1)
    next = 1;
  else if (n<0)
    next = -1;

  for(c=1; c<n; c++){
    next = first + second;
    first = second;
    second = next;
  }

  printf("\nValue: %d\n", next);
}

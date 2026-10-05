#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

int64_t sum_squares(int64_t n);

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  printf("%" PRId64 "\n", sum_squares((int64_t)strtoll(argv[1], NULL, 10)));
  return 0;
}

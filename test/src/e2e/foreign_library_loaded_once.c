#include <stdio.h>

__attribute__((constructor)) static void announce(void) {
  printf("loaded\n");
  fflush(stdout);
}

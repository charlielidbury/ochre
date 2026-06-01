/* Hand-written driver to exercise the KaRaMeL-extracted quicksort.
   Not verified — just confirms the extracted C links and actually sorts. */
#include <stdint.h>
#include <stdio.h>
#include "Quicksort.h"

static int check_sorted(const uint32_t *a, uint32_t n) {
  for (uint32_t i = 0; i + 1 < n; i++)
    if (a[i] > a[i + 1]) return 0;
  return 1;
}

int main(void) {
  uint32_t a[] = {5, 3, 8, 1, 9, 2, 7, 0, 6, 4, 3, 8, 1};
  uint32_t n = sizeof(a) / sizeof(a[0]);

  quicksort(a, 0, n);

  printf("sorted: ");
  for (uint32_t i = 0; i < n; i++) printf("%u ", a[i]);
  printf("\n");

  if (!check_sorted(a, n)) { printf("FAIL: not sorted\n"); return 1; }
  printf("OK: sorted\n");
  return 0;
}

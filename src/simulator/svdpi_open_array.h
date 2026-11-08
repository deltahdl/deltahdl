#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct SvOpenArrayDimRange {
  int left;
  int right;
} SvOpenArrayDimRange;

typedef struct SvOpenArrayDesc {
  void* data;
  int n_dims;
  const SvOpenArrayDimRange* ranges;
  size_t elem_size;
  int has_packed_part;
} SvOpenArrayDesc;

#ifdef __cplusplus
}
#endif

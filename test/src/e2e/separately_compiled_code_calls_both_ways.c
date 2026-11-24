#include "svdpi.h"

extern int sv_twice(int value);

svBit probe_bit(const svBitVecVal* vec, int index) {
  return svGetBitselBit(vec, index);
}

svLogic probe_logic(const svLogicVecVal* vec, int index) {
  return svGetBitselLogic(vec, index);
}

void invert(const svBitVecVal* from, svBitVecVal* to) { to[0] = ~from[0]; }

const char* scope_name(void) { return svGetNameFromScope(svGetScope()); }

int call_export(int value) { return sv_twice(value) + 1; }

int shape(const svOpenArrayHandle h) {
  return svSize(h, 1) * 1000 + svLeft(h, 1) * 100 +
         svRight(h, 1) * 10 + svLow(h, 1);
}

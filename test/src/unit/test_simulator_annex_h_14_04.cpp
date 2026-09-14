#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

// §H.14.4, the C side of Example 9, compiled against svdpi.h and its SV3.1a
// companion as the example writes it -- under the names this tree's naming
// rules give C++ code, Pair for the example's pair typedef, F1 for f1 and
// ExportedSvFunc for exported_sv_func, without the const on f1's int
// parameter that those rules read as a constant, and with o3 the
// svLogicPackedArrRef the example passes to svPutLogicVec32 rather than the
// pointer to one its prototype spells: f1 fills two svLogicVec32 chunks from
// the pair, with their d words clear, puts them whole into the output's
// actual representation through the opaque reference, and calls the export
// with an array passed by reference.
struct Pair {
  int x;
  int y;
};

int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, int* o) {
  g_exported_sv_func_i = i;
  for (int k = 0; k < 8; ++k) o[k] = i + k;
}

void F1(int i1, const Pair* i2, svLogicPackedArrRef o3) {
  svLogicVec32 arr[SV_CANONICAL_SIZE(64)]; /* 2 chunks needed */
  int tab[8] = {0};
  arr[0].c = static_cast<unsigned int>(i2->x);
  arr[0].d = 0;
  arr[1].c = static_cast<unsigned int>(i2->y);
  arr[1].d = 0;
  svPutLogicVec32(o3, arr, 64);
  /* call SystemVerilog */
  ExportedSvFunc(i1, tab); /* tab passed by reference */
}

// §H.14.4: the example's 64-bit output takes two chunks under the SV3.1a
// definitions, as under the canonical ones.
TEST(DpiBinaryCompatibleExample, TheOutputTakesTwoChunks) {
  EXPECT_EQ(SV_CANONICAL_SIZE(64), 2);
  EXPECT_EQ(svSizeOfLogicPackedArr(64), 16);
}

// f1 run over the pair {7, 9} with o3 the reference to an actual 64-bit
// logic array: the actual holds x in its first chunk and y in its second,
// both d words clear, and the export was called with i1.
TEST(DpiBinaryCompatibleExample,
     F1FillsTheOutputThroughTheReferenceAndCallsTheExport) {
  const Pair kPair = {7, 9};
  svLogicVecVal actual[2] = {{0, 0}, {0, 0}};
  F1(3, &kPair, actual);
  EXPECT_EQ(actual[0].aval, 7u);
  EXPECT_EQ(actual[0].bval, 0u);
  EXPECT_EQ(actual[1].aval, 9u);
  EXPECT_EQ(actual[1].bval, 0u);
  EXPECT_EQ(g_exported_sv_func_i, 3);
}

// §H.14.4 with §H.14 and §H.14.1: under the "DPI" annotation the runtime
// hands f1 the address of the actual itself as the opaque reference, so what
// f1 puts through it is in the SystemVerilog actual the moment it is put --
// the binary-compatible path, no canonical copy in between.
TEST(DpiBinaryCompatibleExample, TheReferenceIsTheActualUnderTheDpiAnnotation) {
  DpiRuntime rt;
  DpiRtFunction f1;
  f1.sv_name = "f1";
  f1.c_name = "f1";
  f1.packed_arg_passing = DpiPassingSemanticsOfSpecString("DPI");
  rt.RegisterImport(f1);

  const Pair kPair = {7, 9};
  svLogicVecVal actual[2] = {{0, 0}, {0, 0}};
  void* o3 = rt.PackedArgRef("f1", actual);
  ASSERT_EQ(o3, static_cast<void*>(actual));
  F1(3, &kPair, o3);
  EXPECT_EQ(actual[0].aval, 7u);
  EXPECT_EQ(actual[1].aval, 9u);
}

}  // namespace

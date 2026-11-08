#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

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
  svLogicVec32 arr[SV_CANONICAL_SIZE(64)];
  int tab[8] = {0};
  arr[0].c = static_cast<unsigned int>(i2->x);
  arr[0].d = 0;
  arr[1].c = static_cast<unsigned int>(i2->y);
  arr[1].d = 0;
  svPutLogicVec32(o3, arr, 64);
  ExportedSvFunc(i1, tab);
}

TEST(DpiBinaryCompatibleExample, TheOutputTakesTwoChunks) {
  EXPECT_EQ(SV_CANONICAL_SIZE(64), 2);
  EXPECT_EQ(svSizeOfLogicPackedArr(64), 16);
}

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

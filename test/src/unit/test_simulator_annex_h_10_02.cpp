#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

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

int g_tab_last = 0;

void F1(int i1, const Pair* i2, svLogicVecVal* o3) {
  int tab[8] = {0};
  o3[0].aval = static_cast<uint32_t>(i2->x);
  o3[0].bval = 0;
  o3[1].aval = static_cast<uint32_t>(i2->y);
  o3[1].bval = 0;
  ExportedSvFunc(i1, tab);
  g_tab_last = tab[7];
}

DpiArg Formal(const char* name, DataTypeKind type, Direction direction) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  return formal;
}

TEST(DpiPackedArrayExample, TheImportsCHeaderIsTheExamples) {
  DpiArg i2 = Formal("i2", DataTypeKind::kStruct, Direction::kInput);
  i2.type_name = "pair";
  DpiArg o3 = Formal("o3", DataTypeKind::kLogic, Direction::kOutput);
  o3.width = 64;
  EXPECT_EQ(DpiCFunctionHeader(
                "f1", DataTypeKind::kVoid,
                {Formal("i1", DataTypeKind::kInt, Direction::kInput), i2, o3}),
            "void f1(const int i1, const pair* i2, svLogicVecVal* o3)");
}

TEST(DpiPackedArrayExample, TheExportsCHeaderIsTheExamples) {
  EXPECT_EQ(DpiCHeaderOfExportedSubroutine(
                "exported_sv_func", DataTypeKind::kVoid,
                {Formal("i", DataTypeKind::kInt, Direction::kInput),
                 Formal("o", DataTypeKind::kInt, Direction::kOutput)},
                false),
            "void exported_sv_func(const int i, int* o)");
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(
                Formal("o", DataTypeKind::kInt, Direction::kOutput),
                {SvActualDimension{0, 7}}),
            "int o[8]");
}

TEST(DpiPackedArrayExample, TheWideLogicOutputIsTwoChunks) {
  EXPECT_EQ(DpiCanonicalWordCount(64), 2u);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
}

TEST(DpiPackedArrayExample, F1FillsTheOutputFromThePairAndCallsTheExport) {
  const Pair kPair = {7, 9};
  svLogicVecVal o3[SV_PACKED_DATA_NELEMS(64)] = {};
  F1(3, &kPair, o3);
  EXPECT_EQ(o3[0].aval, 7u);
  EXPECT_EQ(o3[0].bval, 0u);
  EXPECT_EQ(o3[1].aval, 9u);
  EXPECT_EQ(o3[1].bval, 0u);
  const DpiArgValue kReceived =
      DpiArgValue::FromLogicVecWords({SvLogicVecVal{o3[0].aval, o3[0].bval},
                                      SvLogicVecVal{o3[1].aval, o3[1].bval}},
                                     64, DataTypeKind::kLogic);
  EXPECT_EQ(kReceived.AsLogicVecWords()[0].aval, 7u);
  EXPECT_EQ(kReceived.AsLogicVecWords()[1].aval, 9u);
  EXPECT_EQ(kReceived.VecWidth(), 64u);
  EXPECT_EQ(g_exported_sv_func_i, 3);
  EXPECT_EQ(g_tab_last, 10);
}

}  // namespace

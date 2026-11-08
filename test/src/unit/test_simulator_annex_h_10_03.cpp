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

struct Triple {
  int a;
  svBitVecVal b[64][SV_PACKED_DATA_NELEMS(6 * 8)];
  int c;
};

int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, svLogicVecVal* o) {
  g_exported_sv_func_i = i;
  o[0].aval = static_cast<uint32_t>(i);
  o[0].bval = 0;
  o[1].aval = static_cast<uint32_t>(i) * 2;
  o[1].bval = 0;
}

uint32_t g_sum_of_low_bytes = 0;
svLogicVecVal g_al[SV_PACKED_DATA_NELEMS(64)] = {};

void F1(const Triple* t) {
  svBitVecVal a_b = 0;
  svLogicVecVal a_l[SV_PACKED_DATA_NELEMS(64)] = {};
  g_sum_of_low_bytes = 0;
  for (int i = 0; i < 64; i++) {
    svGetPartselBit(&a_b, t->b[i], 0, 8);
    g_sum_of_low_bytes += a_b;
  }
  ExportedSvFunc(2, a_l);
  g_al[0] = a_l[0];
  g_al[1] = a_l[1];
}

DpiArg Formal(const char* name, DataTypeKind type, Direction direction) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  return formal;
}

TEST(DpiMixedTypesExample, TheTriplesMembersAreDeclaredAsTheExampleWrites) {
  EXPECT_EQ(DpiCDeclarationOfAggregateMember("a", DataTypeKind::kInt, {}, {}),
            "int a");
  EXPECT_EQ(DpiCDeclarationOfAggregateMember(
                "b", DataTypeKind::kBit,
                {SvActualDimension{6, 1}, SvActualDimension{1, 8}},
                {SvActualDimension{65, 2}}),
            "svBitVecVal b[64][2]");
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(6 * 8), 2);
  EXPECT_EQ(DpiCDeclarationOfAggregateMember("c", DataTypeKind::kInt, {}, {}),
            "int c");
}

TEST(DpiMixedTypesExample, TheCHeadersAreTheExamples) {
  DpiArg t = Formal("t", DataTypeKind::kStruct, Direction::kInput);
  t.type_name = "triple";
  EXPECT_EQ(DpiCFunctionHeader("f1", DataTypeKind::kVoid, {t}),
            "void f1(const triple* t)");
  DpiArg o = Formal("o", DataTypeKind::kLogic, Direction::kOutput);
  o.width = 64;
  EXPECT_EQ(DpiCHeaderOfExportedSubroutine(
                "exported_sv_func", DataTypeKind::kVoid,
                {Formal("i", DataTypeKind::kInt, Direction::kInput), o}, false),
            "void exported_sv_func(const int i, svLogicVecVal* o)");
}

TEST(DpiMixedTypesExample, F1ReadsTheLowBytesOfBAndCallsTheExport) {
  Triple t = {};
  t.a = 1;
  t.c = 3;
  for (int i = 0; i < 64; i++) {
    t.b[i][0] = (static_cast<uint32_t>(i) << 8) | static_cast<uint32_t>(i + 1);
    t.b[i][1] = 0xFFFF;
  }
  F1(&t);
  EXPECT_EQ(g_sum_of_low_bytes, 2080u);
  EXPECT_EQ(g_exported_sv_func_i, 2);
  EXPECT_EQ(g_al[0].aval, 2u);
  EXPECT_EQ(g_al[1].aval, 4u);
  EXPECT_EQ(g_al[0].bval + g_al[1].bval, 0u);
}

}  // namespace

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

// §H.10.3, the C side of Example 3, compiled against this svdpi.h as the
// example writes it -- under the names this tree's naming rules give C++
// code, Triple for the example's triple typedef, F1 for f1 and
// ExportedSvFunc for exported_sv_func: the struct mixing C types with a
// packed bit array member b defined as for bit [6*8-1:0] b [63:0], the
// extern the SystemVerilog export is called through, and f1 reading the
// least significant byte of each word of b by part-select and calling the
// export with a packed logic array it fills in.
struct Triple {
  int a;
  svBitVecVal b[64][SV_PACKED_DATA_NELEMS(6 * 8)];
  int c;
};

// What the example's SystemVerilog function does is elided; this stand-in
// records what it was handed and writes both chunks of its 64-bit output.
int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, svLogicVecVal* o) {
  g_exported_sv_func_i = i;
  o[0].aval = static_cast<uint32_t>(i);
  o[0].bval = 0;
  o[1].aval = static_cast<uint32_t>(i) * 2;
  o[1].bval = 0;
}

// The bytes f1 read out of b, summed, and the output the export filled in.
uint32_t g_sum_of_low_bytes = 0;
svLogicVecVal g_al[SV_PACKED_DATA_NELEMS(64)] = {};

void F1(const Triple* t) {
  svBitVecVal a_b = 0;
  svLogicVecVal a_l[SV_PACKED_DATA_NELEMS(64)] = {};
  g_sum_of_low_bytes = 0;
  for (int i = 0; i < 64; i++) {
    // Read the least significant byte of each word of b into aB.
    svGetPartselBit(&a_b, t->b[i], 0, 8);
    g_sum_of_low_bytes += a_b;
  }
  ExportedSvFunc(2, a_l); /* the export writes data into output arg aL */
  g_al[0] = a_l[0];
  g_al[1] = a_l[1];
}

// A formal of the example's declarations, named and directed.
DpiArg Formal(const char* name, DataTypeKind type, Direction direction) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  return formal;
}

// §H.10.3: the members of the C-compatible triple -- int a, the packed bit
// array b as svBitVecVal b[64][2], its two packed dimensions [6:1][1:8]
// linearized to 48 bits in two chunks and its unpacked [65:2] normalized to
// 64 elements, and int c.
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

// §H.10.3: the C prototypes -- f1 taking the triple by reference to a const
// triple, and the export taking the int and the 64-bit logic output by
// reference to its canonical representation.
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

// The example's f1 run over a triple whose word i of b holds i in its second
// byte and i + 1 in its least significant one: the part-selects read the 64
// low bytes, summing to 2080, and the export was called with 2 and filled
// aL's two chunks.
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

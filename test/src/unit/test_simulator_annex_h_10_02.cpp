#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

// §H.10.2, the C side of Example 2, compiled against this svdpi.h as the
// example writes it -- under the names this tree's naming rules give C++
// code, Pair for the example's pair typedef, F1 for f1 and ExportedSvFunc
// for exported_sv_func: the pair typedef, the extern the SystemVerilog
// export is called through, and f1 filling the canonical representation of
// its 64-bit logic output from the pair and calling back into SystemVerilog
// with an array passed by reference.
struct Pair {
  int x;
  int y;
};

// What the example's SystemVerilog function does is elided; this stand-in
// records what it was handed and writes every element of the output array,
// which is what an exported function taking `output int o [0:7]` may do.
int g_exported_sv_func_i = 0;
void ExportedSvFunc(int i, int* o) {
  g_exported_sv_func_i = i;
  for (int k = 0; k < 8; ++k) o[k] = i + k;
}

// The example's tab is written by SystemVerilog and read afterwards; its
// last element is kept here for the observation.
int g_tab_last = 0;

void F1(int i1, const Pair* i2, svLogicVecVal* o3) {
  int tab[8] = {0};
  o3[0].aval = static_cast<uint32_t>(i2->x);
  o3[0].bval = 0;
  o3[1].aval = static_cast<uint32_t>(i2->y);
  o3[1].bval = 0;
  ExportedSvFunc(i1, tab); /* tab passed by reference */
  g_tab_last = tab[7];
}

// A formal of the example's declarations, named and directed.
DpiArg Formal(const char* name, DataTypeKind type, Direction direction) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  return formal;
}

// §H.10.2: the C prototype f1 has -- the int input by value with const, the
// pair by reference to a const pair, and the 64-bit logic output by
// reference to its canonical representation.
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

// §H.10.2: the header the export has in C, void exported_sv_func(int, int*),
// the output array of ints being passed by reference; and the unpacked
// formal o [0:7] itself is declared int o[8].
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

// §H.10.2: the 64-bit logic output crosses as two svLogicVecVal chunks, the
// number SV_PACKED_DATA_NELEMS gives 64 bits, so that f1 writes o3[0] and
// o3[1] and no more.
TEST(DpiPackedArrayExample, TheWideLogicOutputIsTwoChunks) {
  EXPECT_EQ(DpiCanonicalWordCount(64), 2u);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
}

// The example's f1 run: the pair {7, 9} lands in the output's two chunks as
// aval words with bval 0, so the 64-bit value SystemVerilog receives is
// {y, x}; and the export was called with i1 and handed tab by reference,
// which it filled.
TEST(DpiPackedArrayExample, F1FillsTheOutputFromThePairAndCallsTheExport) {
  const Pair kPair = {7, 9};
  svLogicVecVal o3[SV_PACKED_DATA_NELEMS(64)] = {};
  F1(3, &kPair, o3);
  EXPECT_EQ(o3[0].aval, 7u);
  EXPECT_EQ(o3[0].bval, 0u);
  EXPECT_EQ(o3[1].aval, 9u);
  EXPECT_EQ(o3[1].bval, 0u);
  // The chunks as the runtime carries a 64-bit logic value across.
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

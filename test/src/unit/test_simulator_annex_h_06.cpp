#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.6 (Semantic constraints), restating §35.5.1: formal and actual
// arguments of imported and exported subroutines are bound by the WYSIWYG
// principle -- the callee gets its actuals as specified for its formals and
// the caller's arguments conform to the formal types, by coercion on the
// caller's side where necessary -- no compiler on either side coerces
// between the caller's declared formals and the callee's, the SystemVerilog
// compiler provides the coercion of the actual arguments of every imported
// call, truncating or extending the bits of a packed array whose width
// differs from the formal's, and the imported or exported function's types
// shall match those of the corresponding foreign subroutine. The cases check
// which coercion a packed actual takes to a formal of another width and
// whether the type a C prototype declares for a formal matches the one the
// SystemVerilog declaration requires.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.6: the SystemVerilog compiler coerces a packed actual to the formal's
// width on the caller's side -- 40 bits bound to a 32-bit formal are
// truncated, 8 bound to 16 extended, and 16 bound to 16 take no coercion.
TEST(DpiSemanticConstraints, TheCallerCoercesAPackedActualToTheFormalsWidth) {
  EXPECT_EQ(DpiCoercionOfPackedActual(40, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(8, 16), DpiActualCoercion::kExtend);
  EXPECT_EQ(DpiCoercionOfPackedActual(16, 16), DpiActualCoercion::kNone);
  EXPECT_EQ(DpiCoercionOfPackedActual(33, 32), DpiActualCoercion::kTruncate);
  EXPECT_EQ(DpiCoercionOfPackedActual(32, 33), DpiActualCoercion::kExtend);
}

// §H.6: the C prototype's type for a formal shall match the one the
// SystemVerilog declaration requires of it (§H.7.2) -- const int for an int
// input, int* for an int output, const svBitVecVal* for a bit [7:0] input
// -- the spacing around a * being no part of the type; unsigned int for the
// int input and svLogicVecVal* for the bit output do not match.
TEST(DpiSemanticConstraints, TheCTypeShallMatchTheFormalsType) {
  const DpiArg kIntIn = Formal(DataTypeKind::kInt, Direction::kInput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntIn, false, "const int"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntIn, false, "unsigned int"));
  const DpiArg kIntOut = Formal(DataTypeKind::kInt, Direction::kOutput);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int*"));
  EXPECT_TRUE(DpiCTypeMatchesFormal(kIntOut, false, "int *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kIntOut, false, "const int"));
  const DpiArg kBitsIn = Formal(DataTypeKind::kBit, Direction::kInput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsIn, false, "const svBitVecVal *"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsIn, false, "const unsigned char"));
  const DpiArg kBitsOut = Formal(DataTypeKind::kBit, Direction::kOutput, 8);
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, false, "svBitVecVal*"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, false, "svLogicVecVal*"));
  // An open array formal is the handle in every direction (§H.12), and a
  // pointer to the canonical form is not it.
  EXPECT_TRUE(DpiCTypeMatchesFormal(kBitsOut, true, "const svOpenArrayHandle"));
  EXPECT_FALSE(DpiCTypeMatchesFormal(kBitsOut, true, "svBitVecVal*"));
}

}  // namespace

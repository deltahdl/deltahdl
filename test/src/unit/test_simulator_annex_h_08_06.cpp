#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <type_traits>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

// Annex H.8.6 (Argument passing by handle, open arrays): an argument
// specified as an open, unsized array is always passed by a handle,
// regardless of the direction of the SystemVerilog formal, and is reached
// through library functions; the implementation of a handle is tool
// specific and transparent to the user, the handle being the generic
// pointer void* under the name svOpenArrayHandle; and an argument passed by
// handle shall always have a const qualifier, because the user shall not
// modify the contents of a handle. The cases check the mode and C type an
// open array takes under every direction and type, the handle's own type,
// and that the array behind it is reached through the library functions.

namespace {

DpiArg Formal(DataTypeKind type, Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// §H.8.6: by handle whatever the direction, and whatever the element type,
// the C type being const svOpenArrayHandle every time.
TEST(DpiPassingByHandle, AnOpenArrayIsAHandleUnderEveryDirectionAndType) {
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    for (const DataTypeKind kType :
         {DataTypeKind::kInt, DataTypeKind::kBit, DataTypeKind::kStruct}) {
      const DpiArg kFormal = Formal(kType, kDirection, 8);
      EXPECT_EQ(DpiPassingModeOfFormal(kFormal, true),
                DpiPassingMode::kByHandle);
      EXPECT_EQ(DpiCTypeOfFormal(kFormal, true), DpiCTypeOfHandleArgument());
    }
  }
  EXPECT_EQ(DpiCTypeOfHandleArgument(), "const svOpenArrayHandle");
  EXPECT_FALSE(DpiUserMayModifyHandleContents());
}

// §H.8.6: the handle is the generic pointer, and what it points to is the
// tool's own -- the user reaches the array's dimensions and bounds through
// the library functions of §H.12.2 and never through the pointer's type.
TEST(DpiPassingByHandle, TheHandleIsAGenericPointerReadThroughTheLibrary) {
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {3, 1}, {2, 5}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 3;
  desc.ranges = kRanges;
  desc.elem_size = 0;
  const svOpenArrayHandle kHandle = &desc;
  EXPECT_TRUE(std::is_const<decltype(kHandle)>::value);
  EXPECT_EQ(svDimensions(kHandle), 3);
  EXPECT_EQ(svLow(kHandle, 1), 1);
  EXPECT_EQ(svHigh(kHandle, 1), 3);
  EXPECT_EQ(svLeft(kHandle, 2), 2);
  EXPECT_EQ(svRight(kHandle, 2), 5);
}

// The C functions the design below calls, each reading or writing an open
// array through the handle §H.8.6 passes it by: the sum of an array of ints
// with its first dimension's ranges, the high byte of each element of an array
// of 40-bit vectors with the packed dimension's left bound, the sum of products
// over a two-dimensional array of structs with its sizes, and outputs written
// element by element.
int SumOpenInts(svOpenArrayHandle h) {
  int sum = 0;
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    sum += *static_cast<int*>(svGetArrElemPtr1(h, i));
  }
  return (sum * 10000) + (svLeft(h, 1) * 1000) + (svRight(h, 1) * 100) +
         (svSize(h, 1) * 10) + svIncrement(h, 1) + 1;
}

int HighBytesOf(svOpenArrayHandle h) {
  int acc = 0;
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    svLogicVecVal v[2];
    svGetLogicArrElem1VecVal(v, h, i);
    acc = (acc * 10) + static_cast<int>(v[1].aval & 0xFFU);
  }
  return acc + (svLeft(h, 0) * 1000);
}

struct Coordinates {
  int i;
  int j;
};

int SumOfProducts(svOpenArrayHandle h) {
  int sum = 0;
  for (int a = svLow(h, 1); a <= svHigh(h, 1); ++a) {
    for (int b = svLow(h, 2); b <= svHigh(h, 2); ++b) {
      auto* p = static_cast<Coordinates*>(svGetArrElemPtr2(h, a, b));
      sum += p->i * p->j;
    }
  }
  return (sum * 100) + (svSize(h, 1) * 10) + svSize(h, 2);
}

void FillOpen(svOpenArrayHandle bits, svOpenArrayHandle vecs,
              svOpenArrayHandle ints) {
  for (int i = svLow(bits, 1); i <= svHigh(bits, 1); ++i) {
    svPutBitArrElem1(bits, static_cast<svBit>(i % 2), i);
  }
  for (int i = svLow(vecs, 1); i <= svHigh(vecs, 1); ++i) {
    svLogicVecVal v = {static_cast<uint32_t>(i * 3), 0};
    svPutLogicArrElem1VecVal(vecs, &v, i);
  }
  for (int i = svLow(ints, 1); i <= svHigh(ints, 1); ++i) {
    *static_cast<int*>(svGetArrElemPtr1(ints, i)) = i * i;
  }
}

// A design passing open arrays of each kind to C, run to its end.
void RunOpenArrayDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  typedef struct { int i; int j; } coords;\n"
      "  import \"DPI-C\" function int sum_open(input int a []);\n"
      "  import \"DPI-C\" function int hi_of_each(input logic [39:0] a []);\n"
      "  import \"DPI-C\" function int sum2d(input coords a [][]);\n"
      "  import \"DPI-C\" function void fill_open(output bit b [],\n"
      "      output logic [7:0] v [], output int i []);\n"
      "  int ia [5:2] = '{10, 20, 30, 40};\n"
      "  logic [39:0] la [1:3];\n"
      "  coords ca [11:12][6:8];\n"
      "  bit b [4:7];\n"
      "  logic [7:0] v [3:5];\n"
      "  int ii [7:8];\n"
      "  int s1, s2, s3;\n"
      "  initial begin\n"
      "    la[1] = {8'd1, 32'd0}; la[2] = {8'd2, 32'd0}; la[3] = {8'd3, "
      "32'd0};\n"
      "    foreach (ca[x, y]) begin\n"
      "      ca[x][y].i = x - 10; ca[x][y].j = y - 5;\n"
      "    end\n"
      "    s1 = sum_open(ia);\n"
      "    s2 = hi_of_each(la);\n"
      "    s3 = sum2d(ca);\n"
      "    fill_open(b, v, ii);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"sum_open", reinterpret_cast<void*>(&SumOpenInts)},
       {"hi_of_each", reinterpret_cast<void*>(&HighBytesOf)},
       {"sum2d", reinterpret_cast<void*>(&SumOfProducts)},
       {"fill_open", reinterpret_cast<void*>(&FillOpen)}},
      "annex_h_08_06_open_arrays");
}

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// §H.8.6 with §35.6.1.1: an open array is passed by handle, and its unsized
// dimension takes the actual's range, [5:2] here, its elements reached by
// their own indices.
TEST(DpiOpenArrayArguments, AnOpenArrayOfIntsTakesTheActualsRange) {
  SimFixture f;
  RunOpenArrayDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "s1"), 1005242U);
}

// §H.12.5: an element of packed type is reached through its canonical
// representation, and dimension 0 is the packed part.
TEST(DpiOpenArrayArguments, PackedElementsAreReachedCanonically) {
  SimFixture f;
  RunOpenArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "s2"), 39123U);
}

// §H.12.4: an element of an unpacked struct is reached by its address, in the
// layout C gives the struct, over two unsized dimensions.
TEST(DpiOpenArrayArguments, StructElementsAreReachedByAddress) {
  SimFixture f;
  RunOpenArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "s3"), 1823U);
}

// An open output array is copied back element by element at the indices C
// wrote them under.
TEST(DpiOpenArrayArguments, OpenOutputArraysAreCopiedBack) {
  SimFixture f;
  RunOpenArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "b[5]"), 1U);
  EXPECT_EQ(VariableValue(f, "b[6]"), 0U);
  EXPECT_EQ(VariableValue(f, "v[4]"), 12U);
  EXPECT_EQ(VariableValue(f, "ii[8]"), 64U);
}

}  // namespace

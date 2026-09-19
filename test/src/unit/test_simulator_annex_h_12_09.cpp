#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.12.9, the C side of Example 7, compiled against this svdpi.h as the
// example writes it -- under the names this tree's naming rules give C++
// code, F1 for f1, and without the const the example puts on the handle
// parameters, which those rules read as constants: f1 takes the input and
// the output open array by handle, reads the input's element count, and
// copies the input to the output either by pointer arithmetic over the
// arrays' addresses where both have the C layout, or, implementation
// independently, element by element through the addresses svGetArrElemPtr1
// computes from each array's own low bound upwards.
struct MyType {
  int i;
};

// Which of the example's two branches ran.
bool g_copied_by_pointer_arithmetic = false;

void F1(svOpenArrayHandle hin, svOpenArrayHandle hout) {
  int count = svSize(hin, 1);
  auto* s = static_cast<MyType*>(svGetArrayPtr(hin));
  auto* d = static_cast<MyType*>(svGetArrayPtr(hout));

  if (s != nullptr && d != nullptr) { /* both arrays have C layout */
    g_copied_by_pointer_arithmetic = true;
    /* an efficient solution using pointer arithmetic */
    while (count-- != 0) *d++ = *s++;
  } else { /* less efficient yet implementation independent */
    g_copied_by_pointer_arithmetic = false;
    int i = svLow(hin, 1);
    int j = svLow(hout, 1);
    while (i <= svHigh(hin, 1)) {
      *static_cast<MyType*>(svGetArrElemPtr1(hout, j++)) =
          *static_cast<MyType*>(svGetArrElemPtr1(hin, i++));
    }
  }
}

// An open array of MyType over [11:20], as the example's source and target.
struct TenOfMyType {
  std::vector<MyType> data = std::vector<MyType>(10);
  SvOpenArrayDimRange ranges[2] = {{0, 0}, {11, 20}};
  SvOpenArrayDesc desc;

  TenOfMyType() {
    desc.data = data.data();
    desc.n_dims = 2;
    desc.ranges = ranges;
    desc.elem_size = sizeof(MyType);
  }

  svOpenArrayHandle Handle() { return &desc; }
};

// §H.12.9: both formals are passed by handle, the output as much as the
// input, so f1's C prototype takes two const svOpenArrayHandle.
TEST(DpiOpenArrayExample, BothOpenArrayFormalsAreHandles) {
  DpiArg in;
  in.name = "i";
  in.type = DataTypeKind::kStruct;
  in.type_name = "MyType";
  in.direction = Direction::kInput;
  DpiArg out = in;
  out.name = "o";
  out.direction = Direction::kOutput;
  EXPECT_EQ(DpiCTypeOfFormal(in, true), "const svOpenArrayHandle");
  EXPECT_EQ(DpiCTypeOfFormal(out, true), "const svOpenArrayHandle");
}

// f1(source, target): the ten elements of source arrive in target in order,
// the count read from the input being ten.
TEST(DpiOpenArrayExample, F1CopiesTheSourceIntoTheTarget) {
  TenOfMyType source;
  TenOfMyType target;
  for (int k = 0; k < 10; ++k)
    source.data[static_cast<std::size_t>(k)].i = 100 + k;
  EXPECT_EQ(svSize(source.Handle(), 1), 10);

  F1(source.Handle(), target.Handle());

  for (int k = 0; k < 10; ++k) {
    EXPECT_EQ(target.data[static_cast<std::size_t>(k)].i, 100 + k) << k;
  }
  // The element source[11] is target[11] afterwards, by the arrays' own
  // indices.
  auto* first = static_cast<MyType*>(svGetArrElemPtr1(target.Handle(), 11));
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->i, 100);
}

// §H.12.9 with §H.12.4: under this simulator an open array's whole-array
// address is undefined, so svGetArrayPtr is NULL and f1 takes the
// implementation-independent branch -- the one that works whichever layout
// an implementation gives its arrays.
TEST(DpiOpenArrayExample, TheImplementationIndependentBranchRunsHere) {
  TenOfMyType source;
  TenOfMyType target;
  EXPECT_EQ(svGetArrayPtr(source.Handle()), nullptr);
  F1(source.Handle(), target.Handle());
  EXPECT_FALSE(g_copied_by_pointer_arithmetic);
  EXPECT_FALSE(DpiWholeArrayIsAccessible(false));
}

}  // namespace

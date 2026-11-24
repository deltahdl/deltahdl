#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

struct MyType {
  int i;
};

bool g_copied_by_pointer_arithmetic = false;

void F1(svOpenArrayHandle hin, svOpenArrayHandle hout) {
  int count = svSize(hin, 1);
  auto* s = static_cast<MyType*>(svGetArrayPtr(hin));
  auto* d = static_cast<MyType*>(svGetArrayPtr(hout));

  if (s != nullptr && d != nullptr) {
    g_copied_by_pointer_arithmetic = true;
    while (count-- != 0) *d++ = *s++;
  } else {
    g_copied_by_pointer_arithmetic = false;
    int i = svLow(hin, 1);
    int j = svLow(hout, 1);
    while (i <= svHigh(hin, 1)) {
      *static_cast<MyType*>(svGetArrElemPtr1(hout, j++)) =
          *static_cast<MyType*>(svGetArrElemPtr1(hin, i++));
    }
  }
}

struct TenOfMyType {
  std::vector<MyType> data = std::vector<MyType>(10);
  SvOpenArrayDimRange ranges[2] = {{0, 0}, {11, 20}};
  SvOpenArrayDesc desc;

  TenOfMyType() {
    desc.data = data.data();
    desc.n_dims = 2;
    desc.has_packed_part = 0;
    desc.ranges = ranges;
    desc.elem_size = sizeof(MyType);
  }

  svOpenArrayHandle Handle() { return &desc; }
};

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
  auto* first = static_cast<MyType*>(svGetArrElemPtr1(target.Handle(), 11));
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->i, 100);
}

TEST(DpiOpenArrayExample, DISABLED_ThePointerBranchRunsForArraysInCLayout) {
  TenOfMyType source;
  TenOfMyType target;
  EXPECT_EQ(svGetArrayPtr(source.Handle()),
            static_cast<void*>(source.data.data()));
  F1(source.Handle(), target.Handle());
  EXPECT_TRUE(g_copied_by_pointer_arithmetic);
}

TEST(DpiOpenArrayExample, AnArrayOutsideCLayoutIsNotAccessibleAsAWhole) {
  EXPECT_FALSE(DpiWholeArrayIsAccessible(false));
}

TEST(DpiOpenArrayExample, DISABLED_ADesignsArraysAreCopiedByThePointerBranch) {
  SimFixture f;
  g_copied_by_pointer_arithmetic = false;
  RunModuleWithC(
      "  typedef struct { int i; } MyType;\n"
      "  import \"DPI-C\" function void f1(input MyType i [],\n"
      "                                  output MyType o []);\n"
      "  MyType source [11:20];\n"
      "  MyType target [11:20];\n"
      "  int first, last;\n"
      "  initial begin\n"
      "    foreach (source[k]) source[k].i = k * 3;\n"
      "    f1(source, target);\n"
      "    first = target[11].i; last = target[20].i;\n"
      "  end\n",
      f, {{"f1", CAddress(&F1)}}, "annex_h_12_09_pointer");
  EXPECT_TRUE(g_copied_by_pointer_arithmetic);
  EXPECT_EQ(DesignValue(f, "first"), 33U);
  EXPECT_EQ(DesignValue(f, "last"), 60U);
}

TEST(DpiOpenArrayExample, ADesignsSourceIsCopiedIntoItsTarget) {
  SimFixture f;
  RunModuleWithC(
      "  typedef struct { int i; } MyType;\n"
      "  import \"DPI-C\" function void f1(input MyType i [],\n"
      "                                  output MyType o []);\n"
      "  MyType source [11:20];\n"
      "  MyType target [20:11];\n"
      "  int sum;\n"
      "  initial begin\n"
      "    foreach (source[k]) source[k].i = k * 3;\n"
      "    f1(source, target);\n"
      "    foreach (target[k]) sum += target[k].i;\n"
      "  end\n",
      f, {{"f1", CAddress(&F1)}}, "annex_h_12_09_copy");
  EXPECT_EQ(DesignValue(f, "sum"), 465U);
}

}  // namespace

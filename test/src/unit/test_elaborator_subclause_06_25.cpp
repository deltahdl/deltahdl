#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ParameterizedDataTypesElab, ClassTypedefTakesTheSpecializationsParams) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef logic [SIZE-1:0] t_vector;\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "  endclass\n"
      "  typedef logic [7:0] t_t0;\n"
      "  C#(t_t0,3)::t_vector v0;\n"
      "  C#(t_t0,3)::t_array a0;\n"
      "  initial a0[0] = 200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v0 = FindVar(design, "t", "v0");
  ASSERT_NE(v0, nullptr);
  EXPECT_EQ(v0->width, 3u);
  const RtlirVariable* a0 = FindVar(design, "t", "a0");
  ASSERT_NE(a0, nullptr);
  EXPECT_EQ(a0->width, 8u);
  EXPECT_EQ(a0->unpacked_size, 3u);
}

TEST(ParameterizedDataTypesElab, ClassTypedefTakesDefaultsAndNamedArgs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "  endclass\n"
      "  C#(.SIZE(5))::t_array a1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* a1 = FindVar(design, "t", "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a1->width, 1u);
  EXPECT_EQ(a1->unpacked_size, 5u);
}

TEST(ParameterizedDataTypesElab, VirtualParameterizedClassIsNotConstructed) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class C#(parameter type T = logic, parameter SIZE = 1);\n"
      "  typedef logic [SIZE-1:0] t_vector;\n"
      "endclass\n"
      "module top;\n"
      "  C#(int, 2) h;\n"
      "  C#(int, 2)::t_vector v;\n"
      "  initial h = new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of abstract class", 7,
                            "8.21"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "", 6, "8.21"));
}

}  // namespace

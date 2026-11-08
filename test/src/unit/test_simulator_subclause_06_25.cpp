#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterizedDataTypesSim, SpecializedClassArrayTypedefHoldsItsElements) {
  const std::string kSrc =
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "  endclass\n"
      "  typedef logic [7:0] t_t0;\n"
      "  C#(t_t0,3)::t_array a0;\n"
      "  int eb, e0, sz;\n"
      "  initial begin\n"
      "    a0[0] = 200;\n"
      "    eb = $bits(a0[0]);\n"
      "    e0 = a0[0];\n"
      "    sz = $size(a0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "eb"), 8u);
  EXPECT_EQ(RunAndGet(kSrc, "e0"), 200u);
  EXPECT_EQ(RunAndGet(kSrc, "sz"), 3u);
}

TEST(ParameterizedDataTypesSim,
     SpecializedClassStructTypedefSpecializesMembers) {
  const std::string kSrc =
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef logic [SIZE-1:0] t_vector;\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "    typedef struct {\n"
      "      t_vector m0 [2*SIZE-1:0];\n"
      "      t_array m1;\n"
      "      bit [SIZE-1:0] m2;\n"
      "    } t_struct;\n"
      "  endclass\n"
      "  typedef struct { logic [3:0] m0 [7:0]; } plain_t;\n"
      "  C#(bit,4)::t_struct s0;\n"
      "  plain_t p0;\n"
      "  int b2, e2, same0, bs;\n"
      "  initial begin\n"
      "    s0.m2 = 4'hB;\n"
      "    b2 = $bits(s0.m2);\n"
      "    e2 = s0.m2;\n"
      "    same0 = $bits(s0.m0) == $bits(p0.m0);\n"
      "    bs = $bits(s0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "b2"), 4u);
  EXPECT_EQ(RunAndGet(kSrc, "e2"), 11u);
  EXPECT_EQ(RunAndGet(kSrc, "same0"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "bs"), 40u);
}

TEST(ParameterizedDataTypesSim, StructTypedefThroughATypedefOfASpecialization) {
  const std::string kSrc =
      "module t;\n"
      "  class Base #(parameter p = 1);\n"
      "    typedef struct { real r; bit [p-1:0] data; } S;\n"
      "  endclass\n"
      "  typedef Base#(32) MyBaseT;\n"
      "  MyBaseT::S s;\n"
      "  Base#(16)::S u;\n"
      "  int bs, bu;\n"
      "  longint v;\n"
      "  initial begin\n"
      "    s.data = 32'hDEADBEEF;\n"
      "    bs = $bits(s.data);\n"
      "    bu = $bits(u.data);\n"
      "    v = s.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "bs"), 32u);
  EXPECT_EQ(RunAndGet(kSrc, "bu"), 16u);
  EXPECT_EQ(RunAndGet(kSrc, "v"), 0xDEADBEEFu);
}

}  // namespace

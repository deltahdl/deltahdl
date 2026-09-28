#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.25's parameterized data types at run time: `C#(t_t0,3)::t_array` holds
// three 8-bit elements, so an element keeps 200, $bits of one is 8, and $size
// of the array is 3.
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

// §6.25's t_struct through `C#(bit,4)`: every member is written in the class's
// parameters, so m2 is `bit [3:0]` and holds 4'hB, and the structure is laid
// out as the same structure written with 4 for SIZE and bit for T is: m0 as
// eight 4-bit vectors, m1 as four bits. Reading an element of an unpacked
// array member back is #3884's, for any unpacked structure.
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
      "  typedef logic [3:0] v_t;\n"
      "  typedef bit a_t [3:0];\n"
      "  typedef struct { v_t m0 [7:0]; a_t m1; bit [3:0] m2; } plain_t;\n"
      "  C#(bit,4)::t_struct s0;\n"
      "  plain_t p0;\n"
      "  int b2, e2, same0, same;\n"
      "  initial begin\n"
      "    s0.m2 = 4'hB;\n"
      "    b2 = $bits(s0.m2);\n"
      "    e2 = s0.m2;\n"
      "    same0 = $bits(s0.m0) == $bits(p0.m0);\n"
      "    same = $bits(s0) == $bits(p0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "b2"), 4u);
  EXPECT_EQ(RunAndGet(kSrc, "e2"), 11u);
  EXPECT_EQ(RunAndGet(kSrc, "same0"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "same"), 1u);
}

// §6.6.7's Base#(32) structure reached through `typedef Base#(32) MyBaseT;`
// and written out as Base#(16): the data member is p bits of each.
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

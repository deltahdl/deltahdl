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

}  // namespace

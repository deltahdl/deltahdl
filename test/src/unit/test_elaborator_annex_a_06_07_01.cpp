#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PatternElaboration, AnArrayPatternIndexKeyIsAConstantExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int P = 1;\n"
      "  localparam int Q = 2;\n"
      "  int i = 1;\n"
      "  int a [0:2];\n"
      "  int c [0:2] = '{i: 5, default: 0};\n"
      "  initial begin\n"
      "    a = '{0: 1, i + 1: 2, default: 0};\n"
      "    a = '{P: 5, Q: 6, int: 0};\n"
      "    a = '{0: 1, P + 1: 2, default: 0};\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an array pattern's index key is a constant "
                              "expression, which names no variable",
                              line, "A.6.7.1"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace

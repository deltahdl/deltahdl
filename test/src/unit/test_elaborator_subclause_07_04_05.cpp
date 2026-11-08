#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayIndexingElaboration, IndexedPartSelectWidthParameterAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  parameter W = 8;\n"
             "  logic [31:0] vec;\n"
             "  logic [7:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base +: W];\n"
             "endmodule\n"));
}

TEST(ArrayIndexingElaboration, IndexedPartSelectWidthLocalparamAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  localparam W = 4;\n"
             "  logic [31:0] vec;\n"
             "  logic [3:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base -: W];\n"
             "endmodule\n"));
}

TEST(ArrayIndexingElaboration, NonConstantPartSelectWidthRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] res;\n"
      "  int base;\n"
      "  int n;\n"
      "  initial res = vec[base +: n];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 6, "11.5.1"));
}

}  // namespace

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.4.5: the size of a part-select shall be constant while the position may be
// variable. Per §11.2.1 a constant expression may be a parameter reference, so
// an indexed part-select whose width is a parameter (with a runtime variable
// position) elaborates without error. The width is produced by a real parameter
// declaration so the constant-folding path that resolves it is exercised.
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

// The same constant-size rule admits a localparam as the width. A localparam is
// a distinct declaration form from a parameter, so it is covered separately.
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

// Negative form of the constant-size rule: an indexed part-select whose width
// is a run-time variable (not a constant expression) is rejected at
// elaboration. Only the size must be constant; the position (base) here is
// deliberately also a variable to show it is the width, not the position, that
// is illegal.
TEST(ArrayIndexingElaboration, NonConstantPartSelectWidthRejected) {
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  logic [31:0] vec;\n"
             "  logic [7:0] res;\n"
             "  int base;\n"
             "  int n;\n"
             "  initial res = vec[base +: n];\n"
             "endmodule\n"));
}

}  // namespace

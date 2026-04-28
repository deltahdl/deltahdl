#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ScopeRulesElaboration, ConditionalGenerateBlocksAllowSameIdentifier) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter P = 1;\n"
             "  if (P == 1) begin : g\n"
             "    logic data;\n"
             "  end else begin : g\n"
             "    logic data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DirectVariableReferenceStopsAtModuleBoundary) {
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  initial outer_x = 1;\n"
             "endmodule\n"
             "module parent;\n"
             "  logic outer_x;\n"
             "  child c();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, InstanceNamePrecedenceOverModuleTypeName) {
  EXPECT_TRUE(
      ElabOk("module foo;\n"
             "  integer x;\n"
             "endmodule\n"
             "module top;\n"
             "  foo foo();\n"
             "  initial foo.x = 5;\n"
             "endmodule\n"));
}

}  // namespace

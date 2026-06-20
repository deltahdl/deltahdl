#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.9: an identifier shall be used to declare only one item within a
// scope. Two nets sharing a name in the same module scope is illegal.
TEST(ScopeRulesElaboration, DuplicateIdentifierInSameScopeRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire w;\n"
             "  wire w;\n"
             "endmodule\n"));
}

// §23.9 also forbids naming a task the same as a variable in the same
// module scope; the two declarations collide on one identifier.
TEST(ScopeRulesElaboration, TaskNameMatchingVariableRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic foo;\n"
             "  task foo;\n"
             "  endtask\n"
             "endmodule\n"));
}

// §23.9 spells out one form of that collision explicitly: a gate instance
// shall not share the name of the net connected to its output.
TEST(ScopeRulesElaboration, GateInstanceNameMatchingOutputNetRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire a, b;\n"
             "  and g1(g1, a, b);\n"
             "endmodule\n"));
}

// §23.9: each module opens a new scope, so the same identifier may name an
// item in two different modules without colliding.
TEST(ScopeRulesElaboration, SameNameInSeparateModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire x;\n"
             "endmodule\n"
             "module top;\n"
             "  wire x;\n"
             "  child c();\n"
             "endmodule\n"));
}

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

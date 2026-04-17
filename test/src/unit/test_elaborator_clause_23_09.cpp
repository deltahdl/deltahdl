#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ScopeRulesElaboration, RedeclVarInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, RedeclNetInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire w;\n"
             "  wire w;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, RedeclarationOfVariableAsNetError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ScopeRulesElaboration, RedeclarationOfNetAsVariableError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ScopeRulesElaboration, TaskSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, TaskSameNameAsVariableInInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface i;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endinterface\n"
             "module m;\n"
             "  i inst();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, GateInstanceSameNameAsOutputNetError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire a, b;\n"
             "  wire g;\n"
             "  and g(g, a, b);\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, GenerateBlockDuplicateDeclarationError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
             "    logic x;\n"
             "    wire x;\n"
             "  end\n"
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

TEST(ScopeRulesElaboration, NamedBlockSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic blk;\n"
             "  initial begin : blk\n"
             "    int y;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, ModuleInstanceSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module child; endmodule\n"
             "module top;\n"
             "  logic u;\n"
             "  child u();\n"
             "endmodule\n"));
}

}  // namespace

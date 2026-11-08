#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

void ExpectContainerHoldsStatement(const char* src, ModuleItemKind kind) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindItemByKind(r, kind), nullptr);
}

void ExpectRejectedAtModuleScope(const char* src, uint32_t line) {
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, "unexpected token in module body", line,
                            "23.2.4"));
}

TEST(ProceduralStatementContainment, InitialHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kInitialBlock);
}

TEST(ProceduralStatementContainment, AlwaysHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  always #1 x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysBlock);
}

TEST(ProceduralStatementContainment, AlwaysCombHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x, y;\n"
      "  always_comb x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysCombBlock);
}

TEST(ProceduralStatementContainment, AlwaysLatchHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic en, x, y;\n"
      "  always_latch if (en) x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysLatchBlock);
}

TEST(ProceduralStatementContainment, AlwaysFFHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  always_ff @(posedge clk) x <= y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysFFBlock);
}

TEST(ProceduralStatementContainment, FinalHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  final x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kFinalBlock);
}

TEST(ProceduralStatementContainment, TaskHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  task t;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      ModuleItemKind::kTaskDecl);
}

TEST(ProceduralStatementContainment, FunctionHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  function int f;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      ModuleItemKind::kFunctionDecl);
}

TEST(ProceduralStatementContainment, DelayControlAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  #5 x = 1;\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, SequentialBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  begin x = 1; end\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, ParallelBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  fork x = 1; join\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, WhileLoopAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  while (1) x = 1;\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, ReturnAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  return;\n"
      "endmodule\n",
      2);
}

}  // namespace

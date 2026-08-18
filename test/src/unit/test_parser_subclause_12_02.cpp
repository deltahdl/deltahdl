// Tests for §12.2 "Overview", whose one rule is that "procedural programming
// statements shall be contained within any of the following constructs": the
// six blocks that activate on their own -- initial, always, always_comb,
// always_latch, always_ff and final -- and the two that activate when called,
// task and function.
//
// The rule has two halves and needs both. Each of the eight has to take a
// procedural statement, and a procedural statement written where none of the
// eight is has to be rejected. The rejection is the module-item grammar's,
// §23.2.4, because a statement is not one of the things a module body may
// hold; §12.2 is the clause that says which constructs put one back in reach.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The eight containers, each parsed with one procedural assignment inside and
// read back by the module-item kind it produced. A container that parsed to
// something else would hold the statement somewhere the simulator never runs.
void ExpectContainerHoldsStatement(const char* src, ModuleItemKind kind) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindItemByKind(r, kind), nullptr);
}

// A procedural statement written among a module's items, where none of §12.2's
// eight constructs is. The module body admits no statement, so the report is
// the module-item grammar's.
void ExpectRejectedAtModuleScope(const char* src, uint32_t line) {
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, "unexpected token in module body", line,
                            "23.2.4"));
}

// §12.2: `initial` is a procedural block that automatically activates.
TEST(ProceduralStatementContainment, InitialHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kInitialBlock);
}

// §12.2: `always` is one of the six.
TEST(ProceduralStatementContainment, AlwaysHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  always #1 x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysBlock);
}

// §12.2: `always_comb` is one of the six.
TEST(ProceduralStatementContainment, AlwaysCombHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x, y;\n"
      "  always_comb x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysCombBlock);
}

// §12.2: `always_latch` is one of the six.
TEST(ProceduralStatementContainment, AlwaysLatchHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic en, x, y;\n"
      "  always_latch if (en) x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysLatchBlock);
}

// §12.2: `always_ff` is one of the six.
TEST(ProceduralStatementContainment, AlwaysFFHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  always_ff @(posedge clk) x <= y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysFFBlock);
}

// §12.2: `final` is one of the six, and the one whose statements run after the
// simulation rather than during it.
TEST(ProceduralStatementContainment, FinalHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  final x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kFinalBlock);
}

// §12.2: `task` is a procedural block that activates when called.
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

// §12.2: `function` is the other of the two.
TEST(ProceduralStatementContainment, FunctionHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  function int f;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      ModuleItemKind::kFunctionDecl);
}

// §12.2 with §9.4: a timing control is a procedural statement, so one standing
// among a module's items is outside every construct that may hold it.
TEST(ProceduralStatementContainment, DelayControlAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  #5 x = 1;\n"
      "endmodule\n",
      3);
}

// §12.2 with §9.3.1: a sequential block is a procedural statement, and a
// module body is not a place for one.
TEST(ProceduralStatementContainment, SequentialBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  begin x = 1; end\n"
      "endmodule\n",
      3);
}

// §12.2 with §9.3.2: a parallel block is a procedural statement too.
TEST(ProceduralStatementContainment, ParallelBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  fork x = 1; join\n"
      "endmodule\n",
      3);
}

// §12.2 with §12.7.3: a loop statement is a procedural statement. `while` is
// the loop keyword that names no generate construct, so it reaches the module
// body's own rejection rather than being read as one.
TEST(ProceduralStatementContainment, WhileLoopAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  while (1) x = 1;\n"
      "endmodule\n",
      3);
}

// §12.2 with §12.8: a jump statement is a procedural statement, and `return`
// outside a subroutine has no construct to return from.
TEST(ProceduralStatementContainment, ReturnAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  return;\n"
      "endmodule\n",
      2);
}

}  // namespace

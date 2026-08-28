#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingScopeParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test_prog(input clk, input [7:0] data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(ClockingScopeParse, AmongOtherModuleItems) {
  auto r = Parse(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
  ASSERT_GE(r.cu->modules[0]->items.size(), 4u);
}

TEST(ClockingScopeParse, InChecker) {
  EXPECT_TRUE(
      ParseOk("checker my_check(input clk, input data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endchecker\n"));
}

TEST(ClockingScopeParse, DotAccessToClockvar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sig;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    $display(dom.sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface intf(input clk, input data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

TEST(ClockingScopeParse, InPackageRejected) {
  // §14.7: a clocking block shall not be declared inside a package.
  auto r = Parse(
      "package pkg;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a clocking block shall not be declared inside a package", 2,
      "14.7"));
}

TEST(ClockingScopeParse, DefaultClockingInPackageRejected) {
  // §14.7: the package prohibition applies to any clocking block, including
  // one carrying the "default" qualifier.
  auto r = Parse(
      "package pkg;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a clocking block shall not be declared inside a package", 2,
      "14.7"));
}

// A.1.11 closes anonymous_program_item to task, function, class, interface
// class, covergroup and class constructor declarations plus the null item, and
// no clocking_declaration is among them, so a clocking block written in an
// anonymous program is rejected there whatever clause governs the package
// around it.
//
// §14.7's own package prohibition stays silent on this source. The guard in
// Parser::ParseClockingDecl holds it back while the parser is inside an
// anonymous program, which is what leaves A.1.11's report the only one the run
// records and makes the message this case names the one it must name.
TEST(ClockingScopeParse, InAnonymousProgramInPackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "an anonymous program may contain only task, function, class, interface "
      "class, covergroup, and class constructor declarations",
      3, "A.1.11"));
}

// §14.7: clocking blocks "cannot be declared inside functions, tasks, or
// packages or outside all declarations in a compilation unit". A module
// declaration precedes the clocking block so that the line the report names is
// the `clocking` keyword rather than the first line of the source, which any
// report standing at the start of the file would also name.
TEST(ClockingScopeParse, AtCompilationUnitScopeRejected) {
  auto r = Parse(
      "module m;\n"
      "endmodule\n"
      "clocking cb @(posedge clk);\n"
      "  input data;\n"
      "endclocking\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a clocking block shall not be declared outside all declarations in a "
      "compilation unit",
      3, "14.7"));
}

// §14.7 names the function among the scopes a clocking block cannot be
// declared in.
TEST(ClockingScopeParse, InFunctionRejected) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a clocking block shall not be declared inside a function, task, or "
      "procedural block",
      3, "14.7"));
}

// One mistake draws one report. Parser::RejectClockingDecl reads the
// declaration through its `endclocking` and discards it, so the function body
// resumes at `endfunction` and nothing is left for a second rule to reject.
// Before this, the tokens were read as an expression and drew a §11.2 report
// that a source failing any other way would draw just as readily.
TEST(ClockingScopeParse, InFunctionReportsExactlyOneError) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endfunction\n"
      "endmodule\n");
  uint32_t errors = 0;
  for (const auto& diag : r.diags) {
    if (diag.severity == DiagSeverity::kError) ++errors;
  }
  EXPECT_EQ(errors, 1U);
}

// §14.7 names the task alongside the function. Both reach the same rejection,
// because a task body and a function body both hold statements.
TEST(ClockingScopeParse, InTaskRejected) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a clocking block shall not be declared inside a function, task, or "
      "procedural block",
      3, "14.7"));
}

// §14.7: "Multiple clocking blocks cannot be nested." The inner block stands
// where a clocking_item belongs, and is rejected under the nesting rule rather
// than read as a malformed clocking_item.
TEST(ClockingScopeParse, NestedClockingRejected) {
  auto r = Parse(
      "module m;\n"
      "  clocking outer @(posedge clk);\n"
      "    clocking inner @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "multiple clocking blocks cannot be nested", 3, "14.7"));
}

// §14.7: "A clocking block can only be declared inside a module, interface,
// checker, or program". A class is none of the four.
TEST(ClockingScopeParse, InClassRejected) {
  auto r = Parse(
      "class c;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a clocking block shall not be declared inside a class", 2,
      "14.7"));
}

// One mistake draws one report in a class body too: the class body resumes at
// `endclass` rather than asking for a property name under §8.5 and then
// rejecting each remaining token of the discarded declaration.
TEST(ClockingScopeParse, InClassReportsExactlyOneError) {
  auto r = Parse(
      "class c;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endclass\n");
  uint32_t errors = 0;
  for (const auto& diag : r.diags) {
    if (diag.severity == DiagSeverity::kError) ++errors;
  }
  EXPECT_EQ(errors, 1U);
}

// §14.7 makes a clocking block a declaration in one of four scopes, never a
// procedural statement, so an initial block is not one of the places it may
// stand. This is the third position that reaches the statement rejection,
// beside the function and the task above.
TEST(ClockingScopeParse, InProceduralBlockRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a clocking block shall not be declared inside a function, task, or "
      "procedural block",
      3, "14.7"));
}

// §14.7 permits a clocking block anywhere inside a module, and a generate block
// is inside one, so none of the rejections above may reach it. The `global`
// form is the one §14.14 bars from a generate block, and
// GlobalClockingParse.GlobalClockingInGenerateBlockIsError in
// test/src/unit/test_parser_subclause_14_14.cpp holds that separate rule.
TEST(ClockingScopeParse, InGenerateBlockAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk;\n"
              "  if (1) begin : g\n"
              "    clocking cb @(posedge clk);\n"
              "      input clk;\n"
              "    endclocking\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, MultipleBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  clocking cb2 @(negedge clk);\n"
      "    output b;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) ++count;
  }
  EXPECT_EQ(count, 2);
}

}  // namespace

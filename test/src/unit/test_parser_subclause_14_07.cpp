#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

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
      ParseOk("checker my_check(input logic clk, input logic data);\n"
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
  auto r = Parse(
      "package pkg;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package body cannot hold a clocking block", 2, "14.7"));
}

TEST(ClockingScopeParse, DefaultClockingInPackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package body cannot hold a clocking block", 2, "14.7"));
}

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
  EXPECT_TRUE(ReportedError(
      r.diags, "a package body cannot hold a clocking block", 3, "14.7"));
}

TEST(ClockingScopeParse, AtCompilationUnitScopeRejected) {
  auto r = Parse(
      "module m;\n"
      "endmodule\n"
      "clocking cb @(posedge clk);\n"
      "  input data;\n"
      "endclocking\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a clocking block cannot stand at the top level of a compilation unit", 3,
      "14.7"));
}

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
      "a clocking block cannot stand as a statement of a function, a task or "
      "a procedural block",
      3, "14.7"));
}

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
      "a clocking block cannot stand as a statement of a function, a task or "
      "a procedural block",
      3, "14.7"));
}

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
      r.diags, "a clocking block cannot hold another clocking block", 3,
      "14.7"));
}

TEST(ClockingScopeParse, InClassRejected) {
  auto r = Parse(
      "class c;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a class body cannot hold a clocking block", 2, "14.7"));
}

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
      "a clocking block cannot stand as a statement of a function, a task or "
      "a procedural block",
      3, "14.7"));
}

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

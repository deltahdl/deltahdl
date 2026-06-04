#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endpackage\n"));
}

TEST(ClockingScopeParse, DefaultClockingInPackageRejected) {
  // §14.7: the package prohibition applies to any clocking block, including
  // one carrying the "default" qualifier.
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endpackage\n"));
}

TEST(ClockingScopeParse, InAnonymousProgramInPackageAccepted) {
  // §24.9 permits an anonymous program inside a package; a clocking block
  // there lives in a program scope, so §14.7's package prohibition does not
  // apply.
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  program;\n"
              "    clocking cb @(posedge clk);\n"
              "      input data;\n"
              "    endclocking\n"
              "  endprogram\n"
              "endpackage\n"));
}

TEST(ClockingScopeParse, AtCompilationUnitScopeRejected) {
  // §14.7: a clocking block shall not be declared outside all declarations in
  // a compilation unit.
  EXPECT_FALSE(
      ParseOk("clocking cb @(posedge clk);\n"
              "  input data;\n"
              "endclocking\n"));
}

TEST(ClockingScopeParse, InFunctionRejected) {
  // §14.7: a clocking block shall not be declared inside a function.
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  function void f();\n"
              "    clocking cb @(posedge clk);\n"
              "      input data;\n"
              "    endclocking\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, InTaskRejected) {
  // §14.7: a clocking block shall not be declared inside a task.
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  task t();\n"
              "    clocking cb @(posedge clk);\n"
              "      input data;\n"
              "    endclocking\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, NestedClockingRejected) {
  // §14.7: multiple clocking blocks cannot be nested.
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  clocking outer @(posedge clk);\n"
              "    clocking inner @(posedge clk);\n"
              "      input data;\n"
              "    endclocking\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, InClassRejected) {
  // §14.7: a clocking block may be declared only inside a module, interface,
  // checker, or program. A class is none of these, so a clocking block in a
  // class body is not accepted.
  EXPECT_FALSE(
      ParseOk("class c;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endclass\n"));
}

TEST(ClockingScopeParse, InProceduralBlockRejected) {
  // §14.7: a clocking block is a declaration at module/interface/checker/
  // program level, not a procedural statement, so it cannot appear inside an
  // initial block.
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    clocking cb @(posedge clk);\n"
              "      input data;\n"
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

}

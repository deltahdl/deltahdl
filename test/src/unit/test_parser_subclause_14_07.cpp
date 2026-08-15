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
  // No report of the §14.7 rule exists at this scope: `clocking` opens no
  // top-level declaration, so Parser::ParseTopLevel rejects it under §3.12.1.
  auto r = Parse(
      "clocking cb @(posedge clk);\n"
      "  input data;\n"
      "endclocking\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"));
}

TEST(ClockingScopeParse, InFunctionRejected) {
  // §14.7: a clocking block shall not be declared inside a function.
  // No report of the §14.7 rule exists inside a subroutine: a function body
  // holds statements, so Parser::ParsePrimaryExpr reads the `clocking` on
  // line 3 as the start of an expression and reports §11.2.
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ClockingScopeParse, InTaskRejected) {
  // §14.7: a clocking block shall not be declared inside a task.
  // As in InFunctionRejected: a task body holds statements, so the `clocking`
  // on line 3 is read as the start of an expression and reported under §11.2.
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ClockingScopeParse, NestedClockingRejected) {
  // §14.7: multiple clocking blocks cannot be nested.
  // The inner `clocking` stands where a clocking_item belongs, so
  // Parser::ParseClockingDirection reports §14.3 rather than §14.7.
  auto r = Parse(
      "module m;\n"
      "  clocking outer @(posedge clk);\n"
      "    clocking inner @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected clocking direction", 3, "14.3"));
}

TEST(ClockingScopeParse, InClassRejected) {
  // §14.7: a clocking block may be declared only inside a module, interface,
  // checker, or program. A class is none of these, so a clocking block in a
  // class body is not accepted.
  // No report of the §14.7 rule exists in a class body: `clocking` opens no
  // class member, so Parser::ParseClassMembers falls through to the property
  // form and asks for the property name under §8.5. Parser::Expect names
  // every keyword "token".
  auto r = Parse(
      "class c;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endclass\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got token", 2, "8.5"));
}

TEST(ClockingScopeParse, InProceduralBlockRejected) {
  // §14.7: a clocking block is a declaration at module/interface/checker/
  // program level, not a procedural statement, so it cannot appear inside an
  // initial block.
  // As in InFunctionRejected: the `clocking` on line 3 stands where a
  // statement belongs and is read as the start of an expression, so the
  // report is the §11.2 one.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
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

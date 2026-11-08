#include <gtest/gtest.h>

#include <string>

#include "fixture_checker_elab.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(CheckerElab, ElaborateCheckerWithPorts) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker chk_ports(input logic clk, input logic rst);\n"
      "endchecker\n",
      f, "chk_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(CheckerDeclaration, EmptyCheckerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker\n", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, ModuleDeclaredInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  module inner; endmodule\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a module, interface, or program cannot be "
                            "declared inside checker 'chk'",
                            2, "17.2"));
}

TEST(CheckerDeclaration, NestedCheckerDeclaredInsideCheckerIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  checker inner; endchecker\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, ModuleInstantiatedInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m; endmodule\n"
      "checker chk;\n"
      "  m u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only checkers can be instantiated inside "
                            "checker 'chk'",
                            3, "17.2"));
}

TEST(CheckerDeclaration, InterfaceDeclaredInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  interface inner; endinterface\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a module, interface, or program cannot be "
                            "declared inside checker 'chk'",
                            2, "17.2"));
}

TEST(CheckerDeclaration, ProgramDeclaredInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  program inner; endprogram\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a module, interface, or program cannot be "
                            "declared inside checker 'chk'",
                            2, "17.2"));
}

TEST(CheckerDeclaration, InterfaceInstantiatedInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; endinterface\n"
      "checker chk;\n"
      "  ifc u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only checkers can be instantiated inside "
                            "checker 'chk'",
                            3, "17.2"));
}

TEST(CheckerDeclaration, ProgramInstantiatedInsideCheckerIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "program prog; endprogram\n"
      "checker chk;\n"
      "  prog u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only checkers can be instantiated inside "
                            "checker 'chk'",
                            3, "17.2"));
}

TEST(CheckerDeclaration, InputFormalContinuousDriveIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  assign a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "input formal argument 'a' cannot be modified "
                            "inside checker 'chk'",
                            2, "17.2"));
}

TEST(CheckerDeclaration, LocalVariableContinuousDriveIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  logic c;\n"
      "  assign c = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, OutputFormalContinuousDriveIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic b, output logic q);\n"
      "  assign q = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, CheckerInstantiatedInsideCheckerIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker inner(input logic x); endchecker\n"
      "checker outer(input logic clk);\n"
      "  inner i1(clk);\n"
      "endchecker\n",
      f, "outer");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, CheckerInAModuleNamesTheModulesClockingBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  clocking cb @(posedge clk); input a; endclocking\n"
      "  checker chk(logic x);\n"
      "    a1: assert property (@(cb) x);\n"
      "  endchecker\n"
      "  chk k(a);\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, ANonSingularFormalTakesNoDefault) {
  const char* const kReport = "is not singular, so it may take no default";
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input int a[2] = '{0, 0}, output int b[2] = '{1, 1},\n"
      "            input bit c = 1'b1,\n"
      "            input struct {int x;} d = '{x: 0},\n"
      "            input union {int x;} e = '{x: 0},\n"
      "            input struct packed {bit x;} g = '{x: 1'b0});\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker formal 'd' is not singular", 3, "17.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker formal 'e' is not singular", 4, "17.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "17.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker formal 'a' is not singular", 1, "17.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker formal 'b' is not singular", 1, "17.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 2, "17.2"));
}

TEST(CheckerDeclaration, AnEnclosingDynamicVariablesElementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  int q[$];\n"
      "  int d[];\n"
      "  int a[string];\n"
      "  C h;\n"
      "  int fx[4];\n"
      "  checker c;\n"
      "    a1: assert property (@(posedge clk) q[0] == 1);\n"
      "    a2: assert property (@(posedge clk) d[0] == 1);\n"
      "    a3: assert property (@(posedge clk) a[\"k\"] == 1);\n"
      "    a4: assert property (@(posedge clk) h.v == 1);\n"
      "    a5: assert property (@(posedge clk) fx[0] == 1);\n"
      "  endchecker\n"
      "  c u();\n"
      "endmodule\n",
      f, "m");
  auto reported = [&](const char* name, int line) {
    return ReportedError(f.diag.Diagnostics(),
                         std::string("references a member or element of the "
                                     "dynamic variable '") +
                             name + "'",
                         line, "17.2");
  };
  EXPECT_TRUE(reported("q", 10));
  EXPECT_TRUE(reported("d", 11));
  EXPECT_TRUE(reported("a", 12));
  EXPECT_TRUE(reported("h", 13));
  EXPECT_FALSE(reported("fx", 14));
}

TEST(CheckerDeclaration, AnEnclosingForkBlocksElementIsReported) {
  const char* const kReport =
      "references an element of the fork-join block 'f' of its enclosing "
      "scope";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  initial fork : f\n"
      "    int v = 1;\n"
      "  join\n"
      "  initial begin : b\n"
      "    int w = 1;\n"
      "  end\n"
      "  checker c;\n"
      "    a1: assert property (@(posedge clk) f.v == 1);\n"
      "    a2: assert property (@(posedge clk) b.w == 1);\n"
      "  endchecker\n"
      "  c u();\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 10, "17.2"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "fork-join block", 11, "17.2"));
}

TEST(CheckerDeclaration, ATypedefIndexAndAPackageClassAreDynamic) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class C; int v; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  typedef int idx_t;\n"
      "  logic clk;\n"
      "  int a[idx_t];\n"
      "  C h;\n"
      "  checker c;\n"
      "    a1: assert property (@(posedge clk) a[0] == 1);\n"
      "    a2: assert property (@(posedge clk) h.v == 1);\n"
      "  endchecker\n"
      "  c u();\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "references a member or element of the dynamic "
                            "variable 'a'",
                            11, "17.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "references a member or element of the dynamic "
                            "variable 'h'",
                            12, "17.2"));
}

TEST(CheckerDeclaration, AVariableDeclaredThroughATypedefIsDynamicAsItsType) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "module m;\n"
      "  typedef int q_t[$];\n"
      "  typedef C c_t;\n"
      "  typedef int f_t[4];\n"
      "  logic clk;\n"
      "  q_t q;\n"
      "  c_t h;\n"
      "  f_t fx;\n"
      "  checker c;\n"
      "    a1: assert property (@(posedge clk) q[0] == 1);\n"
      "    a2: assert property (@(posedge clk) h.v == 1);\n"
      "    a3: assert property (@(posedge clk) fx[0] == 1);\n"
      "  endchecker\n"
      "  c u();\n"
      "endmodule\n",
      f, "m");
  auto reported = [&](const char* name, int line) {
    return ReportedError(f.diag.Diagnostics(),
                         std::string("references a member or element of the "
                                     "dynamic variable '") +
                             name + "'",
                         line, "17.2");
  };
  EXPECT_TRUE(reported("q", 11));
  EXPECT_TRUE(reported("h", 12));
  EXPECT_FALSE(reported("fx", 13));
}

TEST(CheckerDeclaration, AFormalNamingAnInterfaceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface other; endinterface\n"
      "interface ifc; logic s; endinterface\n"
      "module m; endmodule\n"
      "checker c(logic a, ifc i, m j);\n"
      "endchecker\n",
      f, "c");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker formal 'i' names interface 'ifc'; its "
                            "type shall be one a property formal can take",
                            4, "17.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "checker formal 'j' names",
                             4, "17.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "checker formal 'a' names",
                             4, "17.2"));
}

TEST(CheckerDeclaration, AFormalNamingALaterTypedefOrClassIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface T; endinterface\n"
      "interface C; endinterface\n"
      "checker c(T x, C y);\n"
      "endchecker\n"
      "typedef logic T;\n"
      "class C; endclass\n",
      f, "c");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "checker formal 'x' names",
                             3, "17.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "checker formal 'y' names",
                             3, "17.2"));
}

}  // namespace

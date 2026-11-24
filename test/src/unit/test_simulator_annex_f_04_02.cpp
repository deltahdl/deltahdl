#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Assertion(const std::string& value) {
  return "int n;\n  a1: assert property (@(posedge clk) " + value +
         " == 1) n++;\n";
}

std::string Procedure(const std::string& value) {
  return "int n;\n  always_ff @(posedge clk) n <= n + (" + value + " == 1);\n";
}

std::string Clocked(const std::string& body) {
  return "  logic clk = 0;\n"
         "  initial repeat (20) #5 clk = ~clk;\n" +
         body;
}

void ExpectRun(const std::string& src, const std::string& line) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_NE(out.find(line + "\n"), std::string::npos) << src << out;
}

std::string Show(const std::string& path) {
  return "  initial #98 $display(\"n=%0d\", " + path + ");\n";
}

std::string Top(const std::string& body, const std::string& path) {
  return "module m;\n" + Clocked(body) + Show(path) + "endmodule\n";
}

std::string Checker(const std::string& name, const std::string& ports,
                    const std::string& body) {
  return "checker " + name + ports + ";\n  " + body + "endchecker\n";
}

std::string ElementOf(const std::string& keyword, const std::string& body) {
  return keyword + " sub(input logic clk);\n  logic x = 1;\n" +
         Checker("c", "", body) + "  c u();\n" + Show("u.n") + "end" + keyword +
         "\n";
}

void ExpectElementRead(const std::string& keyword, const std::string& body) {
  ExpectRun(
      ElementOf(keyword, body) + Top("  logic x = 0;\n  sub s(clk);\n", "x"),
      "n=10");
}

TEST(CheckerBodyNames, AnInterfacesCheckerReadsTheInterfaceInAnAssertion) {
  ExpectElementRead("interface", Assertion("x"));
}

TEST(CheckerBodyNames, AnInterfacesCheckerReadsTheInterfaceInAProcedure) {
  ExpectElementRead("interface", Procedure("x"));
}

TEST(CheckerBodyNames, AProgramsCheckerReadsTheProgramInAnAssertion) {
  ExpectElementRead("program", Assertion("x"));
}

TEST(CheckerBodyNames, AProgramsCheckerReadsTheProgramInAProcedure) {
  ExpectElementRead("program", Procedure("x"));
}

std::string ShadowingGenerate(const std::string& body) {
  return Top("  int k;\n  logic x = 1;\n" + Checker("c", "", body) +
                 "  if (1) begin : g\n    logic x = 0;\n    c u();\n"
                 "    initial #90 k = u.n;\n  end\n",
             "k");
}

TEST(CheckerBodyNames, DISABLED_AModulesCheckerReadsTheModuleInAnAssertion) {
  ExpectRun(ShadowingGenerate(Assertion("x")), "n=9");
}

TEST(CheckerBodyNames, DISABLED_AModulesCheckerReadsTheModuleInAProcedure) {
  ExpectRun(ShadowingGenerate(Procedure("x")), "n=9");
}

std::string NamedBlock(const std::string& body) {
  return Top("  initial begin : b\n    static int w = 1;\n  end\n" +
                 Checker("c", "", body) + "  c u();\n",
             "u.n");
}

TEST(CheckerBodyNames, DISABLED_ANamedBlocksVariableIsReadInAnAssertion) {
  ExpectRun(NamedBlock(Assertion("b.w")), "n=10");
}

TEST(CheckerBodyNames, ANamedBlocksVariableIsReadInAProcedure) {
  ExpectRun(NamedBlock(Procedure("b.w")), "n=10");
}

TEST(CheckerBodyNames, DISABLED_APathFromTheModuleIsReadInAnAssertion) {
  ExpectRun(NamedBlock(Assertion("m.b.w")), "n=10");
}

TEST(CheckerBodyNames, APathFromTheModuleIsReadInAProcedure) {
  ExpectRun(NamedBlock(Procedure("m.b.w")), "n=10");
}

std::string GenerateBlocks(const std::string& body) {
  return Top(
      "  if (1) begin : g\n    logic y = 1;\n  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : h\n"
      "    logic z = (i == 1);\n  end\n" +
          Checker("c", "", body) + "  c u();\n",
      "u.n");
}

TEST(CheckerBodyNames, DISABLED_AGenerateBlocksVariableIsReadInAnAssertion) {
  ExpectRun(GenerateBlocks(Assertion("g.y")), "n=10");
}

TEST(CheckerBodyNames, AGenerateBlocksVariableIsReadInAProcedure) {
  ExpectRun(GenerateBlocks(Procedure("g.y")), "n=10");
}

TEST(CheckerBodyNames, DISABLED_ALoopBlocksVariableIsReadInAnAssertion) {
  ExpectRun(GenerateBlocks(Assertion("h[1].z")), "n=10");
}

TEST(CheckerBodyNames, ALoopBlocksVariableIsReadInAProcedure) {
  ExpectRun(GenerateBlocks(Procedure("h[1].z")), "n=10");
}

std::string GenerateDeclared(const std::string& body) {
  return Top(
      "  int k;\n  logic v = 1;\n  logic y = 0;\n  if (1) begin : g\n"
      "    logic y = 1;\n" +
          Checker("gc", "", body) +
          "    gc u();\n    initial #90 k = u.n;\n  end\n",
      "k");
}

TEST(CheckerBodyNames,
     DISABLED_AGenerateBlocksCheckerReadsTheBlockInAnAssertion) {
  ExpectRun(GenerateDeclared(Assertion("y")), "n=9");
}

TEST(CheckerBodyNames,
     DISABLED_AGenerateBlocksCheckerReadsTheBlockInAProcedure) {
  ExpectRun(GenerateDeclared(Procedure("y")), "n=9");
}

TEST(CheckerBodyNames, DISABLED_AGenerateBlocksCheckerReadsTheModuleAroundIt) {
  ExpectRun(GenerateDeclared(Assertion("v")), "n=9");
  ExpectRun(GenerateDeclared(Procedure("v")), "n=9");
}

std::string PackageChecker(const std::string& body) {
  return "package pk;\n  logic pv = 1;\n" +
         Checker("pc", "(logic a, logic clk)", body) + "endpackage\n" +
         Top("  logic pv = 0;\n  pk::pc u(pv, clk);\n", "u.n");
}

TEST(CheckerBodyNames, DISABLED_APackagesCheckerReadsThePackageInAnAssertion) {
  ExpectRun(PackageChecker(Assertion("pv")), "n=10");
}

TEST(CheckerBodyNames, DISABLED_APackagesCheckerReadsThePackageInAProcedure) {
  ExpectRun(PackageChecker(Procedure("pv")), "n=10");
}

TEST(CheckerBodyNames, APackagesCheckerReadsAPackageScopedName) {
  ExpectRun(PackageChecker(Assertion("pk::pv")), "n=10");
  ExpectRun(PackageChecker(Procedure("pk::pv")), "n=10");
}

TEST(CheckerBodyNames,
     DISABLED_APackagesCheckerInstantiatesItsPackagesChecker) {
  ExpectRun("package pk;\n" + Checker("inner", "(logic clk)", Assertion("1")) +
                Checker("outer", "(logic clk)", "inner i(clk);\n") +
                "endpackage\n" + Top("  pk::outer u(clk);\n", "u.i.n"),
            "n=10");
}

std::string UnitChecker(const std::string& body) {
  return "logic x = 1;\n" + Checker("c", "(logic a, logic clk)", body) +
         "module sub(input logic clk);\n  logic x = 0;\n  c u(x, clk);\n"
         "endmodule\n" +
         Top("  logic x = 0;\n  logic y = 1;\n  c u(x, clk);\n"
             "  sub s(clk);\n",
             "u.n + 100 * s.u.n");
}

TEST(CheckerBodyNames, ACompilationUnitsCheckerReadsTheUnitInAnAssertion) {
  ExpectRun(UnitChecker(Assertion("x")), "n=1010");
}

TEST(CheckerBodyNames, ACompilationUnitsCheckerReadsTheUnitInAProcedure) {
  ExpectRun(UnitChecker(Procedure("x")), "n=1010");
}

TEST(CheckerBodyNames,
     DISABLED_ACompilationUnitsCheckerReadsAnUpwardNameInAnAssertion) {
  ExpectRun(UnitChecker(Assertion("m.y")), "n=1010");
}

TEST(CheckerBodyNames, ACompilationUnitsCheckerReadsAnUpwardNameInAProcedure) {
  ExpectRun(UnitChecker(Procedure("m.y")), "n=1010");
}

std::string NestedChecker(const std::string& body) {
  return Top("  logic v = 1;\n  logic q = 0;\n" +
                 Checker("outer", "",
                         "logic q = 1;\n" + Checker("inner", "", body) +
                             "  inner i();\n") +
                 "  outer u();\n",
             "u.i.n");
}

TEST(CheckerBodyNames, ANestedCheckerReadsTheOuterChecker) {
  ExpectRun(NestedChecker(Assertion("q")), "n=10");
  ExpectRun(NestedChecker(Procedure("q")), "n=10");
}

TEST(CheckerBodyNames, ANestedCheckerReadsTheModuleAroundBoth) {
  ExpectRun(NestedChecker(Assertion("v")), "n=10");
  ExpectRun(NestedChecker(Procedure("v")), "n=10");
}

std::string OwnVariable(const std::string& body) {
  return Top("  logic y = 0;\n" +
                 Checker("c", "(logic a)", "logic y = 1;\n  " + body) +
                 "  c u(y);\n",
             "u.n");
}

TEST(CheckerBodyNames, TheCheckersOwnVariableHidesAnOuterOne) {
  ExpectRun(OwnVariable(Assertion("y")), "n=10");
  ExpectRun(OwnVariable(Procedure("y")), "n=10");
}

std::string HidingFormal(const std::string& body) {
  return Top("  logic x = 0;\n  logic w = 1;\n" +
                 Checker("c", "(logic x)", body) + "  c u(w);\n",
             "u.n");
}

TEST(CheckerBodyNames, TheCheckersFormalHidesAnOuterVariable) {
  ExpectRun(HidingFormal(Assertion("x")), "n=10");
  ExpectRun(HidingFormal(Procedure("x")), "n=10");
}

TEST(CheckerActualNames, AShadowedActualReadsTheInstancingScope) {
  ExpectRun(UnitChecker(Assertion("!a")), "n=1010");
  ExpectRun(UnitChecker(Procedure("!a")), "n=1010");
}

TEST(CheckerActualNames, TheCheckersOwnVariableDoesNotCaptureTheActual) {
  ExpectRun(OwnVariable(Assertion("!a")), "n=10");
  ExpectRun(OwnVariable(Procedure("!a")), "n=10");
}

TEST(CheckerActualNames, APackageCheckersActualReadsTheInstancingModule) {
  ExpectRun(PackageChecker(Assertion("!a")), "n=10");
  ExpectRun(PackageChecker(Procedure("!a")), "n=10");
}

}  // namespace

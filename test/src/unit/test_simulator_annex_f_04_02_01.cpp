#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string CheckerOf(const std::string& ports, const std::string& items) {
  return "checker ck(" + ports + ");\n  int n = 0, k = 0;\n" + items +
         "endchecker\n";
}

std::string TopOf(const std::string& decls, const std::string& actuals) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  initial repeat (20) #5 clk = ~clk;\n"
         "  bit a = 1, b = 1, z = 0;\n" +
         decls + "  ck u(" + actuals +
         ");\n"
         "  initial #98 $display(\"n=%0d k=%0d\", u.n, u.k);\n"
         "endmodule\n";
}

void ExpectLine(const std::string& src, int n, int k) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::string line =
      "n=" + std::to_string(n) + " k=" + std::to_string(k) + "\n";
  EXPECT_NE(out.find(line), std::string::npos) << src << out;
}

std::string Counted(const std::string& property) {
  return "  assert property (" + property + ") n++; else k++;\n";
}

void ExpectFormal(const std::string& formal, const std::string& decls,
                  const std::string& actual, const std::string& body,
                  bool holds) {
  ExpectLine(CheckerOf(formal + ", event c", Counted("@c " + body)) +
                 TopOf(decls, actual + ", posedge clk"),
             holds ? 10 : 0, holds ? 0 : 10);
}

void ExpectReads(const std::string& formal, const std::string& decls,
                 const std::string& actual, const std::string& body) {
  ExpectFormal(formal, decls, actual, body, true);
  ExpectFormal(formal, decls, actual, "!(" + body + ")", false);
}

void ExpectFormalInProcedure(const std::string& formal,
                             const std::string& decls,
                             const std::string& actual, const std::string& body,
                             int count) {
  ExpectLine(CheckerOf(formal + ", event c",
                       "  always_ff @c n <= n + (" + body + ");\n") +
                 TopOf(decls, actual + ", posedge clk"),
             count, 0);
}

std::string Nibbles() {
  return "  logic [3:0] p = 15, q = 1;\n"
         "  logic signed [3:0] sa = 4'sb1000;\n";
}

TEST(CheckerUntypedFormal, AnOperatorActualIsSelfDetermined) {
  ExpectReads("x", Nibbles(), "p + q", "x == 0");
  ExpectReads("x", Nibbles(), "p + q", "x + 8'd16 == 16");
}

TEST(CheckerUntypedFormal, AnOperatorActualIsSelfDeterminedInAProcedure) {
  ExpectFormalInProcedure("x", Nibbles(), "p + q", "x + 8'd16 == 16", 10);
}

TEST(CheckerUntypedFormal, DISABLED_ASignedOperatorKeepsItsSigning) {
  ExpectReads("x", Nibbles(), "sa >>> 1", "x == 8'h0C");
}

TEST(CheckerUntypedFormal, AnOperatorActualIsOneTerm) {
  ExpectReads("x", "", "a || z", "(x && 1'b0) == 0");
  ExpectReads("x", "", "z | a", "(x & 1'b1) == 1");
}

TEST(CheckerUntypedFormal, DISABLED_AVectorIsSelectedFrom) {
  std::string decls = "  logic [7:0] vec = 8'h24;\n";
  ExpectReads("x", decls, "vec", "x[2]");
  ExpectReads("x", decls, "vec", "x[7:4] == 2");
}

TEST(CheckerUntypedFormal, DISABLED_AVectorIsSelectedFromInAProcedure) {
  std::string decls = "  logic [7:0] vec = 8'h24;\n";
  ExpectFormalInProcedure("x", decls, "vec", "x[2]", 10);
  ExpectFormalInProcedure("x", decls, "vec", "x[3]", 0);
}

TEST(CheckerUntypedFormal, DISABLED_AStructuresMemberIsRead) {
  ExpectReads("x", "  struct packed { logic [3:0] hi, lo; } pr = 8'h25;\n",
              "pr", "x.lo == 5 && x.hi == 2");
}

TEST(CheckerUntypedFormal, DISABLED_AStructuresMemberIsReadInAProcedure) {
  ExpectFormalInProcedure(
      "x", "  struct packed { logic [3:0] hi, lo; } pr = 8'h25;\n", "pr",
      "x.lo == 5 && x.hi == 2", 10);
}

TEST(CheckerUntypedFormal, DISABLED_AnUnpackedStructuresMemberIsRead) {
  ExpectReads("x", "  struct { int hi, lo; } pr = '{2, 5};\n", "pr",
              "x.lo == 5 && x.hi == 2");
}

TEST(CheckerUntypedFormal, DISABLED_AFixedArraysElementIsRead) {
  ExpectReads("x", "  int arr[3] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

TEST(CheckerUntypedFormal, DISABLED_ADynamicArraysElementIsRead) {
  ExpectReads("x", "  int arr[] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

TEST(CheckerUntypedFormal, DISABLED_AQueuesElementIsRead) {
  ExpectReads("x", "  int arr[$] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

std::string Associative(const std::string& index, const std::string& key) {
  return "  int arr[" + index + "];\n  initial arr[" + key + "] = 5;\n";
}

TEST(CheckerUntypedFormal, DISABLED_AnAssociativeArraysElementIsRead) {
  ExpectReads("x", Associative("int", "7"), "arr", "x[7] == 5");
}

TEST(CheckerUntypedFormal, DISABLED_AStringIndexedArraysElementIsRead) {
  ExpectReads("x", Associative("string", "\"s\""), "arr", "x[\"s\"] == 5");
}

TEST(CheckerUntypedFormal, DISABLED_AnAssociativeArraysMethodsAreCalled) {
  ExpectReads("x", Associative("int", "7"), "arr",
              "(x.num() == 1 && x.exists(7))");
}

TEST(CheckerTypedFormal, ABitFormalReadsTheCastActual) {
  ExpectReads("bit x", "", "8'h02", "x == 0");
  ExpectReads("bit x", "", "8'h03", "x == 1");
}

TEST(CheckerTypedFormal, ABitFormalReadsTheCastActualInAProcedure) {
  ExpectFormalInProcedure("bit x", "", "8'h02", "x", 0);
  ExpectFormalInProcedure("bit x", "", "8'h03", "x", 10);
}

TEST(CheckerTypedFormal, AVectorFormalNarrowsItsActual) {
  ExpectReads("logic [1:0] x", "  logic [7:0] v = 8'h0e;\n", "v", "x == 2");
  ExpectReads("logic [1:0] x", "  logic [7:0] v = 8'h0e;\n", "v",
              "$bits(x) == 2");
}

TEST(CheckerTypedFormal, AVectorFormalNarrowsItsActualInAProcedure) {
  ExpectFormalInProcedure("logic [1:0] x", "  logic [7:0] v = 8'h0e;\n", "v",
                          "x == 2 && $bits(x) == 2", 10);
}

TEST(CheckerTypedFormal, AFixedArrayFormalReadsItsActualsElement) {
  ExpectReads("int x[3]", "  int arr[3] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

TEST(CheckerTypedFormal, DISABLED_ADynamicArrayFormalReadsItsActualsElement) {
  ExpectReads("int x[]", "  int arr[] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

TEST(CheckerTypedFormal, DISABLED_AQueueFormalReadsItsActualsElement) {
  ExpectReads("int x[$]", "  int arr[$] = '{4, 5, 6};\n", "arr", "x[1] == 5");
}

TEST(CheckerTypedFormal,
     DISABLED_AnAssociativeArrayFormalReadsItsActualsElement) {
  ExpectReads("int x[int]", Associative("int", "7"), "arr", "x[7] == 5");
}

TEST(CheckerTypedFormal,
     DISABLED_AStringIndexedArrayFormalReadsItsActualsElement) {
  ExpectReads("int x[string]", Associative("string", "\"s\""), "arr",
              "x[\"s\"] == 5");
}

TEST(CheckerTypedFormal, DISABLED_AnAssociativeArrayFormalsMethodsAreCalled) {
  ExpectReads("int x[int]", Associative("int", "7"), "arr",
              "(x.num() == 1 && x.exists(7))");
}

std::string Named() {
  return "  property pd(x); x; endproperty\n"
         "  sequence sd(x); x; endsequence\n";
}

void ExpectInstanceActual(const std::string& formal, const std::string& passing,
                          const std::string& failing) {
  for (const char* use : {"  assert property (@c f) n++; else k++;\n",
                          "  assume property (@c f) n++; else k++;\n"}) {
    ExpectLine(CheckerOf(formal + " f, event c", use) +
                   TopOf(Named(), passing + ", posedge clk"),
               10, 0);
    ExpectLine(CheckerOf(formal + " f, event c", use) +
                   TopOf(Named(), failing + ", posedge clk"),
               0, 10);
  }
  std::string cover =
      CheckerOf(formal + " f, event c", "  cover property (@c f) n++;\n");
  ExpectLine(cover + TopOf(Named(), passing + ", posedge clk"), 10, 0);
  ExpectLine(cover + TopOf(Named(), failing + ", posedge clk"), 0, 0);
}

TEST(CheckerPropertyFormal, DISABLED_APropertyInstanceStandsForIt) {
  ExpectInstanceActual("property", "pd(a)", "pd(z)");
}

TEST(CheckerPropertyFormal, DISABLED_ASequenceInstanceStandsForIt) {
  ExpectInstanceActual("property", "sd(a)", "sd(z)");
}

TEST(CheckerPropertyFormal, DISABLED_APropertyInstanceStandsUnderAnOperator) {
  ExpectInstanceActual("property", "pd(a) and a", "pd(z) and a");
  ExpectInstanceActual("property", "not pd(z)", "not pd(a)");
  ExpectInstanceActual("property", "a |-> pd(a)", "a |-> pd(z)");
}

TEST(CheckerPropertyFormal, APropertyExpressionStandsForIt) {
  ExpectInstanceActual("property", "a and b", "a and z");
}

TEST(CheckerSequenceFormal, DISABLED_ASequenceInstanceStandsForIt) {
  ExpectInstanceActual("sequence", "sd(a)", "sd(z)");
}

TEST(CheckerSequenceFormal, ASequenceHoldingAnInstanceStandsForIt) {
  ExpectInstanceActual("sequence", "sd(a) ##0 a", "sd(z) ##0 a");
}

TEST(CheckerUntypedFormal,
     DISABLED_AnInstanceOfASequenceOrPropertyStandsForIt) {
  ExpectInstanceActual("untyped", "sd(a)", "sd(z)");
  ExpectInstanceActual("untyped", "pd(a)", "pd(z)");
}

void ExpectClockedActual(const std::string& formal, const std::string& decls,
                         const std::string& actual) {
  ExpectLine(CheckerOf(formal + " f", Counted("f")) + TopOf(decls, actual), 10,
             0);
}

TEST(CheckerPropertyFormal, DISABLED_AClockedPropertyInstanceGivesItsClock) {
  ExpectClockedActual(
      "property", "  property pc(x); @(posedge clk) x; endproperty\n", "pc(a)");
}

TEST(CheckerSequenceFormal, DISABLED_AClockedSequenceInstanceGivesItsClock) {
  ExpectClockedActual(
      "sequence", "  sequence sc(x); @(posedge clk) x; endsequence\n", "sc(a)");
}

TEST(CheckerPropertyFormal, AClockedPropertyExpressionGivesItsClock) {
  ExpectClockedActual("property", "", "@(posedge clk) a");
}

TEST(CheckerPropertyFormal,
     DISABLED_AGloballyClockedInstanceTakesTheGlobalClock) {
  ExpectLine(CheckerOf("property p, sequence s",
                       Counted("p") + "  cover property (s) k++;\n") +
                 TopOf("  global clocking @(posedge clk); endclocking\n"
                       "  property p2(x); @($global_clock) x; endproperty\n"
                       "  bit c = 0;\n"
                       "  initial #50 c = 1;\n",
                       "p2(a), @($global_clock) a[*1:$] ##1 c"),
             10, 9);
}

std::string PackageDecls() {
  return "package pk;\n" + Named() + "endpackage\n";
}

TEST(CheckerPropertyFormal, DISABLED_AnImportedInstanceStandsForIt) {
  ExpectLine(PackageDecls() +
                 CheckerOf("property p, event c", Counted("@c p")) +
                 TopOf("  import pk::*;\n", "pd(a), posedge clk"),
             10, 0);
}

TEST(CheckerSequenceFormal, DISABLED_AnImportedInstanceStandsForIt) {
  ExpectLine(PackageDecls() +
                 CheckerOf("sequence s, event c", Counted("@c s")) +
                 TopOf("  import pk::*;\n", "sd(a), posedge clk"),
             10, 0);
}

std::string InterfaceDecls() {
  return "interface ifc;\n" + Named() + "endinterface\n";
}

TEST(CheckerPropertyFormal, DISABLED_AnInterfacesInstanceStandsForIt) {
  ExpectLine(InterfaceDecls() +
                 CheckerOf("property p, event c", Counted("@c p")) +
                 TopOf("  ifc i();\n", "i.pd(a), posedge clk"),
             10, 0);
}

TEST(CheckerSequenceFormal, DISABLED_AnInterfacesInstanceStandsForIt) {
  ExpectLine(InterfaceDecls() +
                 CheckerOf("sequence s, event c", Counted("@c s")) +
                 TopOf("  ifc i();\n", "i.sd(a), posedge clk"),
             10, 0);
}

void ExpectMethodActual(const std::string& method, const std::string& edge,
                        int n) {
  std::string checker = CheckerOf(
      "sequence s, event c", "  cover property (@c s." + method + ") n++;\n");
  std::string decls = "  sequence e(x); @(" + edge + " clk) x; endsequence\n";
  ExpectLine(checker + TopOf(decls, "e(a), posedge clk"), n, 0);
  ExpectLine(checker + TopOf(decls, "e(z), posedge clk"), 0, 0);
}

TEST(CheckerSequenceFormal, DISABLED_MatchedReadsItsInstanceActual) {
  ExpectMethodActual("matched", "negedge", 9);
}

TEST(CheckerSequenceFormal, DISABLED_TriggeredReadsItsInstanceActual) {
  ExpectMethodActual("triggered", "posedge", 10);
}

void ExpectDefault(const std::string& formal, const std::string& value,
                   const std::string& passing, const std::string& failing) {
  std::string before = "bit hi = 1, lo = 0;\n";
  std::string ports = "event c, " + formal + " = ";
  ExpectLine(before + CheckerOf(ports + passing, Counted("@c " + value)) +
                 TopOf("", "posedge clk"),
             10, 0);
  ExpectLine(before + CheckerOf(ports + failing, Counted("@c " + value)) +
                 TopOf("", ".c(posedge clk)"),
             0, 10);
}

TEST(OmittedCheckerActual, AnUntypedFormalTakesItsDefault) {
  ExpectDefault("x", "x", "hi", "lo");
}

TEST(OmittedCheckerActual, ADataTypedFormalTakesItsDefault) {
  ExpectDefault("bit x", "x", "8'h03", "8'h02");
}

TEST(OmittedCheckerActual, DISABLED_ASequenceFormalTakesItsDefault) {
  ExpectDefault("sequence x", "x", "hi ##0 hi", "hi ##0 lo");
}

TEST(OmittedCheckerActual, DISABLED_APropertyFormalTakesItsDefault) {
  ExpectDefault("property x", "x", "hi |-> hi", "hi |-> lo");
}

TEST(OmittedCheckerActual, AnEventFormalTakesItsDefault) {
  ExpectLine("logic ck0 = 0;\n" +
                 CheckerOf("logic x, event c = posedge ck0", Counted("@c x")) +
                 TopOf("  always @(clk) ck0 = clk;\n", "a"),
             10, 0);
}

}  // namespace

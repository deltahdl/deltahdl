#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Source(const std::string& before, const std::string& body) {
  return before +
         "module t;\n"
         "  logic clk = 0;\n"
         "  initial repeat (20) #5 clk = ~clk;\n"
         "  int n = 0, k = 0;\n"
         "  bit a = 1, b = 1, z = 0;\n" +
         body +
         "  initial #98 $display(\"n=%0d k=%0d\", n, k);\n"
         "endmodule\n";
}

void ExpectOutcome(const std::string& body, int n, int k,
                   const std::string& before = "") {
  std::string src = Source(before, body);
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::string line =
      "n=" + std::to_string(n) + " k=" + std::to_string(k) + "\n";
  EXPECT_NE(out.find(line), std::string::npos) << src << out;
}

std::string Assert(const std::string& property) {
  return "  assert property (" + property + ") n++; else k++;\n";
}

std::string Cover(const std::string& property) {
  return "  cover property (@(posedge clk) " + property + ") n++;\n";
}

std::string Defaulted(const std::string& value) {
  return "  property qd(x = " + value +
         "); @(posedge clk) x; endproperty\n"
         "  property q(x, y = " +
         value + "); @(posedge clk) x && y; endproperty\n";
}

void ExpectDefaultTaken(const std::string& instance) {
  ExpectOutcome(Defaulted("b") + Assert(instance), 10, 0);
  ExpectOutcome(Defaulted("z") + Assert(instance), 0, 10);
}

TEST(OmittedPropertyActual, DISABLED_AnInstanceWithNoListTakesTheDefault) {
  ExpectDefaultTaken("qd");
}

TEST(OmittedPropertyActual, DISABLED_AnEmptyListTakesTheDefault) {
  ExpectDefaultTaken("qd()");
}

TEST(OmittedPropertyActual, DISABLED_AShortPositionalListTakesTheDefault) {
  ExpectDefaultTaken("q(a)");
}

TEST(OmittedPropertyActual, DISABLED_ANamedListTakesTheDefault) {
  ExpectDefaultTaken("q(.x(a))");
}

TEST(OmittedPropertyActual, AFullListTakesNoDefault) {
  ExpectOutcome(Defaulted("z") + Assert("q(a, b)"), 10, 0);
}

TEST(OmittedPropertyActual, DISABLED_ADefaultNamesTheClock) {
  ExpectOutcome("  property q(x, c = clk); @(posedge c) x; endproperty\n" +
                    Assert("q(a)"),
                10, 0);
}

std::string Scope(const std::string& open, const std::string& close) {
  return open +
         "  bit clk, d = 1;\n"
         "  property q(x, y = d); @(posedge clk) x && y; endproperty\n" +
         close;
}

TEST(OmittedPropertyActual, DISABLED_APackagesPropertyTakesTheDefault) {
  ExpectOutcome("  always @(clk) pk::clk = clk;\n" + Assert("pk::q(a)") +
                    Assert("pk::q(z)"),
                10, 10, Scope("package pk;\n", "endpackage\n"));
}

TEST(OmittedPropertyActual, DISABLED_AnInterfacesPropertyTakesTheDefault) {
  ExpectOutcome("  ifc u();\n  always @(clk) u.clk = clk;\n" +
                    Assert("u.q(a)") + Assert("u.q(z)"),
                10, 10, Scope("interface ifc;\n", "endinterface\n"));
}

TEST(OmittedPropertyActual, DISABLED_AnAssumptionTakesTheDefault) {
  ExpectOutcome(Defaulted("b") + "  assume property (q(a)) n++; else k++;\n" +
                    "  assume property (q(z)) n++; else k++;\n",
                10, 10);
}

TEST(OmittedPropertyActual, DISABLED_ACoverTakesTheDefault) {
  ExpectOutcome(Defaulted("b") + "  cover property (q(a)) n++;\n" +
                    "  cover property (q(z)) k++;\n",
                10, 0);
}

TEST(OmittedPropertyActual, ARestrictionTakesTheDefault) {
  SimFixture f;
  RunCapture(Source("", Defaulted("b") + "  restrict property (q(a));\n"), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0U);
}

TEST(OmittedPropertyActual, AnAlwaysProceduresAssertionTakesTheDefault) {
  ExpectOutcome(Defaulted("b") + "  always @(posedge clk) begin\n" +
                    Assert("q(a)") + Assert("q(z)") + "  end\n",
                10, 10);
}

TEST(OmittedPropertyActual, AnInitialProceduresAssertionTakesTheDefault) {
  ExpectOutcome(Defaulted("b") + "  initial begin\n" + Assert("q(a)") +
                    Assert("q(z)") + "  end\n",
                1, 1);
}

void ExpectUntyped(const std::string& body, const std::string& actual,
                   const std::string& decls, int n) {
  for (const char* kind : {"sequence", "property"}) {
    std::string decl =
        std::string("  ") + kind + " s(x); " + body + "; end" + kind + "\n";
    ExpectOutcome(decls + decl + Cover("s(" + actual + ")"), n, 0);
  }
}

TEST(UntypedFormal, ASignedOperatorKeepsItsSigning) {
  std::string decls = "  logic signed [3:0] sa = 4'sb1000;\n";
  ExpectUntyped("x == 8'h0C", "sa >>> 1", decls, 10);
  ExpectUntyped("x == 8'h04", "sa >>> 1", decls, 0);
}

TEST(UntypedFormal, ALogicalActualIsOneTerm) {
  ExpectUntyped("x && z", "a || z", "", 0);
  ExpectUntyped("x && b", "z || a", "", 10);
}

TEST(UntypedFormal, ABitwiseActualIsOneTerm) {
  ExpectUntyped("x & z", "a | z", "", 0);
  ExpectUntyped("x & b", "z | a", "", 10);
}

TEST(UntypedFormal, AConditionalActualIsOneTerm) {
  ExpectUntyped("x + 1 == 1", "a ? b : z", "", 0);
  ExpectUntyped("x + 1 == 1", "a ? z : b", "", 10);
}

std::string Burst() {
  return "  bit r;\n"
         "  initial begin #10 r = 1; #40 r = 0; end\n";
}

std::string Repeated(const std::string& kind, const std::string& repetition) {
  return "  " + kind + " s(hi); !r ##1 r" + repetition + " ##1 !r; end" + kind +
         "\n";
}

void ExpectUnboundedRepetition(const std::string& kind) {
  for (const char* repetition : {"[*1:hi]", "[->1:hi]", "[=1:hi]"}) {
    std::string decls = Burst() + Repeated(kind, repetition);
    ExpectOutcome(decls + Cover("s($)"), 1, 0);
    ExpectOutcome(decls + Cover("s(2)"), 0, 0);
  }
}

TEST(UntypedFormal, ADollarBoundsASequencesRepetition) {
  ExpectUnboundedRepetition("sequence");
}

TEST(UntypedFormal, ADollarBoundsAPropertysRepetition) {
  ExpectUnboundedRepetition("property");
}

TEST(UntypedFormal, DISABLED_ABoundPassesThroughANestedInstance) {
  std::string decls = Burst() + Repeated("sequence", "[*1:hi]") +
                      "  sequence o(m); s(m); endsequence\n";
  ExpectOutcome(decls + Cover("o($)"), 1, 0);
  ExpectOutcome(decls + Cover("o(5)"), 1, 0);
  ExpectOutcome(decls + Cover("o(2)"), 0, 0);
}

TEST(UntypedFormal, AVectorIsSelectedFrom) {
  std::string decls = "  logic [7:0] vec = 8'h04;\n";
  ExpectUntyped("x[2]", "vec", decls, 10);
  ExpectUntyped("x[3]", "vec", decls, 0);
}

TEST(UntypedFormal, AStructuresMemberIsRead) {
  std::string decls = "  struct packed { logic [3:0] hi, lo; } pr = 8'h25;\n";
  ExpectUntyped("x.lo == 5", "pr", decls, 10);
  ExpectUntyped("x.hi == 5", "pr", decls, 0);
}

TEST(UntypedFormal, AnUnpackedStructuresMemberIsRead) {
  std::string decls = "  struct { int hi; int lo; } pr = '{2, 5};\n";
  ExpectUntyped("x.lo == 5", "pr", decls, 10);
  ExpectUntyped("x.hi == 5", "pr", decls, 0);
}

TEST(UntypedFormal, AnArrayElementIsSelectedFrom) {
  std::string decls = "  logic [3:0][7:0] m = 32'h00000400;\n";
  ExpectUntyped("x[2]", "m[1]", decls, 10);
  ExpectUntyped("x[2]", "m[0]", decls, 0);
}

std::string Typed(const std::string& type, const std::string& body) {
  return "  logic [7:0] v = 8'h02, w = 8'h05;\n  property p(" + type +
         " x); @(posedge clk) " + body + "; endproperty\n";
}

TEST(TypedPropertyFormal, DISABLED_ABareBooleanBodyReadsTheCastActual) {
  ExpectOutcome(Typed("bit", "x") + Assert("p(v)"), 0, 10);
  ExpectOutcome(Typed("bit", "x") + Assert("p(w)"), 10, 0);
}

TEST(TypedPropertyFormal, AnImplicationBodyReadsTheCastActual) {
  ExpectOutcome(Typed("bit", "1 |-> x") + Assert("p(v)"), 0, 10);
}

TEST(TypedPropertyFormal,
     DISABLED_AVectorFormalNarrowsItsActualInABareBoolean) {
  ExpectOutcome(Typed("logic [1:0]", "x == 1") + Assert("p(w)"), 10, 0);
  ExpectOutcome(Typed("logic [1:0]", "x == 5") + Assert("p(w)"), 0, 10);
}

TEST(TypedPropertyFormal, AVectorFormalNarrowsItsActualInAnImplication) {
  ExpectOutcome(Typed("logic [1:0]", "1 |-> x == 1") + Assert("p(w)"), 10, 0);
}

TEST(SequenceMethodOperand, TriggeredReadsASequenceFormalInAProperty) {
  std::string decls =
      "  sequence e(x); @(posedge clk) x; endsequence\n"
      "  property p(sequence s); @(posedge clk) s.triggered; endproperty\n";
  ExpectOutcome(decls + Assert("p(e(a))") + Assert("p(e(z))"), 10, 10);
}

TEST(SequenceMethodOperand,
     DISABLED_TriggeredReadsASequenceFormalInAConsequent) {
  std::string decls =
      "  sequence e(x); @(posedge clk) x; endsequence\n"
      "  property p(sequence s); @(posedge clk) a |-> s.triggered; "
      "endproperty\n";
  ExpectOutcome(decls + Assert("p(e(a))") + Assert("p(e(z))"), 10, 10);
}

TEST(SequenceMethodOperand, MatchedReadsASequenceFormalInAProperty) {
  std::string decls =
      "  sequence e(x); @(negedge clk) x; endsequence\n"
      "  property p(sequence s); @(posedge clk) s.matched; endproperty\n";
  ExpectOutcome(decls + Assert("p(e(a))") + Assert("p(e(z))"), 9, 11);
}

TEST(PropertyFormal, DISABLED_ABareSequenceInstanceStandsForIt) {
  std::string decls =
      "  sequence sd(x); x; endsequence\n"
      "  property ps(property p); p; endproperty\n";
  ExpectOutcome(decls + Assert("@(posedge clk) ps(sd(a))") +
                    Assert("@(posedge clk) ps(sd(z))"),
                10, 10);
}

TEST(PropertyFormal, ALooselyBoundActualStandsWholeUnderNot) {
  std::string decls = "  property ps(property p); not p; endproperty\n";
  ExpectOutcome(decls + Assert("@(posedge clk) ps(a or b)"), 0, 10);
  ExpectOutcome(decls + Assert("@(posedge clk) ps(z or z)"), 10, 0);
}

std::string OrBody() { return "  sequence s; a or z; endsequence\n"; }

TEST(InstanceBody, AnOrStandsWholeUnderAnd) {
  ExpectOutcome(OrBody() + Cover("s and z"), 0, 0);
  ExpectOutcome(OrBody() + Cover("s and b"), 10, 0);
}

TEST(InstanceBody, AnOrStandsWholeUnderIntersect) {
  ExpectOutcome(OrBody() + Cover("s intersect z"), 0, 0);
  ExpectOutcome(OrBody() + Cover("s intersect b"), 10, 0);
}

TEST(InstanceBody, AnOrStandsWholeBeforeADelay) {
  ExpectOutcome(OrBody() + Cover("s ##1 z"), 0, 0);
  ExpectOutcome(OrBody() + Cover("s ##1 b"), 9, 0);
}

TEST(InstanceBody, AnOrStandsWholeUnderWithin) {
  ExpectOutcome(OrBody() + Cover("s within z"), 0, 0);
  ExpectOutcome(OrBody() + Cover("s within b"), 10, 0);
}

TEST(InstanceBody, AChainIsRepeatedWhole) {
  std::string decls = "  bit c = 1;\n  initial #10 c = 0;\n";
  ExpectOutcome(decls + "  sequence s; c ##1 b; endsequence\n" + Cover("s[*2]"),
                0, 0);
  ExpectOutcome(decls + "  sequence s; a ##1 b; endsequence\n" + Cover("s[*2]"),
                7, 0);
}

void ExpectProperty(const std::string& body, const std::string& use, int n,
                    int k) {
  ExpectOutcome("  property p; " + body + "; endproperty\n" +
                    Assert("@(posedge clk) " + use),
                n, k);
}

TEST(InstanceBody, AnOrPropertyStandsWholeUnderNot) {
  ExpectProperty("a or b", "not p", 0, 10);
  ExpectProperty("z or z", "not p", 10, 0);
}

TEST(InstanceBody, AnImpliesPropertyStandsWholeUnderNot) {
  ExpectProperty("z implies b", "not p", 0, 10);
  ExpectProperty("a implies z", "not p", 10, 0);
}

TEST(InstanceBody, AnImplicationStandsWholeUnderAnd) {
  ExpectProperty("z |-> b", "p and z", 0, 10);
}

TEST(InstanceBody, AnOrPropertyStandsWholeUnderAnd) {
  ExpectProperty("a or b", "p and z", 0, 10);
  ExpectProperty("a or z", "p and b", 10, 0);
}

TEST(InstanceBody, AnImplicationStandsWholeUnderUntil) {
  std::string decls =
      "  bit c = 1;\n  initial #10 c = 0;\n"
      "  property p; c |-> c; endproperty\n";
  ExpectOutcome(decls + Assert("@(posedge clk) p until z"), 0, 0);
}

std::string EndPoints() {
  return "  sequence s(x); @(posedge clk) x; endsequence\n"
         "  sequence s0; @(posedge clk) a; endsequence\n";
}

TEST(SequenceKeptAsAnItem,
     DISABLED_AnEventControlTakesAnInstanceWithArguments) {
  ExpectOutcome(EndPoints() + "  always @(s(a)) n++;\n  always @(s(z)) k++;\n",
                10, 0);
}

TEST(SequenceKeptAsAnItem, AnEventControlTakesAnInstanceWithoutArguments) {
  ExpectOutcome(EndPoints() + "  always @(s0) n++;\n", 10, 0);
}

std::string WaitLoop(const std::string& sequence) {
  return "  always begin wait (" + sequence +
         ".triggered); n++; @(negedge clk); end\n";
}

TEST(SequenceKeptAsAnItem, DISABLED_AWaitTakesAnInstanceWithArguments) {
  ExpectOutcome(EndPoints() + WaitLoop("s(a)"), 10, 0);
}

TEST(SequenceKeptAsAnItem, AWaitOnAnInstanceThatNeverEndsStaysBlocked) {
  ExpectOutcome(EndPoints() + WaitLoop("s(z)"), 0, 0);
}

TEST(SequenceKeptAsAnItem, AWaitTakesAnInstanceWithoutArguments) {
  ExpectOutcome(EndPoints() + WaitLoop("s0"), 10, 0);
}

TEST(SequenceKeptAsAnItem, AnAssertionsClockTakesAnInstanceWithoutArguments) {
  ExpectOutcome(EndPoints() + Assert("@(s0) b") + Assert("@(s0) z"), 10, 10);
}

TEST(SequenceKeptAsAnItem,
     DISABLED_AnAssertionsClockTakesAnInstanceWithArguments) {
  ExpectOutcome(EndPoints() + Assert("@(s(a)) b") + Assert("@(s(a)) z"), 10,
                10);
}

}  // namespace

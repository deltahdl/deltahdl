#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Signals() {
  return "  bit a = 1, z = 0;\n  int tick = 0, n = 0;\n"
         "  always @(negedge clk) tick = tick + 1;\n";
}

std::string Report() { return "  initial #98 $display(\"n=%0d\", n);\n"; }

std::string Design(const std::string& before, const std::string& inside) {
  return before +
         "module t;\n  logic clk = 0;\n"
         "  initial repeat (20) #5 clk = ~clk;\n" +
         Signals() + inside + Report() + "endmodule\n";
}

void ExpectN(const std::string& src, int n) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_NE(out.find("n=" + std::to_string(n) + "\n"), std::string::npos)
      << src << out;
  EXPECT_FALSE(f.diag.HasErrors()) << src;
}

struct Thread {
  int value = 1;
  int delay = 0;
  std::string type = "int";
  std::string start = "4";
  std::string instance = "s(v)";
};

std::string Reader(const Thread& thread) {
  return "  sequence rd;\n    " + thread.type + " v; int m;\n    (1, m = tick" +
         (thread.start.empty() ? "" : ", v = " + thread.start) + ") ##0 " +
         thread.instance + " ##1 (v == " + std::to_string(thread.value) +
         " && tick == m + " + std::to_string(thread.delay + 1) +
         ");\n  endsequence\n"
         "  cover property (@(posedge clk) rd) n++;\n";
}

std::string Sequence(const std::string& formals, const std::string& body) {
  return "  sequence s(" + formals + ");\n    " + body + ";\n  endsequence\n";
}

int Ends(const Thread& thread) { return 9 - thread.delay; }

void ExpectThread(const std::string& formals, const std::string& body,
                  const Thread& thread) {
  ExpectN(Design("", Sequence(formals, body) + Reader(thread)), Ends(thread));
}

void ExpectNoThread(const std::string& formals, const std::string& body,
                    const Thread& thread) {
  ExpectN(Design("", Sequence(formals, body) + Reader(thread)), 0);
}

void ExpectOutput(const std::string& body, int value, int delay) {
  Thread thread;
  thread.value = value;
  thread.delay = delay;
  ExpectThread("local output int o", body, thread);
}

void ExpectInout(const std::string& body, int value, int delay) {
  Thread thread;
  thread.value = value;
  thread.delay = delay;
  ExpectThread("local inout int o", body, thread);
}

TEST(InputLocalFormal, ItIsInitializedFromItsActual) {
  ExpectThread("local input int i", "(a && i == 4)", {4});
  ExpectNoThread("local input int i", "(a && i == 5)", {4});
}

TEST(InputLocalFormal, AWriteToItLeavesItsActual) {
  ExpectThread("local input int i", "(a, i += 1) ##0 (i == 5)", {4});
}

TEST(InputLocalFormal, DISABLED_ABodyLocalReadsItsValue) {
  ExpectThread("local input int i", "int w = i; (a && w == 4)", {4});
  ExpectThread("local int i", "int w = i; (a && w == 4)", {4});
}

TEST(InputLocalFormal, DISABLED_ALaterBodyLocalReadsAnEarlierOneReadingIt) {
  ExpectThread("local input int i", "int w = i, x = w + 1; (a && x == 5)", {4});
  ExpectThread("local input int i", "int h = 5, w = i + h; (a && w == 9)", {4});
}

TEST(InoutLocalFormal, DISABLED_ABodyLocalReadsItsValue) {
  ExpectThread("local inout int i", "int w = i; (a && w == 4)", {4});
}

TEST(InoutLocalFormal, ItIsAssignedBack) { ExpectInout("(a, o += 1)", 5, 0); }

TEST(OutputLocalFormal, ItIsAssignedBack) {
  ExpectOutput("(a, o = 1)", 1, 0);
  ExpectOutput("a ##2 (a, o = 3)", 3, 2);
}

TEST(OutputLocalFormal, AnUnassignedActualIsAccepted) {
  ExpectThread("local output int o", "(a, o = 1)", {1, 0, "int", ""});
}

TEST(LocalFormalAssignedBack, ANarrowerSignedFormalIsExtended) {
  ExpectThread("local output byte o", "(a, o = 265)", {9});
  ExpectThread("local output byte o", "(a, o = -1)", {-1});
}

TEST(LocalFormalAssignedBack, AWiderFormalIsTruncated) {
  ExpectThread("local output int o", "(a, o = 300)", {44, 0, "byte"});
}

TEST(LocalFormalAssignedBack, AnInoutFormalWrapsAtItsOwnWidth) {
  ExpectThread("local inout byte o", "(a, o += 1)", {-128, 0, "int", "127"});
}

TEST(LocalFormalAssignedBack, APackedSignedFormalIsExtended) {
  ExpectThread("local output logic signed [7:0] o", "(a, o = -1)", {-1});
  ExpectThread("local output bit signed [7:0] o", "(a, o = -1)", {-1});
}

TEST(LocalFormalAssignedBack, ANamedUnsignedTypeIsZeroExtended) {
  ExpectN(Design("typedef byte unsigned ub;\n",
                 Sequence("local output ub o", "(a, o = 255)") + Reader({255})),
          9);
}

TEST(LocalFormalAssignedBack, DISABLED_AByteUnsignedFormalIsZeroExtended) {
  ExpectThread("local output byte unsigned o", "(a, o = 255)", {255});
}

TEST(LocalFormalAssignedBack, DISABLED_AnIntUnsignedFormal) {
  ExpectThread("local output int unsigned o", "(a, o = 5)", {5});
  ExpectThread("local inout int unsigned o", "(a, o += 1)", {5});
}

TEST(ForkedLocalFormal, EachRepetitionCountAssignsItsOwnCopy) {
  ExpectInout("(a, o += 1)[*1:2]", 5, 0);
  ExpectInout("(a, o += 1)[*1:2]", 6, 1);
}

TEST(ForkedLocalFormal, EachDelayAssignsItsOwnCopy) {
  ExpectOutput("a ##[1:2] (1, o = 5)", 5, 1);
  ExpectOutput("a ##[1:2] (1, o = 5)", 5, 2);
}

TEST(ForkedLocalFormal, DISABLED_EachOrBranchAssignsItsValueAtItsEnd) {
  ExpectOutput("(a, o = 1) or (a ##1 (1, o = 2))", 1, 0);
  ExpectOutput("(a, o = 1) or (a ##1 (1, o = 2))", 2, 1);
}

TEST(ForkedLocalFormal, DISABLED_AMatchingOrBranchAloneAssigns) {
  ExpectOutput("(a, o = 1) or (z, o = 2)", 1, 0);
  ExpectOutput("(z, o = 1) or (a, o = 2)", 2, 0);
}

TEST(ForkedLocalFormal, DISABLED_OrBranchesEndingTogetherKeepTheirOwnValues) {
  ExpectOutput("(a, o = 1) or (a, o = 2)", 1, 0);
  ExpectOutput("(a, o = 1) or (a, o = 2)", 2, 0);
}

TEST(ForkedLocalFormal, DISABLED_AnInoutUnderOr) {
  ExpectInout("(a, o += 1) or (a ##1 (1, o += 2))", 5, 0);
  ExpectInout("(a, o += 1) or (a ##1 (1, o += 2))", 6, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnOutputAssignedInOneAndOperand) {
  ExpectOutput("(a, o = 1) and (a ##1 a)", 1, 1);
  ExpectOutput("(a ##1 a) and (a, o = 1)", 1, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnInoutAssignedInOneAndOperand) {
  ExpectInout("(a, o += 1) and (a ##1 a)", 5, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnOutputAssignedUnderIntersect) {
  ExpectOutput("(a, o = 1) intersect a", 1, 0);
  ExpectOutput("(a ##1 (1, o = 1)) intersect (a ##1 a)", 1, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnOutputAssignedUnderWithin) {
  ExpectOutput("(a, o = 1) within (a ##1 a)", 1, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnOutputUnderFirstMatchOfAnOr) {
  ExpectOutput("first_match((a, o = 1) or (a ##1 (1, o = 2)))", 1, 0);
}

TEST(ForkedLocalFormal, AFirstMatchLeavesALaterMatchUnassigned) {
  ExpectNoThread("local output int o",
                 "first_match((a, o = 1) or (a ##1 (1, o = 2)))", {2, 1});
}

TEST(ForkedLocalFormal, AnOutputUnderFirstMatchOfOneOperand) {
  ExpectOutput("first_match((a, o = 1))", 1, 0);
}

TEST(ForkedLocalFormal, AnOutputUnderThroughout) {
  ExpectOutput("a throughout (a ##1 (1, o = 1))", 1, 1);
}

TEST(ForkedLocalFormal, DISABLED_AnOrNestedInALongerBody) {
  ExpectOutput("a ##0 ((a, o = 1) or (a, o = 2))", 2, 0);
}

TEST(ForkedLocalFormal, DISABLED_AnAndNestedInALongerBody) {
  ExpectOutput("((a, o = 1) and (a ##1 a)) ##1 a", 1, 2);
}

TEST(ForkedLocalFormal, DISABLED_AnIntersectNestedInALongerBody) {
  ExpectOutput("a ##0 ((a, o = 1) intersect a)", 1, 0);
}

TEST(ForkedLocalFormal, DISABLED_AWithinNestedInALongerBody) {
  ExpectOutput("a ##0 ((a, o = 1) within (a ##1 a))", 1, 1);
}

TEST(LocalFormalAssignedBack, AnOutwardFormalPassedOnToAnInnerInstance) {
  ExpectN(
      Design("",
             "  sequence in(local output int o); (a, o = 1); endsequence\n" +
                 Sequence("local output int o", "in(o)") + Reader({1})),
      9);
}

TEST(LocalFormalAssignedBack, AnInoutPassedOnTwice) {
  ExpectN(
      Design("",
             "  sequence in(local inout int o); (a, o += 1); endsequence\n" +
                 Sequence("local inout int o", "in(o) ##1 in(o)") +
                 Reader({6, 1})),
      8);
}

TEST(LocalFormalAssignedBack, TwoOutwardFormalsOfDifferentTypes) {
  ExpectN(Design("", Sequence("local output byte o, local output int p",
                              "(a, o = 265, p = 7)") +
                         "  sequence rd; int v, w;\n"
                         "    s(v, w) ##1 (v == 9 && w == 7); endsequence\n"
                         "  cover property (@(posedge clk) rd) n++;\n"),
          9);
}

TEST(LocalFormalAssignedBack, APropertysLocalIsTheActual) {
  ExpectN(Design("", Sequence("local output int o", "(a, o = 1)") +
                         "  property pr; int v;\n"
                         "    @(posedge clk) s(v) ##1 (v == 1);\n"
                         "  endproperty\n  cover property (pr) n++;\n"),
          9);
}

std::string OutputSequence() {
  return Sequence("local output int o", "(a, o = 1)");
}

std::string InoutSequence() {
  return Sequence("local inout int o", "(a, o += 1)");
}

Thread InoutThread() { return {5}; }

std::string Element(const std::string& keyword, const std::string& body) {
  return keyword + " sub(input logic clk);\n" + Signals() + body + Report() +
         "end" + keyword + "\n";
}

void ExpectElementAssignsBack(const std::string& keyword) {
  std::string top =
      "module t;\n  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n  sub u(clk);\nendmodule\n";
  ExpectN(Element(keyword, OutputSequence() + Reader({1})) + top, 9);
  ExpectN(Element(keyword, InoutSequence() + Reader(InoutThread())) + top, 9);
}

TEST(LocalFormalPlace, AModulesSequence) { ExpectElementAssignsBack("module"); }

TEST(LocalFormalPlace, AnInterfacesSequence) {
  ExpectElementAssignsBack("interface");
}

void ExpectProgramAssignsBack(const std::string& body) {
  ExpectN(
      "program sub(input logic clk, input var int tick);\n"
      "  bit a = 1, z = 0;\n  int n = 0;\n" +
          body + Report() +
          "endprogram\nmodule t;\n  logic clk = 0;\n  int tick = 0;\n"
          "  initial repeat (20) #5 clk = ~clk;\n"
          "  always @(negedge clk) tick = tick + 1;\n"
          "  sub u(clk, tick);\nendmodule\n",
      9);
}

TEST(LocalFormalPlace, AProgramsSequence) {
  ExpectProgramAssignsBack(OutputSequence() + Reader({1}));
  ExpectProgramAssignsBack(InoutSequence() + Reader(InoutThread()));
}

void ExpectCheckerAssignsBack(const std::string& body) {
  ExpectN("checker ck(logic clk, logic a, int tick);\n  int n = 0;\n" + body +
              "endchecker\nmodule t;\n  logic clk = 0;\n"
              "  initial repeat (20) #5 clk = ~clk;\n" +
              Signals() +
              "  ck u(clk, a, tick);\n"
              "  initial #98 $display(\"n=%0d\", u.n);\nendmodule\n",
          9);
}

TEST(LocalFormalPlace, ACheckersSequence) {
  ExpectCheckerAssignsBack(OutputSequence() + Reader({1}));
  ExpectCheckerAssignsBack(InoutSequence() + Reader(InoutThread()));
}

Thread Prefixed(const std::string& prefix, const std::string& start) {
  return {1, 0, "int", start, prefix + "s(v)"};
}

std::string ClockingBlock() {
  return "  clocking cb @(posedge clk);\n" + OutputSequence() +
         "  endclocking\n";
}

void ExpectPlace(const std::string& before, const std::string& inside,
                 const std::string& prefix, const std::string& start) {
  ExpectN(Design(before, inside + Reader(Prefixed(prefix, start))), 9);
}

TEST(LocalFormalPlace, AClockingBlocksSequence) {
  ExpectPlace("", ClockingBlock(), "cb.", "4");
}

TEST(LocalFormalPlace, DISABLED_AClockingBlocksSequenceWithAnUnassignedActual) {
  ExpectPlace("", ClockingBlock(), "cb.", "");
}

std::string Package() {
  return "package pk;\n  bit a = 1;\n" + OutputSequence() + "endpackage\n";
}

TEST(LocalFormalPlace, APackagesSequence) {
  ExpectPlace(Package(), "", "pk::", "4");
}

TEST(LocalFormalPlace, DISABLED_APackagesSequenceWithAnUnassignedActual) {
  ExpectPlace(Package(), "", "pk::", "");
}

TEST(LocalFormalPlace, AnImportedSequence) {
  ExpectPlace(Package(), "  import pk::s;\n", "", "4");
}

TEST(LocalFormalPlace, DISABLED_AnImportedSequenceWithAnUnassignedActual) {
  ExpectPlace(Package(), "  import pk::s;\n", "", "");
}

TEST(LocalFormalPlace, DISABLED_ACompilationUnitsSequence) {
  ExpectPlace("bit a = 1;\n" + OutputSequence(), "", "", "4");
}

TEST(LocalFormalPlace,
     DISABLED_ACompilationUnitsSequenceWithAnUnassignedActual) {
  ExpectPlace("bit a = 1;\n" + OutputSequence(), "", "", "");
}

TEST(LocalFormalPlace, AGenerateBlocksSequence) {
  ExpectN(Design("", "  if (1) begin : g\n" + OutputSequence() + Reader({1}) +
                         "  end\n"),
          9);
}

void ExpectProperty(const std::string& formals, const std::string& body,
                    const std::string& actuals) {
  ExpectN(Design("", "  property q(" + formals + ");\n    " + body +
                         ";\n  endproperty\n  cover property (q" + actuals +
                         ") n++;\n"),
          10);
}

TEST(PropertyLocalFormal, DISABLED_ABodyLocalReadsAnInputFormal) {
  ExpectProperty("local input int f",
                 "int g = f + 1; @(posedge clk) (g == tick + 1)", "(tick)");
}

TEST(PropertyLocalFormal, DISABLED_ABodyLocalReadsAnInferredInputFormal) {
  ExpectProperty("local int f", "int g = f; @(posedge clk) (g == tick)",
                 "(tick)");
}

TEST(PropertyLocalFormal, DISABLED_ABodyLocalReadsADefaultActual) {
  ExpectProperty("local input int f = tick + 3",
                 "int g = f; @(posedge clk) (g == tick + 3)", "()");
}

TEST(PropertyLocalFormal, DISABLED_ABodyLocalReadsTwoFormals) {
  ExpectProperty("local input int e, local input int f",
                 "int g = e + f; @(posedge clk) (g == 2 * tick + 3)",
                 "(tick, tick + 3)");
}

TEST(PropertyLocalFormal,
     DISABLED_ABodyLocalReadsAFormalAndAnEarlierBodyLocal) {
  ExpectProperty("local input int f",
                 "int h = 5, g = f + h; @(posedge clk) (g == tick + 5)",
                 "(tick)");
}

TEST(PropertyLocalFormal, DISABLED_AChainOfBodyLocalsStartsAtAFormal) {
  ExpectProperty("local input int f",
                 "int g = f, h = g; @(posedge clk) (h == tick)", "(tick)");
}

TEST(PropertyLocalFormal, TheFormalItselfHoldsItsActual) {
  ExpectProperty("local input int f", "@(posedge clk) (f == tick)", "(tick)");
}

}  // namespace

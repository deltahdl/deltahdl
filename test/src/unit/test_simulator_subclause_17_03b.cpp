#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kFailingOutputs =
    "checker cf(logic clk, output bit failure);\n"
    "  a1: assert property (@(posedge clk) 0) failure = 1'b0;\n"
    "    else failure = 1'b1;\n"
    "endchecker\n"
    "checker cf2(logic clk, output bit [1:0] failure);\n"
    "  a1: assert property (@(posedge clk) 0) failure = 2'b00;\n"
    "    else failure = 2'b10;\n"
    "endchecker\n";

std::string AfterOneEdge(const std::string& items, const std::string& shown) {
  SimFixture f;
  return RunCapture(std::string(kFailingOutputs) +
                        "module sub;\n  bit x;\nendmodule\n"
                        "module top;\n"
                        "  typedef bit [1:0] pair_t;\n"
                        "  logic clk = 0;\n" +
                        items + "  initial begin #5 clk = 1; #1 $display(" +
                        shown + "); end\nendmodule\n",
                    f);
}

TEST(CheckerOutputActualRun, NetsSelectsAndPathsAreDriven) {
  EXPECT_EQ(AfterOneEdge("  wire w;\n"
                         "  wire [3:0] wv;\n"
                         "  bit [3:0] vec, pv;\n"
                         "  int i = 2;\n"
                         "  sub s();\n"
                         "  cf u1(clk, w);\n"
                         "  cf u2(clk, wv[1]);\n"
                         "  cf2 u3(clk, wv[3:2]);\n"
                         "  cf u4(clk, vec[i]);\n"
                         "  cf2 u5(clk, pv[0+:2]);\n"
                         "  cf u6(clk, s.x);\n",
                         "\"%b %b %b %b %b\", w, wv, vec, pv, s.x"),
            "1 101z 0100 0010 1\n");
}

TEST(CheckerOutputActualRun, DISABLED_StreamsAndAssignmentPatternsAreDriven) {
  EXPECT_EQ(AfterOneEdge("  bit a, b, c0, c1, d0, d1;\n"
                         "  cf2 u7(clk, {>>{a, b}});\n"
                         "  cf2 u8(clk, '{c0, c1});\n"
                         "  cf2 u9(clk, pair_t'{d0, d1});\n",
                         "\"%b%b %b%b %b%b\", a, b, c0, c1, d0, d1"),
            "10 10 10\n");
}

constexpr const char* kCountingPorts =
    "checker pcnt(logic clk, logic a);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
    "endchecker\n"
    "checker pd(logic clk, logic a, k = 1'b1);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@(posedge clk) a && k) pass++; else fail++;\n"
    "endchecker\n";

constexpr const char* kStimulus =
    "  logic clk = 0, a = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n";

std::pair<uint64_t, uint64_t> Counts(const std::string& src,
                                     const std::string& scope) {
  SimFixture f;
  auto* pass = RunAndFindVar(src, f, scope + ".pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable(scope + ".fail")->value.ToUint64()};
}

std::string Top(const std::string& items) {
  return std::string(kCountingPorts) + "module top;\n" + kStimulus + items +
         "endmodule\n";
}

const std::pair<uint64_t, uint64_t> kBoundToA{3, 2};
const std::pair<uint64_t, uint64_t> kAlwaysHigh{5, 0};
const std::pair<uint64_t, uint64_t> kAlwaysLow{0, 5};

TEST(CheckerImplicitConnectionRun, AnImplicitNameBindsValueInputs) {
  EXPECT_EQ(Counts(Top("  pcnt u(.clk, .a);\n"), "u"), kBoundToA);
}

TEST(CheckerImplicitConnectionRun, AWildcardBindsValueInputs) {
  EXPECT_EQ(Counts(Top("  pcnt u(.*);\n"), "u"), kBoundToA);
}

std::string OutputTop(const std::string& instance) {
  return "checker co(logic clk, output bit failure);\n"
         "  a1: assert property (@(posedge clk) 0) failure = 1'b0;\n"
         "    else failure = 1'b1;\n"
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  bit failure;\n" +
         instance +
         "  initial begin #5 clk = 1; #1 $display(\"%b\", failure); end\n"
         "endmodule\n";
}

TEST(CheckerImplicitConnectionRun, AnImplicitNameOrWildcardBindsAnOutput) {
  SimFixture f1;
  EXPECT_EQ(RunCapture(OutputTop("  co u(.clk, .failure);\n"), f1), "1\n");
  SimFixture f2;
  EXPECT_EQ(RunCapture(OutputTop("  co u(.*);\n"), f2), "1\n");
}

TEST(CheckerImplicitConnectionRun, AnExplicitNameOverridesTheWildcard) {
  std::string src =
      Top("  logic b = 1;\n"
          "  pcnt u1(.*, .a(b));\n"
          "  pcnt u2(.a(b), .*);\n");
  EXPECT_EQ(Counts(src, "u1"), kAlwaysHigh);
  EXPECT_EQ(Counts(src, "u2"), kAlwaysHigh);
}

TEST(CheckerImplicitConnectionRun, AWildcardKeepsADefaultWithNoNameInScope) {
  EXPECT_EQ(Counts(Top("  pd u(.*);\n"), "u"), kBoundToA);
}

TEST(CheckerImplicitConnectionRun,
     DISABLED_AnEmptyNamedConnectionKeepsTheDefault) {
  std::string src =
      Top("  logic k = 0;\n"
          "  pd u1(.*, .k());\n"
          "  pd u2(.*);\n");
  EXPECT_EQ(Counts(src, "u1"), kBoundToA);
  EXPECT_EQ(Counts(src, "u2"), kAlwaysLow);
}

TEST(CheckerImplicitConnectionRun, AnEventFormalTakesASameNamedEvent) {
  for (const char* instance : {"  pe u(.clk, .a);\n", "  pe u(.*);\n"}) {
    SCOPED_TRACE(instance);
    EXPECT_EQ(Counts(std::string("checker pe(event clk, logic a);\n"
                                 "  int pass = 0, fail = 0;\n"
                                 "  a1: assert property (@clk a) pass++; else "
                                 "fail++;\n"
                                 "endchecker\n"
                                 "module top;\n"
                                 "  event clk;\n"
                                 "  logic a = 1;\n"
                                 "  initial begin\n"
                                 "    #5;\n"
                                 "    repeat (5) begin ->clk; #10; end\n"
                                 "  end\n"
                                 "  initial begin #12 a = 0; #20 a = 1; #20 "
                                 "$finish; end\n") +
                         instance + "endmodule\n",
                     "u"),
              kBoundToA);
  }
}

constexpr const char* kSequencePropertyChecker =
    "checker ps(logic clk, sequence s, property p);\n"
    "  int sp = 0, sf = 0, pp = 0, pf = 0;\n"
    "  a1: assert property (@(posedge clk) s) sp++; else sf++;\n"
    "  a2: assert property (@(posedge clk) p) pp++; else pf++;\n"
    "endchecker\n";

std::pair<uint64_t, uint64_t> SequenceCounts(const std::string& items,
                                             const char* instance) {
  SimFixture f;
  auto* sp =
      RunAndFindVar(std::string(kSequencePropertyChecker) + "module top;\n" +
                        kStimulus + items + instance + "endmodule\n",
                    f, "u.sp");
  if (sp == nullptr) return {~0ull, ~0ull};
  auto value = [&f](const char* name) {
    return f.ctx.FindVariable(std::string("u.") + name)->value.ToUint64();
  };
  EXPECT_EQ(value("pp"), value("sp"));
  EXPECT_EQ(value("pf"), value("sf"));
  return {value("sp"), value("sf")};
}

TEST(CheckerImplicitConnectionRun, SequenceAndPropertyFormalsTakeSignals) {
  for (const char* instance : {"  ps u(.clk, .s, .p);\n", "  ps u(.*);\n"}) {
    SCOPED_TRACE(instance);
    EXPECT_EQ(SequenceCounts("  logic s, p;\n  assign s = a;\n  assign p = "
                             "a;\n",
                             instance),
              kBoundToA);
  }
}

TEST(CheckerImplicitConnectionRun,
     DISABLED_SequenceAndPropertyFormalsTakeDecls) {
  for (const char* instance : {"  ps u(.clk, .s, .p);\n", "  ps u(.*);\n"}) {
    SCOPED_TRACE(instance);
    EXPECT_EQ(SequenceCounts("  sequence s;\n    a;\n  endsequence\n"
                             "  property p;\n    a;\n  endproperty\n",
                             instance),
              kBoundToA);
  }
}

TEST(CheckerImplicitConnectionRun, AWildcardDoesNotImportAPackageName) {
  std::string pkg = "package pq;\n  logic k = 0;\nendpackage\n";
  std::string src = pkg + kCountingPorts + "module top;\n  import pq::*;\n" +
                    kStimulus +
                    "  pd u1(.*);\n"
                    "endmodule\n";
  EXPECT_EQ(Counts(src, "u1"), kBoundToA);
  std::string named = pkg + kCountingPorts + "module top;\n  import pq::*;\n" +
                      kStimulus +
                      "  pd u2(.k, .*);\n"
                      "endmodule\n";
  EXPECT_EQ(Counts(named, "u2"), kAlwaysLow);
}

std::string InContainer(const std::string& keyword, const std::string& name,
                        const std::string& instances) {
  std::string header =
      keyword == "checker"
          ? "checker " + name + "(logic clk, logic a);\n"
          : keyword + " " + name + "(input logic clk, input logic a);\n";
  return header + instances + "end" + keyword + "\n";
}

TEST(CheckerImplicitConnectionRun, EachPlaceBindsByImplicitNameAndWildcard) {
  const char* const kInstances = "  pcnt u1(.clk, .a);\n  pcnt u2(.*);\n";
  for (const char* keyword : {"interface", "program", "checker"}) {
    SCOPED_TRACE(keyword);
    std::string src =
        std::string(kCountingPorts) + InContainer(keyword, "box", kInstances) +
        "module top;\n" + kStimulus + "  box b(clk, a);\nendmodule\n";
    EXPECT_EQ(Counts(src, "b.u1"), kBoundToA);
    EXPECT_EQ(Counts(src, "b.u2"), kBoundToA);
  }
  std::string gen =
      Top("  if (1) begin : g\n" + std::string(kInstances) + "  end\n");
  EXPECT_EQ(Counts(gen, "g.u1"), kBoundToA);
  EXPECT_EQ(Counts(gen, "g.u2"), kBoundToA);
}

TEST(CheckerImplicitConnectionRun, AProceduralInstanceBindsTheSameWay) {
  std::string src =
      Top("  always @(posedge clk) begin\n"
          "    pcnt u1(.clk, .a);\n"
          "    pcnt u2(.*);\n"
          "  end\n");
  EXPECT_EQ(Counts(src, "u1"), kBoundToA);
  EXPECT_EQ(Counts(src, "u2"), kBoundToA);
}

TEST(CheckerImplicitConnectionRun, APackageCheckerBindsTheSameWay) {
  std::string src = std::string("package p;\n") + kCountingPorts +
                    "endpackage\n"
                    "module top;\n" +
                    kStimulus +
                    "  p::pcnt u1(.clk, .a);\n"
                    "  p::pcnt u2(.*);\n"
                    "endmodule\n";
  EXPECT_EQ(Counts(src, "u1"), kBoundToA);
  EXPECT_EQ(Counts(src, "u2"), kBoundToA);
}

constexpr const char* kEventInner =
    "checker inner(logic sig, event clock);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@clock sig) pass++; else fail++;\n"
    "endchecker\n";

std::string EventOuter(const std::string& formal, const std::string& instance,
                       const std::string& actual) {
  return std::string(kEventInner) + "checker outer(logic s, " + formal +
         ");\n" + instance +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0, a = 1;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin #16 a = 0; #8 a = 1; #28 $finish; end\n"
         "  outer o(a, " +
         actual + ");\nendmodule\n";
}

const std::pair<uint64_t, uint64_t> kOnFallingEdges{4, 1};

TEST(CheckerEventActualRun, AnEdgeOfALogicFormalClocksANestedChecker) {
  EXPECT_EQ(Counts(EventOuter("logic ck", "  inner k(s, negedge ck);\n", "clk"),
                   "o.k"),
            kOnFallingEdges);
}

TEST(CheckerEventActualRun, DISABLED_AnEventFormalClocksANestedChecker) {
  for (const char* instance :
       {"  inner k(s, c);\n", "  inner k(.sig(s), .clock(c));\n"}) {
    SCOPED_TRACE(instance);
    EXPECT_EQ(Counts(EventOuter("event c", instance, "negedge clk"), "o.k"),
              kOnFallingEdges);
  }
}

}  // namespace

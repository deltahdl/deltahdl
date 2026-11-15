#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kContextChecker =
    "checker chk(logic sig, event clock = $inferred_clock,\n"
    "            logic reset = $inferred_disable);\n"
    "  int pass = 0, fail = 0;\n"
    "  a1: assert property (@clock disable iff (reset) sig) pass++;\n"
    "    else fail++;\n"
    "endchecker\n";

std::pair<uint64_t, uint64_t> ContextCheckerCounts(const std::string& module) {
  SimFixture f;
  auto* pass =
      RunAndFindVar(std::string(kContextChecker) + module, f, "k.pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable("k.fail")->value.ToUint64()};
}

TEST(CheckerContextInference, AStaticInstanceTakesTheScopesDefaults) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1, rst = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default clocking @(posedge clk); endclocking\n"
                "  default disable iff rst;\n"
                "  chk k(a);\n"
                "  initial begin #12 begin a = 0; rst = 0; end #20 a = 1;\n"
                "    #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(2ull, 2ull));
}

TEST(CheckerContextInference, AProceduralInstanceTakesTheProceduresClock) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1, rst = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default disable iff rst;\n"
                "  always @(posedge clk) begin\n"
                "    chk k(a);\n"
                "  end\n"
                "  initial begin #12 begin a = 0; rst = 0; end #20 a = 1;\n"
                "    #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(2ull, 2ull));
}

TEST(CheckerContextInference, NoDefaultDisableIffInfersFalse) {
  EXPECT_EQ(ContextCheckerCounts(
                "module top;\n"
                "  logic clk = 0, a = 1;\n"
                "  always #5 clk = ~clk;\n"
                "  default clocking @(posedge clk); endclocking\n"
                "  chk k(a);\n"
                "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
                "endmodule\n"),
            std::make_pair(3ull, 2ull));
}

constexpr const char* kTwoEdgeStimulus =
    "  logic clk = 0, a = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin #16 a = 0; #8 a = 1; #28 $finish; end\n";

std::pair<uint64_t, uint64_t> CountsAt(const std::string& src,
                                       const std::string& scope) {
  SimFixture f;
  auto* pass = RunAndFindVar(src, f, scope + ".pass");
  if (pass == nullptr) return {~0ull, ~0ull};
  return {pass->value.ToUint64(),
          f.ctx.FindVariable(scope + ".fail")->value.ToUint64()};
}

std::string ContextTop(const std::string& items) {
  return std::string(kContextChecker) + "module top;\n" + kTwoEdgeStimulus +
         items + "endmodule\n";
}

const std::pair<uint64_t, uint64_t> kOnPosedge{5, 0};
const std::pair<uint64_t, uint64_t> kOnNegedge{4, 1};

TEST(CheckerContextInferenceRun, AnInstanceUnderAnIfTakesTheProceduresClock) {
  EXPECT_EQ(CountsAt(ContextTop("  logic en = 1;\n"
                                "  default clocking @(negedge clk); "
                                "endclocking\n"
                                "  always @(posedge clk) begin\n"
                                "    if (en) begin\n"
                                "      chk k(a);\n"
                                "    end\n"
                                "  end\n"),
                     "k"),
            kOnPosedge);
}

TEST(CheckerContextInferenceRun, AnAlwaysFfInstanceTakesItsOwnClock) {
  EXPECT_EQ(CountsAt(ContextTop("  default clocking @(posedge clk); "
                                "endclocking\n"
                                "  always_ff @(negedge clk) begin\n"
                                "    chk k(a);\n"
                                "  end\n"),
                     "k"),
            kOnNegedge);
}

constexpr const char* kContextDefaults =
    "  logic rst = 1, r0 = 0;\n"
    "  wire wclk = clk;\n"
    "  default clocking @(posedge clk); endclocking\n"
    "  default disable iff rst;\n";

TEST(CheckerContextInferenceRun, EveryFormalConnectedByNameUsesItsActual) {
  std::string src =
      ContextTop(std::string(kContextDefaults) +
                 "  chk k(.sig(a), .clock(negedge clk), .reset(r0));\n"
                 "  chk k2(.sig(a), .clock(wclk), .reset(r0));\n");
  EXPECT_EQ(CountsAt(src, "k"), kOnNegedge);
  EXPECT_EQ(CountsAt(src, "k2"), std::make_pair(9ull, 1ull));
}

TEST(CheckerContextInferenceRun, EveryFormalConnectedByPositionUsesItsActual) {
  EXPECT_EQ(CountsAt(ContextTop(std::string(kContextDefaults) +
                                "  chk k(a, negedge clk, r0);\n"),
                     "k"),
            kOnNegedge);
}

TEST(CheckerContextInferenceRun, AConnectedClockLeavesTheResetInferred) {
  EXPECT_EQ(CountsAt(ContextTop("  logic rst = 1;\n"
                                "  initial #12 rst = 0;\n"
                                "  default clocking @(posedge clk); "
                                "endclocking\n"
                                "  default disable iff rst;\n"
                                "  chk k(.sig(a), .clock(negedge clk));\n"),
                     "k"),
            std::make_pair(3ull, 1ull));
}

TEST(CheckerContextInferenceRun, APackageCheckerTakesEachModulesClock) {
  std::string src = "package pk;\n" + std::string(kContextChecker) +
                    "endpackage\n"
                    "module mp(input logic clk, a);\n"
                    "  default clocking @(posedge clk); endclocking\n"
                    "  pk::chk k(a);\n"
                    "endmodule\n"
                    "module mn(input logic clk, a);\n"
                    "  default clocking @(negedge clk); endclocking\n"
                    "  pk::chk k(a);\n"
                    "endmodule\n"
                    "module top;\n" +
                    kTwoEdgeStimulus +
                    "  mp up(clk, a);\n"
                    "  mn un(clk, a);\n"
                    "endmodule\n";
  EXPECT_EQ(CountsAt(src, "up.k"), kOnPosedge);
  EXPECT_EQ(CountsAt(src, "un.k"), kOnNegedge);
}

constexpr const char* kLocalChecker =
    "  checker lc(logic sig, event clock = $inferred_clock,\n"
    "             logic reset = $inferred_disable);\n"
    "    int pass = 0, fail = 0;\n"
    "    a1: assert property (@clock disable iff (reset) sig) pass++;\n"
    "      else fail++;\n"
    "  endchecker\n";

TEST(CheckerContextInferenceRun, TheInstantiationDecidesNotTheDeclaration) {
  std::string src = ContextTop(
      "  default clocking @(negedge clk); "
      "endclocking\n" +
      std::string(kLocalChecker) +
      "  lc ks(a);\n"
      "  always @(posedge clk) begin\n"
      "    lc kp(a);\n"
      "  end\n");
  EXPECT_EQ(CountsAt(src, "ks"), kOnNegedge);
  EXPECT_EQ(CountsAt(src, "kp"), kOnPosedge);
}

TEST(CheckerContextInferenceRun, ANamedDefaultClockingIsInferred) {
  EXPECT_EQ(CountsAt(ContextTop("  default clocking cb @(negedge clk); "
                                "endclocking\n"
                                "  chk k(a);\n"),
                     "k"),
            kOnNegedge);
}

TEST(CheckerContextInferenceRun, AGenerateBlockTakesTheModulesClock) {
  std::string src = ContextTop(
      "  default clocking @(negedge clk); endclocking\n"
      "  if (1) begin : g\n    chk k(a);\n  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : gf\n    chk k(a);\n  end\n");
  EXPECT_EQ(CountsAt(src, "g.k"), kOnNegedge);
  EXPECT_EQ(CountsAt(src, "gf[0].k"), kOnNegedge);
}

TEST(CheckerContextInferenceRun, AGenerateBlocksOwnDefaultClockingIsInferred) {
  EXPECT_EQ(CountsAt(ContextTop("  if (1) begin : g\n"
                                "    default clocking @(negedge clk); "
                                "endclocking\n"
                                "    chk k(a);\n"
                                "  end\n"),
                     "g.k"),
            kOnNegedge);
}

TEST(CheckerContextInferenceRun, AnInterfaceOrProgramTakesItsDefaultClocking) {
  for (const char* keyword : {"interface", "program"}) {
    SCOPED_TRACE(keyword);
    std::string src = std::string(kContextChecker) + keyword +
                      " box(input logic clk, a);\n"
                      "  default clocking @(negedge clk); endclocking\n" +
                      kLocalChecker +
                      "  chk k(a);\n"
                      "  lc kl(a);\n"
                      "end" +
                      keyword +
                      "\n"
                      "module top;\n" +
                      kTwoEdgeStimulus + "  box b(clk, a);\nendmodule\n";
    EXPECT_EQ(CountsAt(src, "b.k"), kOnNegedge);
    EXPECT_EQ(CountsAt(src, "b.kl"), kOnNegedge);
  }
}

TEST(CheckerContextInferenceRun, ACheckersDefaultClockingOnALogicFormal) {
  std::string src = std::string(kContextChecker) +
                    "checker outer(logic s, logic ck);\n"
                    "  default clocking @(negedge ck); endclocking\n" +
                    kLocalChecker +
                    "  chk k(s);\n"
                    "  lc kl(s);\n"
                    "endchecker\n"
                    "module top;\n" +
                    kTwoEdgeStimulus + "  outer o(a, clk);\nendmodule\n";
  EXPECT_EQ(CountsAt(src, "o.k"), kOnNegedge);
  EXPECT_EQ(CountsAt(src, "o.kl"), kOnNegedge);
}

TEST(CheckerContextInferenceRun,
     DISABLED_ACheckersDefaultClockingOnAnEventFormal) {
  EXPECT_EQ(
      CountsAt(std::string(kContextChecker) +
                   "checker outer(logic s, event c);\n"
                   "  default clocking @c; endclocking\n"
                   "  chk k(s);\n"
                   "endchecker\n"
                   "module top;\n" +
                   kTwoEdgeStimulus + "  outer o(a, negedge clk);\nendmodule\n",
               "o.k"),
      kOnNegedge);
}

TEST(CheckerContextInferenceRun,
     DISABLED_ACheckerDeclaredInAGenerateBlockInfers) {
  EXPECT_EQ(CountsAt(ContextTop("  if (1) begin : g\n"
                                "    default clocking @(negedge clk); "
                                "endclocking\n" +
                                std::string(kLocalChecker) +
                                "    lc k(a);\n"
                                "  end\n"),
                     "g.k"),
            kOnNegedge);
}

std::string FormalKindTop(const std::string& formals,
                          const std::string& instance) {
  return "checker fk(" + formals +
         ");\n"
         "  int pass = 0, fail = 0;\n"
         "  a1: assert property (@clock disable iff (reset) sig) pass++;\n"
         "    else fail++;\n"
         "endchecker\n"
         "module top;\n" +
         kTwoEdgeStimulus +
         "  logic rst = 1;\n"
         "  initial #12 rst = 0;\n"
         "  default clocking @(negedge clk); endclocking\n"
         "  default disable iff rst;\n" +
         instance + "endmodule\n";
}

const std::pair<uint64_t, uint64_t> kNegedgeAfterReset{3, 1};

TEST(CheckerContextInferenceRun, EachKindOfFormalTakesTheInferredValues) {
  for (const char* formals :
       {"logic sig, untyped clock = $inferred_clock, untyped reset = "
        "$inferred_disable",
        "clock = $inferred_clock, logic sig, reset = $inferred_disable",
        "logic sig, event e, clock = $inferred_clock, logic reset = "
        "$inferred_disable",
        "logic sig, event clock = $inferred_clock, input bit reset = "
        "$inferred_disable"}) {
    SCOPED_TRACE(formals);
    std::string f = formals;
    std::string instance = f.find("event e") != std::string::npos
                               ? "  fk k(.sig(a), .e(posedge clk));\n"
                               : "  fk k(.sig(a));\n";
    EXPECT_EQ(CountsAt(FormalKindTop(f, instance), "k"), kNegedgeAfterReset);
  }
}

}  // namespace

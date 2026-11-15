#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunClean(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << src;
  return out;
}

struct Step {
  const char* value;
  const char* flags;
};

using Steps = std::vector<Step>;

std::string Flags(const std::string& operand, const std::string& clock) {
  std::string out = "{";
  const char* sep = "";
  for (const char* fn : {"$rose", "$fell", "$stable", "$changed"}) {
    out += sep;
    out += fn;
    out += "(";
    out += operand;
    out += clock;
    out += ")";
    sep = ", ";
  }
  return out + "}";
}

std::string Asserted(const std::string& condition) {
  return "  assert property (@(posedge clk) " + condition +
         ")\n    $display(\"ok %0d\", $time);\n"
         "    else $display(\"mismatch %0d\", $time);\n";
}

std::string Procedural(const std::string& flags) {
  return "  always @(posedge clk)\n    if (" + flags +
         " === e) $display(\"ok %0d\", $time);\n"
         "    else $display(\"mismatch %0d %b\", $time, " +
         flags + ");\n";
}

std::string Stimulus(const std::string& prefix, const std::string& var,
                     const Steps& steps) {
  std::string out = "  initial begin\n";
  const char* delay = "    ";
  for (const Step& step : steps) {
    out += delay;
    if (*step.value != '\0') {
      out += prefix + var + " = " + step.value + "; ";
    }
    out += prefix + "e = 4'b" + step.flags + ";\n";
    delay = "    #10 ";
  }
  return out + "  end\n";
}

std::string OkLines(size_t ticks) {
  std::string out;
  for (size_t i = 0; i < ticks; ++i) {
    out += "ok " + std::to_string(10 * i + 5) + "\n";
  }
  return out;
}

std::string Module(const std::string& outside, const std::string& items,
                   size_t ticks) {
  return outside +
         "module t;\n  logic clk = 0;\n  always #5 clk = ~clk;\n"
         "  logic [3:0] e;\n" +
         items + "  initial #" + std::to_string(10 * ticks) +
         " $finish(0);\nendmodule\n";
}

void ExpectEachContext(const std::string& decls, const std::string& var,
                       const std::string& operand, const Steps& steps) {
  const std::string kItems = decls + Stimulus("", var, steps);
  const std::string kChecks[] = {
      Asserted(Flags(operand, "") + " === e"),
      Procedural(Flags(operand, "")),
      Procedural(Flags(operand, ", @(posedge clk)")),
  };
  for (const std::string& check : kChecks) {
    EXPECT_EQ(RunClean(Module("", kItems + check, steps.size())),
              OkLines(steps.size()))
        << decls << check;
  }
}

void ExpectEachContext(const std::string& decls, const Steps& steps) {
  ExpectEachContext(decls, "v", "v", steps);
}

TEST(ValueChangeResultRun, AnUpperBitAloneNeitherRisesNorFalls) {
  ExpectEachContext("  logic [1:0] v = 2'b00;\n", {{"2'b00", "0010"},
                                                   {"2'b10", "0001"},
                                                   {"2'b11", "1001"},
                                                   {"2'b01", "0001"}});
  ExpectEachContext("  logic [1:0] v = 2'b01;\n", {{"2'b01", "0010"},
                                                   {"2'b11", "0001"},
                                                   {"2'b10", "0101"},
                                                   {"2'b00", "0001"}});
}

TEST(ValueChangeResultRun, StableAndChangedCompareTheWholeValue) {
  ExpectEachContext("  logic [1:0] v = 2'b00;\n",
                    {{"2'b00", "0010"}, {"2'b10", "0001"}, {"2'b10", "0010"}});
}

TEST(ValueChangeResultRun, AnUpperBitGoingToXOrZIsAChange) {
  ExpectEachContext("  logic [1:0] v = 2'b01;\n", {{"2'b01", "0010"},
                                                   {"2'bx1", "0001"},
                                                   {"2'b01", "0001"},
                                                   {"2'bz1", "0001"}});
}

TEST(ValueChangeResultRun, AnLsbLeavingXOrZ) {
  ExpectEachContext("  logic [1:0] v = 2'b0z;\n", {{"2'b0z", "0010"},
                                                   {"2'b01", "1001"},
                                                   {"2'b0x", "0001"},
                                                   {"2'b00", "0101"},
                                                   {"2'b1z", "0001"},
                                                   {"2'b10", "0101"},
                                                   {"2'b0z", "0001"}});
}

constexpr Step kBitWalk[] = {{"3'b000", ""},
                             {"3'b001", ""},
                             {"3'b011", ""},
                             {"3'b111", ""},
                             {"3'b101", ""}};

Steps Walk(const char* const (&flags)[5]) {
  Steps steps;
  for (size_t i = 0; i < 5; ++i) {
    steps.push_back({kBitWalk[i].value, flags[i]});
  }
  return steps;
}

TEST(ValueChangeResultRun, AnExpressionOperandFollowsItsOwnLsb) {
  const std::string kDecl = "  logic [2:0] w = 3'b000;\n";
  ExpectEachContext(kDecl, "w", "{w[2], w[0]}",
                    Walk({"0010", "1001", "0010", "0001", "0010"}));
  ExpectEachContext(kDecl, "w", "w[1]",
                    Walk({"0010", "0010", "1001", "0010", "0101"}));
  ExpectEachContext(kDecl, "w", "w[2:1]",
                    Walk({"0010", "0010", "1001", "0001", "0101"}));
}

TEST(ValueChangeResultRun, TwoStateAndStructOperandsFollowTheirLsb) {
  const Steps kSteps = {
      {"2", "0001"}, {"3", "1001"}, {"1", "0001"}, {"0", "0101"}};
  ExpectEachContext("  bit [1:0] v;\n", kSteps);
  ExpectEachContext("  int v;\n", kSteps);
  ExpectEachContext("  struct packed { logic hi; logic lo; } v = 2'b00;\n",
                    kSteps);
}

TEST(ValueChangeResultRun, TheResultIsOneBitWide) {
  EXPECT_EQ(RunClean(Module(
                "",
                "  logic [3:0] v = 0, w = 0;\n  int sum;\n"
                "  initial begin #10 v = 1; w = 1; end\n"
                "  always @(posedge clk) begin\n"
                "    sum = $rose(v) + $rose(w);\n"
                "    $display(\"%0d %0d %b %0d\", $time, $bits($rose(v)), "
                "$rose(v) + $rose(w), sum);\n"
                "  end\n",
                2)),
            "5 1 0 0\n15 1 0 2\n");
}

Steps ContainerSteps() { return {{"2'b01", "0010"}, {"2'b00", "0101"}}; }

std::string ContainerCheck() { return Asserted(Flags("v", "") + " === e"); }

TEST(ValueChangeResultRun, AnInterfaceAndAProgram) {
  EXPECT_EQ(RunClean(Module(
                "interface ifc(input logic clk);\n"
                "  logic [1:0] v = 2'b01;\n  logic [3:0] e;\n" +
                    ContainerCheck() + "endinterface\n",
                "  ifc u(clk);\n" + Stimulus("u.", "v", ContainerSteps()), 2)),
            OkLines(2));
  EXPECT_EQ(RunClean(Module("program pr(input logic clk);\n"
                            "  logic [1:0] v = 2'b01;\n  logic [3:0] e;\n" +
                                ContainerCheck() +
                                Stimulus("", "v", ContainerSteps()) +
                                "  initial #100;\nendprogram\n",
                            "  pr p(clk);\n", 2)),
            OkLines(2));
}

std::string CheckerOver(const std::string& items, const Steps& steps) {
  return Module("checker ck(logic clk, logic [1:0] v, logic [3:0] e);\n" +
                    items + "endchecker\n",
                "  logic [1:0] v = 2'b01;\n  ck c(clk, v, e);\n" +
                    Stimulus("", "v", steps),
                steps.size());
}

TEST(ValueChangeResultRun, DISABLED_ACheckersFormalStandsForItsActual) {
  EXPECT_EQ(RunClean(CheckerOver(ContainerCheck(), ContainerSteps())),
            OkLines(2));
}

std::string Sequence(const std::string& formals) {
  return "  sequence vc" + formals + "; " + Flags("v", "") +
         " === e; endsequence\n";
}

Steps SequenceSteps() {
  return {{"2'b10", "0101"}, {"2'b11", "1001"}, {"2'b01", "0001"}};
}

TEST(ValueChangeResultRun, ASequenceDeclaredInAPackageInterfaceOrProgram) {
  EXPECT_EQ(
      RunClean(Module("package pk;\n" + Sequence("(v, e)") + "endpackage\n",
                      "  logic [1:0] v = 2'b01;\n" +
                          Stimulus("", "v", SequenceSteps()) +
                          Asserted("pk::vc(v, e)"),
                      3)),
      OkLines(3));
  EXPECT_EQ(
      RunClean(Module("interface ifc(input logic clk);\n"
                      "  logic [1:0] v = 2'b01;\n  logic [3:0] e;\n" +
                          Sequence("") + "endinterface\n",
                      "  ifc u(clk);\n" + Stimulus("u.", "v", SequenceSteps()) +
                          Asserted("u.vc"),
                      3)),
      OkLines(3));
  EXPECT_EQ(RunClean(Module("program pr(input logic clk);\n"
                            "  logic [1:0] v = 2'b01;\n  logic [3:0] e;\n" +
                                Sequence("") + Asserted("vc") +
                                Stimulus("", "v", SequenceSteps()) +
                                "  initial #100;\nendprogram\n",
                            "  pr p(clk);\n", 3)),
            OkLines(3));
}

TEST(ValueChangeResultRun, ASequenceDeclaredInAChecker) {
  EXPECT_EQ(
      RunClean(CheckerOver(Sequence("") + Asserted("vc"), SequenceSteps())),
      OkLines(3));
}

TEST(DefaultSampledValueRun, AFallFromTheInitializer) {
  ExpectEachContext("  logic v = 1;\n", {{"0", "0101"}});
}

TEST(DefaultSampledValueRun, AnUninitializedFourStateVariableStartsAtX) {
  ExpectEachContext("  logic v;\n", {{"0", "0101"}, {"0", "0010"}});
  ExpectEachContext("  logic v;\n", {{"1", "1001"}, {"1", "0010"}});
  ExpectEachContext("  logic v;\n", {{"", "0010"}});
}

TEST(DefaultSampledValueRun, AnUninitializedTwoStateVariableStartsAtZero) {
  ExpectEachContext("  bit v;\n", {{"1", "1001"}});
  ExpectEachContext("  bit v;\n", {{"0", "0010"}});
}

TEST(DefaultSampledValueRun, AVectorAgainstItsInitializer) {
  ExpectEachContext("  logic [3:0] v = 4'h5;\n", {{"4'h6", "0101"}});
  ExpectEachContext("  logic [3:0] v = 4'h5;\n", {{"", "0010"}});
}

TEST(DefaultSampledValueRun, ANetStartsAtZ) {
  ExpectEachContext("  wire v;\n  assign v = 1;\n", "e", "v", {{"", "1001"}});
}

TEST(DefaultSampledValueRun, AnExpressionStartsAtItsOperandsDefaults) {
  ExpectEachContext("  logic a = 1, c;\n", "c", "a & c", {{"1", "1001"}});
}

TEST(DefaultSampledValueRun, AProcedureCallBeforeTheFirstTick) {
  EXPECT_EQ(RunClean(Module("",
                            "  logic s = 1;\n  logic [3:0] v = 4'h5;\n"
                            "  initial begin\n    #1 s = 0; v = 4'h6;\n"
                            "    #1 $display(\"%b %b\", $fell(s, @(posedge "
                            "clk)), $stable(v, @(posedge clk)));\n  end\n",
                            1)),
            "1 0\n");
}

std::string ShownBoth(const std::string& label) {
  return "$display(\"" + label + " %0d %b %b\", $time, b, $sampled(b))";
}

std::string Toggling(const std::string& items) {
  return Module("",
                "  logic b = 0, rst = 0, a = 0;\n"
                "  always @(posedge clk) b <= ~b;\n" +
                    items,
                3);
}

std::string ThreeTicks(const std::string& label) {
  return label + " 5 1 0\n" + label + " 15 0 1\n" + label + " 25 1 0\n";
}

std::string Directive(const std::string& head, const std::string& spec,
                      const std::string& tail) {
  std::string out = "  ";
  out += head;
  out += " (@(posedge clk) ";
  out += spec;
  out += ") ";
  out += tail;
  return out;
}

void ExpectEachActionBlock(const std::string& holds, const std::string& fails) {
  const std::string kPass = ShownBoth("pass") + ";\n";
  const std::string kFail = "else " + ShownBoth("fail") + ";\n";
  for (const char* kind : {"assert property", "assume property"}) {
    EXPECT_EQ(RunClean(Toggling(Directive(kind, holds, kPass))),
              ThreeTicks("pass"))
        << kind;
    EXPECT_EQ(RunClean(Toggling(Directive(kind, fails, kFail))),
              ThreeTicks("fail"))
        << kind;
  }
  for (const char* kind : {"cover property", "cover sequence"}) {
    EXPECT_EQ(RunClean(Toggling(Directive(kind, holds, kPass))),
              ThreeTicks("pass"))
        << kind;
  }
  EXPECT_EQ(RunClean(Toggling(Directive("initial expect", holds, kPass))),
            "pass 5 1 0\n");
}

TEST(SampledInAnActionBlockRun, EachActionBlockWhenThePropertyReadsIt) {
  ExpectEachActionBlock("b !== 1'bz", "b === 1'bz");
}

TEST(SampledInAnActionBlockRun,
     DISABLED_EachActionBlockWhenThePropertyDoesNotReadIt) {
  ExpectEachActionBlock("1", "0");
}

std::string ResetPulse() {
  return "  always @(posedge clk) rst <= ($time == 15 || $time == 25);\n";
}

std::string Disabled(const std::string& condition, int ticks) {
  return Module("",
                "  logic rst = 0;\n" + ResetPulse() +
                    "  assert property (@(posedge clk) disable iff (" +
                    condition +
                    ") 0)\n    else $display(\"fail %0d\", $time);\n",
                ticks);
}

TEST(SampledInADisableConditionRun, DISABLED_AResetRisingOrFallingInTheTick) {
  EXPECT_EQ(RunClean(Disabled("$sampled(rst)", 5)),
            "fail 5\nfail 15\nfail 45\n");
  EXPECT_EQ(RunClean(Disabled("rst", 5)), "fail 5\nfail 35\nfail 45\n");
}

std::string Implication(const std::string& condition,
                        const std::string& pulse) {
  return Module("",
                "  logic rst = 0, a = 0, b = 0;\n"
                "  initial begin #10 a = 1; #10 a = 0; end\n"
                "  initial begin " +
                    pulse +
                    " end\n"
                    "  assert property (@(posedge clk) disable iff (" +
                    condition +
                    ") a |=> b)\n    else $display(\"fail %0d\", $time);\n",
                4);
}

TEST(SampledInADisableConditionRun, AGlitchBetweenTicksOfAMultiTickAttempt) {
  EXPECT_EQ(RunClean(Implication("$sampled(rst)", "#22 rst = 1; #1 rst = 0;")),
            "fail 25\n");
  EXPECT_EQ(RunClean(Implication("$sampled(rst)", "#22 rst = 1; #5 rst = 0;")),
            "");
}

TEST(SampledInADisableConditionRun, DISABLED_ANamedPropertyAndADefaultDisable) {
  EXPECT_EQ(RunClean(Module("",
                            "  logic rst = 0;\n" + ResetPulse() +
                                "  property p;\n    @(posedge clk) disable iff "
                                "($sampled(rst)) 0;\n  endproperty\n"
                                "  assert property (p) else $display(\"fail "
                                "%0d\", $time);\n",
                            5)),
            "fail 5\nfail 15\nfail 45\n");
  EXPECT_EQ(RunClean(Module("",
                            "  logic rst = 0;\n" + ResetPulse() +
                                "  default disable iff ($sampled(rst));\n"
                                "  assert property (@(posedge clk) 0) else "
                                "$display(\"fail %0d\", $time);\n",
                            5)),
            "fail 5\nfail 15\nfail 45\n");
}

struct Wrapper {
  const char* open;
  const char* close;
  const char* instance;
};

constexpr Wrapper kWrappers[] = {
    {"interface w(input logic clk, b, rst);\n", "endinterface\n",
     "  w u(clk, b, rst);\n"},
    {"program w(input logic clk, b, rst);\n", "endprogram\n",
     "  w u(clk, b, rst);\n"},
    {"checker w(logic clk, logic b, logic rst);\n", "endchecker\n",
     "  w u(clk, b, rst);\n"},
};

std::string Wrapped(const Wrapper& w, const std::string& items) {
  return Module(w.open + items + w.close,
                "  logic b = 0, rst = 0;\n  always @(posedge clk) b <= ~b;\n" +
                    ResetPulse() + w.instance,
                5);
}

TEST(SampledInAnActionBlockRun, AnInterfaceAProgramAndAChecker) {
  for (const Wrapper& w : kWrappers) {
    EXPECT_EQ(RunClean(Wrapped(w,
                               "  assert property (@(posedge clk) b !== "
                               "1'bz) " +
                                   ShownBoth("pass") + ";\n")),
              "pass 5 1 0\npass 15 0 1\npass 25 1 0\npass 35 0 1\n"
              "pass 45 1 0\n")
        << w.open;
  }
}

TEST(SampledInADisableConditionRun, DISABLED_AnInterfaceAProgramAndAChecker) {
  for (const Wrapper& w : kWrappers) {
    EXPECT_EQ(
        RunClean(Wrapped(
            w,
            "  assert property (@(posedge clk) disable iff "
            "($sampled(rst)) 0)\n    else $display(\"fail %0d\", $time);\n")),
        "fail 5\nfail 15\nfail 45\n")
        << w.open;
  }
}

}  // namespace

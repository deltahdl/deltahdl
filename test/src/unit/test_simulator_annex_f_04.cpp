#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Verdicts {
  uint64_t pass = 0;
  uint64_t fail = 0;
};

std::string Stimulus(
    const std::vector<std::pair<std::string, std::string>>& ticks) {
  std::string out = "  initial begin\n";
  for (const auto& [a, b] : ticks) {
    out += "    a = ";
    out += a;
    out += "; b = ";
    out += b;
    out += "; #5 clk = 1; #5 clk = 0;\n";
  }
  return out + "  end\n";
}

std::vector<std::pair<std::string, std::string>> PartSelectTicks() {
  return {{"2'b01", "2'b00"},
          {"2'b10", "2'b00"},
          {"2'b00", "2'b10"},
          {"2'b01", "2'b10"},
          {"2'b11", "2'b01"}};
}

Verdicts VerdictsOf(const std::string& declarations,
                    const std::string& assertion, const std::string& prefix,
                    const std::string& stimulus) {
  SimFixture f;
  std::string src =
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic [0:1] a = 0, b = 0;\n"
      "  int pass = 0, fail = 0;\n";
  src += declarations;
  src += assertion;
  src += stimulus;
  src += "endmodule\n";
  auto* pass = RunAndFindVar(src, f, prefix + "pass");
  Verdicts v;
  if (pass == nullptr) {
    ADD_FAILURE() << "no " << prefix << "pass";
    return v;
  }
  v.pass = pass->value.ToUint64();
  v.fail = f.ctx.FindVariable(prefix + "fail")->value.ToUint64();
  return v;
}

void ExpectPartSelectOfACastActual(const std::string& declarations,
                                   const std::string& assertion,
                                   const std::string& prefix = "") {
  Verdicts v =
      VerdictsOf(declarations, assertion, prefix, Stimulus(PartSelectTicks()));
  EXPECT_EQ(v.pass, 2u);
  EXPECT_EQ(v.fail, 3u);
}

TEST(RewriteItemSim, APartSelectOfATypedSequenceFormalReadsTheCastActual) {
  ExpectPartSelectOfACastActual(
      "  sequence s(logic [0:3] v); v[1:2] == 2'b10; endsequence\n",
      "  assert property (@(posedge clk) s(type(logic [0:3])'({a, b})))\n"
      "    pass++; else fail++;\n");
}

TEST(RewriteItemSim, APartSelectOfATypedPropertyFormalReadsTheCastActual) {
  ExpectPartSelectOfACastActual(
      "  property p(logic [0:3] v); v[1:2] == 2'b10; endproperty\n",
      "  assert property (@(posedge clk) p(type(logic [0:3])'({a, b})))\n"
      "    pass++; else fail++;\n");
}

TEST(RewriteItemSim, APartSelectOfATypedCheckerFormalReadsTheCastActual) {
  ExpectPartSelectOfACastActual(
      "  checker c(logic [0:3] v, logic ck);\n"
      "    int pass = 0, fail = 0;\n"
      "    assert property (@(posedge ck) v[1:2] == 2'b10)\n"
      "      pass++; else fail++;\n"
      "  endchecker\n",
      "  c u(type(logic [0:3])'({a, b}), clk);\n", "u.");
}

TEST(RewriteItemSim, ABitSelectOfAnUntypedFormalReadsTheOperatorResult) {
  Verdicts v = VerdictsOf("  sequence s(x); x[2]; endsequence\n",
                          "  assert property (@(posedge clk) s({2'b00, a} + "
                          "b)) pass++; else fail++;\n",
                          "",
                          Stimulus({{"2'b01", "2'b11"},
                                    {"2'b01", "2'b01"},
                                    {"2'b10", "2'b10"},
                                    {"2'b11", "2'b11"}}));
  EXPECT_EQ(v.pass, 3u);
  EXPECT_EQ(v.fail, 1u);
}

TEST(RewriteItemSim,
     DISABLED_AMemberOfAnUntypedFormalReadsTheConditionalResult) {
  Verdicts v = VerdictsOf(
      "  typedef struct packed { logic hi; logic lo; } pair_t;\n"
      "  sequence s(x); x.lo; endsequence\n",
      "  assert property (@(posedge clk) s(a[0] ? pair_t'(a) : pair_t'(b)))\n"
      "    pass++; else fail++;\n",
      "",
      Stimulus({{"2'b01", "2'b01"},
                {"2'b10", "2'b01"},
                {"2'b11", "2'b00"},
                {"2'b00", "2'b01"}}));
  EXPECT_EQ(v.pass, 3u);
  EXPECT_EQ(v.fail, 1u);
}

TEST(RewriteItemSim, TriggeredOnASequenceFormalOfAPropertyReadsItsActual) {
  Verdicts v = VerdictsOf(
      "  property p(sequence f); f.triggered; endproperty\n",
      "  assert property (@(posedge clk) p(@(posedge clk) a[1] ##1 b[1]))\n"
      "    pass++; else fail++;\n",
      "",
      Stimulus({{"2'b01", "2'b00"},
                {"2'b00", "2'b01"},
                {"2'b00", "2'b01"},
                {"2'b01", "2'b00"},
                {"2'b00", "2'b01"}}));
  EXPECT_EQ(v.pass, 2u);
  EXPECT_EQ(v.fail, 3u);
}

TEST(RewriteItemSim, APropertyFormalTakesEveryOperationOfAPropertyInstance) {
  Verdicts v =
      VerdictsOf("  property p(property f); not f; endproperty\n",
                 "  assert property (@(posedge clk) p(a[1] |-> b[1]))\n"
                 "    pass++; else fail++;\n",
                 "",
                 Stimulus({{"2'b01", "2'b00"},
                           {"2'b01", "2'b01"},
                           {"2'b00", "2'b00"},
                           {"2'b01", "2'b00"}}));
  EXPECT_EQ(v.pass, 2u);
  EXPECT_EQ(v.fail, 2u);
}

}  // namespace

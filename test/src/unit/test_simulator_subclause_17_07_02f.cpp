#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

void RunDesign(SimFixture& f, const std::string& src, std::string_view first) {
  ASSERT_NE(RunAndFindVar(src, f, first), nullptr);
}

constexpr std::string_view kPairedChecker =
    "checker c(logic clk, bit [7:0] a, bit [7:0] b);\n"
    "  rand bit [7:0] q;\n"
    "  u3: assume property (@(posedge clk) q == a);\n"
    "  u4: assume property (@(posedge clk) q != b);\n"
    "endchecker\n";

TEST(AssumeSetFormation, AConstCastInsideAnActualLeavesTheAssumptionOut) {
  SimFixture f;
  RunDesign(f,
            std::string(kPairedChecker) +
                "module top;\n"
                "  logic clk = 0;\n"
                "  logic [7:0] v1 = 8'd5, v2 = 8'd5;\n"
                "  always #5 clk = ~clk;\n"
                "  c F1(clk, v1, const'(v2) + 8'd0);\n"
                "  c F2(clk, v1, {v2[7:4], const'(v2[3:0])});\n"
                "  c F3(clk, v1, v2 + 8'd0);\n"
                "  initial #30 $finish;\n"
                "endmodule\n",
            "F1.q");
  EXPECT_EQ(ValueOf(f, "F1.q"), 5u);
  EXPECT_EQ(ValueOf(f, "F2.q"), 5u);
  EXPECT_NE(ValueOf(f, "F3.q"), 5u);
}

TEST(AssumeSetFormation, AnAutomaticValueInsideAnActualLeavesTheAssumptionOut) {
  SimFixture f;
  RunDesign(f,
            std::string(kPairedChecker) +
                "module top;\n"
                "  logic clk = 0;\n"
                "  logic [7:0] v1 = 8'd5, v2 = 8'd5;\n"
                "  always #5 clk = ~clk;\n"
                "  always @(posedge clk) begin\n"
                "    automatic bit [7:0] w = 8'd5;\n"
                "    c F2(clk, v1, w + 8'd0);\n"
                "    c F4(clk, v1, v2 + 8'd0);\n"
                "  end\n"
                "  initial #30 $finish;\n"
                "endmodule\n",
            "F2.q");
  EXPECT_EQ(ValueOf(f, "F2.q"), 5u);
  EXPECT_NE(ValueOf(f, "F4.q"), 5u);
}

std::string ParentOverChild(const std::string& actual) {
  return "checker child(logic clk, bit [7:0] x);\n"
         "  u1: assume property (@(posedge clk) x == 8'd42);\n"
         "endchecker\n"
         "checker parent(logic clk, bit [7:0] v);\n"
         "  rand bit [7:0] q;\n"
         "  child B1(clk, " +
         actual +
         ");\n"
         "  int fail = 0;\n"
         "  a1: assert property (@(posedge clk) q == 8'd42) else fail++;\n"
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  logic [7:0] v = 8'd0;\n"
         "  always #5 clk = ~clk;\n"
         "  parent p(clk, v);\n"
         "  initial #200 $finish;\n"
         "endmodule\n";
}

TEST(AssumeSetFormation, AChildsActualHoldingAConstCastIsLeftOut) {
  SimFixture left_out;
  RunDesign(left_out, ParentOverChild("q + const'(v)"), "p.fail");
  EXPECT_GT(ValueOf(left_out, "p.fail"), 0u);
  SimFixture kept;
  RunDesign(kept, ParentOverChild("q + v"), "p.fail");
  EXPECT_EQ(ValueOf(kept, "p.fail"), 0u);
}

TEST(AssumeSetFormation,
     DISABLED_AChildsActualOverAnActiveAndAnInactiveVariableIsIn) {
  SimFixture f;
  RunDesign(f,
            "checker c1(logic clk);\n"
            "  rand bit [7:0] q, r;\n"
            "  always_ff @(posedge clk) r <= 8'd2;\n"
            "  checker c2(logic clk, bit [7:0] x);\n"
            "    u1: assume property (@(posedge clk) x == 8'd42);\n"
            "  endchecker\n"
            "  c2 B1(clk, q + r);\n"
            "  int fail = 0;\n"
            "  a1: assert property (@(posedge clk) 8'(q + r) == 8'd42) "
            "else fail++;\n"
            "endchecker\n"
            "module top;\n"
            "  logic clk = 0;\n"
            "  always #5 clk = ~clk;\n"
            "  c1 F1(clk);\n"
            "  initial #200 $finish;\n"
            "endmodule\n",
            "F1.fail");
  EXPECT_EQ(ValueOf(f, "F1.fail"), 0u);
  EXPECT_EQ(ValueOf(f, "F1.q"), 40u);
}

TEST(AssumeSetFormation,
     AChildsActualOverOnlyAnInactiveVariableStaysInTheChild) {
  SimFixture f;
  RunDesign(f,
            "checker c2(logic clk, bit [7:0] x);\n"
            "  rand bit [7:0] n;\n"
            "  u2: assume property (@(posedge clk) n == x);\n"
            "  int fail = 0;\n"
            "  a2: assert property (@(posedge clk) n == x) else fail++;\n"
            "endchecker\n"
            "checker c1(logic clk);\n"
            "  rand bit [7:0] r;\n"
            "  bit [7:0] cnt = 8'd0;\n"
            "  always_ff @(posedge clk) cnt <= cnt + 8'd1;\n"
            "  always_ff @(posedge clk) r <= cnt;\n"
            "  c2 B2(clk, r);\n"
            "endchecker\n"
            "module top;\n"
            "  logic clk = 0;\n"
            "  always #5 clk = ~clk;\n"
            "  c1 F1(clk);\n"
            "  initial #200 $finish;\n"
            "endmodule\n",
            "F1.B2.fail");
  EXPECT_EQ(ValueOf(f, "F1.B2.fail"), 0u);
  EXPECT_EQ(ValueOf(f, "F1.B2.n") + 1, ValueOf(f, "F1.r"));
}

TEST(AssumeSetFormation, AGrandchildsAssumptionJoinsTheGrandparentsSet) {
  SimFixture f;
  RunDesign(f,
            "checker leaf(logic clk, bit [7:0] y);\n"
            "  u1: assume property (@(posedge clk) y == 8'd42);\n"
            "endchecker\n"
            "checker child(logic clk, bit [7:0] x);\n"
            "  leaf L(clk, x);\n"
            "endchecker\n"
            "checker parent(logic clk, bit [7:0] v);\n"
            "  rand bit [7:0] q;\n"
            "  child B1(clk, q);\n"
            "  int fail = 0;\n"
            "  a1: assert property (@(posedge clk) q == 8'd42) else fail++;\n"
            "endchecker\n"
            "module top;\n"
            "  logic clk = 0;\n"
            "  always #5 clk = ~clk;\n"
            "  parent p(clk, 8'd0);\n"
            "  initial #200 $finish;\n"
            "endmodule\n",
            "p.fail");
  EXPECT_EQ(ValueOf(f, "p.fail"), 0u);
}

TEST(AssumeSetFormation, AChildInAGenerateBlockJoinsTheParentsSet) {
  for (std::string_view block :
       {"  if (1) begin : g\n    child B1(clk, q);\n  end\n",
        "  for (genvar i = 0; i < 1; i++) begin : g\n"
        "    child B1(clk, q);\n  end\n"}) {
    SCOPED_TRACE(block);
    SimFixture f;
    RunDesign(f,
              "checker child(logic clk, bit [7:0] x);\n"
              "  u1: assume property (@(posedge clk) x == 8'd42);\n"
              "endchecker\n"
              "checker parent(logic clk);\n"
              "  rand bit [7:0] q;\n" +
                  std::string(block) +
                  "  int fail = 0;\n"
                  "  a1: assert property (@(posedge clk) q == 8'd42) "
                  "else fail++;\n"
                  "endchecker\n"
                  "module top;\n"
                  "  logic clk = 0;\n"
                  "  always #5 clk = ~clk;\n"
                  "  parent p(clk);\n"
                  "  initial #200 $finish;\n"
                  "endmodule\n",
              "p.fail");
    EXPECT_EQ(ValueOf(f, "p.fail"), 0u);
  }
}

std::string SlowAssumptionFastSampling(const std::string& assumed) {
  return "checker chk(logic clk, logic fclk, logic a);\n"
         "  rand bit [15:0] y;\n"
         "  bit nf = 1'b1;\n"
         "  rand const bit k;\n"
         "  rand bit g;\n"
         "  always_ff @(posedge clk) g <= 1'b1;\n"
         "  m1: assume property (@(posedge clk) " +
         assumed +
         ");\n"
         "  int between = 0;\n"
         "  bit [15:0] last;\n"
         "  always_ff @(posedge fclk) begin\n"
         "    if ($time > 45 && $time % 40 != 25 && y != last)\n"
         "      between <= between + 1;\n"
         "    last <= y;\n"
         "  end\n"
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0, fclk = 0, a = 1;\n"
         "  initial begin #20; forever begin clk = 1; #20 clk = 0; #20; end "
         "end\n"
         "  always #5 fclk = ~fclk;\n"
         "  chk c(clk, fclk, a);\n"
         "  initial #400 $finish;\n"
         "endmodule\n";
}

TEST(AssumeSetFormation, AnAssumptionReadingNoActiveVariableLeavesTheSetEmpty) {
  for (std::string_view assumed : {"a", "nf", "k || !k", "g || !g"}) {
    SCOPED_TRACE(assumed);
    SimFixture f;
    RunDesign(f, SlowAssumptionFastSampling(std::string(assumed)), "c.between");
    EXPECT_GT(ValueOf(f, "c.between"), 5u);
  }
}

TEST(AssumeSetFormation, AnAssumptionReadingTheActiveVariableKeepsItClocked) {
  SimFixture f;
  RunDesign(f, SlowAssumptionFastSampling("y != 16'd0"), "c.between");
  EXPECT_EQ(ValueOf(f, "c.between"), 0u);
}

}  // namespace

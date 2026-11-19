#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclSim, EmptySpecifyBlockSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SpecifyBlockDeclSim, SpecifyWithAllItemKindsSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t(input a, clk, data, output b, out1, out2);\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(SpecifyBlockDeclSim, SpecifyBlockDoesNotInterfereBehavioral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input x, output y, out1, out2);\n"
      "  logic [7:0] a, b;\n"
      "  specify\n"
      "    pulsestyle_ondetect out1;\n"
      "    showcancelled out2;\n"
      "    (x => y) = 10;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 11u}, {"b", 22u}});
}

TEST(SpecifyBlockDeclSim, BehaviouralValuesMatchTheSameModuleWithoutTheBlock) {
  constexpr const char* kHead =
      "module t(input x, output y);\n"
      "  logic [7:0] a, b;\n"
      "  assign y = x;\n";
  constexpr const char* kBody =
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #3 b = a + 8'd7;\n"
      "    #4 a = b << 1;\n"
      "  end\n"
      "endmodule\n";
  SimFixture with_block;
  LowerRunAndCheck(with_block,
                   ElaborateSrc(std::string(kHead) +
                                    "  specify\n"
                                    "    pulsestyle_ondetect y;\n"
                                    "    showcancelled y;\n"
                                    "    (x => y) = 10;\n"
                                    "  endspecify\n" +
                                    kBody,
                                with_block),
                   {{"a", 24u}, {"b", 12u}});
  SimFixture without_block;
  LowerRunAndCheck(without_block,
                   ElaborateSrc(std::string(kHead) + kBody, without_block),
                   {{"a", 24u}, {"b", 12u}});
}

}  // namespace

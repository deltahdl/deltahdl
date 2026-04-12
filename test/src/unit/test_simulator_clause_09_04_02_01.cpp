#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_sensitivity.h"

using namespace delta;

namespace {

TEST(EventOrOperatorSimulation, CommaSynonymousWithOr) {
  std::vector<VarRef> comma_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  std::vector<VarRef> or_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  auto comma_result = ComputeImplicitSensitivity(comma_list);
  auto or_result = ComputeImplicitSensitivity(or_list);
  EXPECT_EQ(comma_result, or_result);
}

TEST(EventOrOperatorSimulation, OrTriggersOnAnyEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    rst = 0;\n"
      "    x = 0;\n"
      "    #5 rst = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk or posedge rst) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(EventOrOperatorSimulation, CommaTriggersOnAnyEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    rst = 0;\n"
      "    x = 0;\n"
      "    #5 rst = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk, posedge rst) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(EventOrOperatorSimulation, MixedOrCommaTriggersOnAnyEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, x;\n"
      "  initial begin\n"
      "    a = 0; b = 0; c = 0; x = 0;\n"
      "    #5 b = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(a or b, c) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(EventOrOperatorSimulation, OrAndCommaProduceIdenticalBehavior) {
  auto run = [](const char* sensitivity) -> uint64_t {
    SimFixture f;
    std::string src =
        "module m;\n"
        "  logic a, b, x;\n"
        "  initial begin\n"
        "    a = 0; b = 0; x = 0;\n"
        "    #5 a = 1;\n"
        "  end\n"
        "  initial begin\n"
        "    @(";
    src += sensitivity;
    src +=
        ") x = 1;\n"
        "  end\n"
        "endmodule\n";
    auto* design = ElaborateSrc(src, f);
    if (!design) return 0;
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    f.scheduler.Run();
    auto* var = f.ctx.FindVariable("x");
    return var ? var->value.ToUint64() : 0;
  };
  EXPECT_EQ(run("a or b"), run("a, b"));
}

}  // namespace

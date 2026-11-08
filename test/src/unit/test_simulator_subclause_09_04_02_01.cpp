#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EventOrOperatorSimulation, CommaSynonymousWithOr) {
  auto run = [](const char* sensitivity) -> uint64_t {
    SimFixture f;
    std::string src =
        "module m;\n"
        "  logic a, b, c, x;\n"
        "  initial begin\n"
        "    a = 0; b = 0; c = 0; x = 0;\n"
        "    #5 b = 1;\n"
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
  EXPECT_EQ(run("a or b or c"), run("a, b, c"));
  EXPECT_EQ(run("a or b or c"), 1u);
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

TEST(EventOrOperatorSimulation, OrTriggersOnNamedEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e1, e2;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    @(e1 or e2) x = 8'd42;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> e2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(EventOrOperatorSimulation, CommaTriggersOnNamedEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e1, e2;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    @(e1, e2) x = 8'd42;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> e2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

}  // namespace

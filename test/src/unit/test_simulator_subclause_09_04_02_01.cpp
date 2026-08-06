#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §9.4.2.1: a comma-separated sensitivity list shall be synonymous to the
// or-separated form. Elaborate and run one design body under both spellings
// while a middle operand (b) changes, then confirm the event control fires
// identically for each spelling — and that it actually fired (x == 1), so the
// equality cannot pass by both spellings silently doing nothing. This observes
// the parser's uniform treatment of `or` and `,` through the full pipeline.
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

// §9.4.2.1: the OR operator admits named-event operands, and the occurrence of
// any one of the events triggers the statement. One process blocks on an
// or-separated list of two named events; a second process triggers only the
// SECOND event. Running the design must unblock the waiter. This exercises the
// named-event operand type of the OR operator end-to-end -- the event
// declaration and the -> trigger come from the §9.4.2 event-control machinery
// -- observed at runtime rather than at parse time.
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

// §9.4.2.1: a comma acts as the event OR operator over named-event operands
// too. Same two named events spelled as a comma-separated list; triggering one
// of them must unblock the waiter, matching the or-separated behavior. Observes
// the comma spelling with the named-event operand type through the full
// pipeline.
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

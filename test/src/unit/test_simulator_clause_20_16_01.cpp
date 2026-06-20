#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.16.1 distinguishes the synchronous and asynchronous PLA array types. Both
// are evaluated by the simulator's PLA engine (eval_systask.cpp): a synchronous
// task evaluates only when it is called, an asynchronous task additionally
// re-evaluates whenever an input term or a personality-memory word changes, and
// both update their output terms without any delay. These tests drive a small
// AND-array (one output, two inputs) so the array-type behavior is observable
// from the final value of the output term.

uint64_t RunModule(SimFixture& f, const char* src, std::string_view var) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : 0;
}

// §20.16.1: "the output terms are updated without any delay." The output is
// readable as its newly computed value in the same time step, with no
// intervening delay control - here captured into another variable on the very
// next statement.
TEST(PlaArrayType, OutputsUpdatedWithoutDelay) {
  SimFixture f;
  uint64_t cap = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  logic [1:1] cap;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    cap = out;\n"
                           "  end\n"
                           "endmodule\n",
                           "cap");
  EXPECT_EQ(cap, 1u);
}

// §20.16.1: the asynchronous form re-evaluates whenever an input term changes
// value. After the call drives out high, lowering an input later in time makes
// the AND-array recompute on its own and drive out low - without re-calling the
// task.
TEST(PlaArrayType, AsyncReevaluatesOnInputChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
}

// §20.16.1: the synchronous form does NOT re-evaluate on its own. The same
// input change that drives the asynchronous output low leaves the synchronous
// output at the value computed at the call, because the call controls the time
// of evaluation.
TEST(PlaArrayType, SyncDoesNotReevaluateOnInputChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

// §20.16.1: a synchronous task evaluates each time it is called, so re-calling
// it after an input change updates the outputs to reflect the new inputs.
TEST(PlaArrayType, SyncReevaluatesWhenCalledAgain) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "    #1 in = 2'b10;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 0u);
}

// §20.16.1: the asynchronous form also re-evaluates whenever any word in the
// personality memory changes. With one input high and one low, narrowing the
// personality so it selects only the high input makes the AND-array recompute
// and drive out high - triggered solely by the memory write.
TEST(PlaArrayType, AsyncReevaluatesOnMemoryChange) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    #1 mem[1] = 2'b10;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

// §20.16.1: the no-delay update applies to the asynchronous form too. A
// change-driven re-evaluation takes effect in the same time step as the change
// that triggered it - here the lowered input and the capture of the output both
// happen at time zero, with no delay control between them, yet the output
// already reflects the new inputs.
TEST(PlaArrayType, AsyncOutputUpdatedWithoutDelay) {
  SimFixture f;
  uint64_t cap = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  logic [1:1] cap;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $async$and$array(mem, in, out);\n"
                           "    in = 2'b10;\n"
                           "    cap = out;\n"
                           "  end\n"
                           "endmodule\n",
                           "cap");
  EXPECT_EQ(cap, 0u);
}

// §20.16.1: the example calls drive the input and output terms as
// concatenations of scalars rather than as packed vectors. The asynchronous
// engine must collect each concatenated input signal as a trigger and unpack
// the result across the concatenated output terms. With a personality that maps
// each output to one input, lowering one input recomputes only that output
// term.
TEST(PlaArrayType, AsyncDrivesConcatenatedTermsOnInputChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a1, a2;\n"
      "  logic b1, b2;\n"
      "  logic [1:2] mem [1:2];\n"
      "  initial begin\n"
      "    a1 = 1'b1;\n"
      "    a2 = 1'b1;\n"
      "    mem[1] = 2'b10;\n"
      "    mem[2] = 2'b01;\n"
      "    $async$and$array(mem, {a1, a2}, {b1, b2});\n"
      "    #1 a2 = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  // Only the output term fed by the changed input recomputes; the other holds.
  EXPECT_EQ(b1->value.ToUint64(), 1u);
  EXPECT_EQ(b2->value.ToUint64(), 0u);
}

}  // namespace

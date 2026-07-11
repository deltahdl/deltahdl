#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.6.2: $bits returns a value whose type is integer; the simulator
// constructs the result as a 32-bit Logic4Vec irrespective of how wide the
// argument is.
TEST(UtilitySystemTaskTest, BitsResultIsInteger) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("v", 7);
  var->value = MakeLogic4VecVal(f.arena, 7, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// §20.6.2: $bits returns 0 when its argument is a dynamically sized
// expression that is currently empty. Built from real source: an unelaborated
// queue declared with no initializer holds zero elements, so its live
// bit-stream size is 0.
TEST(PrimarySim, BitsOfCurrentlyEmptyQueueReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 0u);
}

// §20.6.2: for a non-empty dynamically sized expression, $bits reports the
// live bit-stream size — the element count times the per-element width. Three
// 32-bit ints in a queue give 96. The queue is populated from a real
// assignment-pattern initializer (§7.10.1), not hand-built.
TEST(PrimarySim, BitsOfNonEmptyQueueReportsLiveBitStreamSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

// §20.6.2 (NC2): a 4-state value counts as 1 bit. A 32-bit logic vector — even
// holding all-x content — reports a bit-stream size of exactly 32, matching
// its declared width, though the runtime may use wider storage for the x/z
// encoding. Built from real source and driven through the full pipeline.
TEST(PrimarySim, BitsOf4StateVectorEqualsDeclaredWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  int n;\n"
      "  initial begin\n"
      "    v = 32'bx;\n"
      "    n = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 32u);
}

// §20.6.2 NC6: the packed struct {logic valid; bit [8:1] data;} has total
// bit-stream width 9 (1 + 8). $bits on either the typedef or a variable of
// that type shall report exactly that width.
TEST(PrimarySim, BitsOfPackedStructTypedefMatchesMemberSum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic valid; bit [8:1] data; } MyType;\n"
      "  int w_type;\n"
      "  int w_var;\n"
      "  MyType m;\n"
      "  initial begin\n"
      "    w_type = $bits(MyType);\n"
      "    w_var = $bits(m);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w_type = f.ctx.FindVariable("w_type");
  auto* w_var = f.ctx.FindVariable("w_var");
  ASSERT_NE(w_type, nullptr);
  ASSERT_NE(w_var, nullptr);
  EXPECT_EQ(w_type->value.ToUint64(), 9u);
  EXPECT_EQ(w_var->value.ToUint64(), 9u);
}

// §20.6.2 (NC1 data_type form): $bits(data_type) accepts a ranged built-in
// type and reports that packed vector's bit-stream size — 8 for logic [7:0].
// This is a distinct argument form from a bare keyword or a struct typedef.
TEST(PrimarySim, BitsOfRangedDataTypeArg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  initial n = $bits(logic [7:0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 8u);
}

// §20.6.2: the dynamically sized-expression rule also holds for a dynamic
// array (§7.5), a different source construct from a queue. Sized with a real
// new[3] initializer, its live bit-stream size is 3 * 32 = 96 — driven through
// the full pipeline, not hand-built.
TEST(PrimarySim, BitsOfDynamicArrayFromNewReportsLiveBitStreamSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[3];\n"
      "  int n;\n"
      "  initial n = $bits(d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

// §20.6.2 (NC5): because $bits folds to an elaboration-time constant on a
// fixed-size argument, it may define a parameter/localparam value — a code path
// distinct from a packed-dimension range. Here a localparam takes its value
// from $bits and then sizes a vector; reading $bits of that vector back at run
// time observes the constant that flowed through the parameter (16).
TEST(PrimarySim, BitsResultUsableAsLocalparamValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int W = $bits(16'h0);\n"
      "  logic [W-1:0] v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 16u);
}

}  // namespace

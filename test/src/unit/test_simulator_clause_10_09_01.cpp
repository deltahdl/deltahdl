#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The four element pointers of a 2x2 integer array named `arr`.
struct Array2x2 {
  Variable* e00 = nullptr;
  Variable* e01 = nullptr;
  Variable* e10 = nullptr;
  Variable* e11 = nullptr;
};

// Elaborates and runs `src`, then returns the four element pointers of a 2x2
// integer array named `arr`. Callers ASSERT on the pointers and their values to
// keep each test's distinct expectations local.
Array2x2 RunAndFetch2x2(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  LowerAndRun(design, f);
  Array2x2 out;
  out.e00 = f.ctx.FindVariable("arr[0][0]");
  out.e01 = f.ctx.FindVariable("arr[0][1]");
  out.e10 = f.ctx.FindVariable("arr[1][0]");
  out.e11 = f.ctx.FindVariable("arr[1][1]");
  EXPECT_NE(out.e00, nullptr);
  EXPECT_NE(out.e01, nullptr);
  EXPECT_NE(out.e10, nullptr);
  EXPECT_NE(out.e11, nullptr);
  return out;
}

TEST(ArrayLiteralSim, PositionalAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{8'hAA, 8'hBB, 8'hCC};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, PositionalVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33);
}

TEST(ArrayLiteralSim, ReplicationAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{3{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFF);
}

TEST(ArrayLiteralSim, ReplicationVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{3{8'hAA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

TEST(ArrayLiteralSim, DefaultAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{default: 8'h42};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x42);
}

TEST(ArrayLiteralSim, DefaultVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{default: 8'h99};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x99);
}

TEST(ArrayLiteralSim, IndexKeyWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{1: 8'hBB, default: 8'h00};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x00);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x00);
}

TEST(ArrayLiteralSim, IndexKeyVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{2: 8'hCC, default: 8'h11};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, DescendingRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [2:0] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, MultipleIndexKeysWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{0: 100, 2: 200, default: 0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 100u);
  EXPECT_EQ(e1->value.ToUint64(), 0u);
  EXPECT_EQ(e2->value.ToUint64(), 200u);
}

TEST(ArrayLiteralSim, DescendingRangeAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [1:0];\n"
      "  initial begin\n"
      "    arr = '{30, 40};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 30u);
  EXPECT_EQ(e0->value.ToUint64(), 40u);
}

TEST(ArrayLiteralSim, ReplicationMultiElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr = '{2{5, 10}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  auto* e3 = f.ctx.FindVariable("arr[3]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 10u);
  EXPECT_EQ(e2->value.ToUint64(), 5u);
  EXPECT_EQ(e3->value.ToUint64(), 10u);
}

TEST(ArrayLiteralSim, SingleElementInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:0] = '{42};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  ASSERT_NE(e0, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 42u);
}

TEST(ArrayLiteralSim, IndexKeyOnlyAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{0: 10, 1: 20, 2: 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
  EXPECT_EQ(e2->value.ToUint64(), 30u);
}

TEST(ArrayLiteralSim, NarrowToWideContextEval) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:1];\n"
      "  initial arr = '{1'b1, 1'b1};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 1u);
  EXPECT_EQ(e1->value.ToUint64(), 1u);
}

TEST(ArrayLiteralSim, WideToNarrowContextEval) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] arr [0:1];\n"
      "  initial arr = '{8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0xBu);
  EXPECT_EQ(e1->value.ToUint64(), 0xDu);
}

TEST(ArrayLiteralSim, PositionalMultidimensionalValues) {
  SimFixture f;
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e10, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(arr.e00->value.ToUint64(), 1u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 2u);
  EXPECT_EQ(arr.e10->value.ToUint64(), 3u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 4u);
}

TEST(ArrayLiteralSim, DefaultMultidimensionalValues) {
  SimFixture f;
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{default: '{default: 42}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e10, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(arr.e00->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e10->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 42u);
}

// §10.9.1: a type key sets every element whose type matches it and that an
// index key has not already set. Here the element type (int) matches the
// `int` key, so all elements take its value and the default is never reached.
TEST(ArrayLiteralSim, TypeKeyMatchesAllElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:2] = '{int: 42, default: 0};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 42u);
  EXPECT_EQ(e1->value.ToUint64(), 42u);
  EXPECT_EQ(e2->value.ToUint64(), 42u);
}

// §10.9.1: when the element type does not match the type key, the keyed value
// is skipped and the default key applies to the unmatched elements. The `int`
// key does not match the logic element type, so every element gets 8'hFF.
TEST(ArrayLiteralSim, TypeKeyMismatchFallsToDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{int: 8'h05, default: 8'hFF};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0xFFu);
  EXPECT_EQ(e1->value.ToUint64(), 0xFFu);
  EXPECT_EQ(e2->value.ToUint64(), 0xFFu);
}

// §10.9.1: a type key sets only those elements that an index key above has not
// already set. Here the index key claims element 0, so the `int` type key —
// which matches every element's type — must fall only to the remaining
// elements. Observing 100 at element 0 (not the type value 7) confirms the
// index-above-type precedence rather than either key winning outright.
TEST(ArrayLiteralSim, IndexKeyTakesPrecedenceOverTypeKey) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:2] = '{0: 100, int: 7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 100u);
  EXPECT_EQ(e1->value.ToUint64(), 7u);
  EXPECT_EQ(e2->value.ToUint64(), 7u);
}

// §10.9.1: a replication in an array pattern represents an entire single
// dimension. In a multidimensional array the outer replication fills the outer
// dimension and the inner replication fills the inner one, so '{2{'{3{9}}}}
// sets every leaf of a [1:2][1:3] array to 9. Observing all six leaves confirms
// the replication is expanded per dimension rather than broadcast as a scalar.
TEST(ArrayLiteralSim, NestedReplicationFillsEachDimension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int n [1:2][1:3];\n"
      "  initial n = '{2{'{3{9}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (int i = 1; i <= 2; ++i) {
    for (int j = 1; j <= 3; ++j) {
      auto name = "n[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* e = f.ctx.FindVariable(name);
      ASSERT_NE(e, nullptr) << name;
      EXPECT_EQ(e->value.ToUint64(), 9u) << name;
    }
  }
}

// §10.9.1: an index-keyed value is evaluated in the context of an assignment to
// the indexed element, so a value wider than the element is coerced to the
// element's width just as a positional item would be. Each 16-bit keyed literal
// lands in an 8-bit element as its low byte.
TEST(ArrayLiteralSim, IndexKeyedValueCoercedToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  initial arr = '{0: 16'h1234, 1: 16'h5678};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x34u);
  EXPECT_EQ(e1->value.ToUint64(), 0x78u);
}

// §10.9.1: the value paired with an index key is a full expression, not just a
// literal. Here a runtime expression over a variable supplies both the keyed
// element and the default, so the pattern is evaluated when the assignment
// runs.
TEST(ArrayLiteralSim, IndexKeyedValueEvaluatesExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:2];\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 5;\n"
      "    arr = '{1: k + 10, default: k};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 15u);
  EXPECT_EQ(e2->value.ToUint64(), 5u);
}

// §10.9.1: in a declaration initializer each positional item is evaluated in
// the assignment context of its element, so a 16-bit value is coerced to the
// 8-bit element. This exercises the declaration-init lowering path, which is
// separate from the procedural-assignment path.
TEST(ArrayLiteralSim, PositionalVarInitCoercesToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1] = '{16'h1234, 16'h5678};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x34u);
  EXPECT_EQ(e1->value.ToUint64(), 0x78u);
}

// §10.9.1: the same assignment-context coercion applies to a key-resolved value
// in a declaration initializer. The index-keyed and default-keyed 16-bit values
// are each narrowed to the 8-bit element.
TEST(ArrayLiteralSim, KeyedVarInitCoercesToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{0: 16'hAABB, default: 16'h00CC};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0xBBu);
  EXPECT_EQ(e1->value.ToUint64(), 0xCCu);
  EXPECT_EQ(e2->value.ToUint64(), 0xCCu);
}

}  // namespace

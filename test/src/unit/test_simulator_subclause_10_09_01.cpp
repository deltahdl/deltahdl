#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The four element pointers of a 2x2 unpacked array named `arr`.
struct Array2x2 {
  Variable* e00 = nullptr;
  Variable* e01 = nullptr;
  Variable* e10 = nullptr;
  Variable* e11 = nullptr;
};

// Elaborates and runs `src`, then returns the four element pointers of a 2x2
// unpacked array named `arr`. Callers ASSERT on the pointers and their values
// to keep each test's distinct expectations local.
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

// §10.9: an array pattern key is a constant expression, so `N-1` names an
// element as definitely as a number does. N is 3 here and the array runs 0 to
// 3, so the two keys name elements 2 and 3 and the default fills the two below
// them. Reading one token per key would make both keys `N`, putting one value
// on top of the other at element 3 and leaving element 2 with the default --
// which is what tells a key that was evaluated from one that was not.
TEST(ArrayLiteralSim, ConstantExpressionKeyNamesItsElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter N = 3;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial arr = '{N-1: 8'hAA, N: 8'hBB, default: 8'h11};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0xBB);
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
  RunModuleArray(f,
                 "module t;\n"
                 "  int arr [0:2];\n"
                 "  initial begin\n"
                 "    arr = '{0: 100, 2: 200, default: 0};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {100u, 0u, 200u});
}

// §10.9.1 over a descending range. A pattern's expressions match the array's
// elements in the order the declaration writes them, left to right: §10.10.1
// gives `int A3[1:3]; A3 = '{1, 2, 3};` as A3[1]=1, A3[2]=2, A3[3]=3, and
// §10.10 arranges the elements a concatenation represents "in left-to-right
// order to form the resulting array". The leftmost element of [1:0] is arr[1],
// so 30 lands there and 40 in arr[0] -- the reverse of what the expressions
// read as, which is what makes a descending range worth a test of its own.
// RunModuleArray checks by index, so the expectation is written that way.
TEST(ArrayLiteralSim, DescendingRangeAssignment) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int arr [1:0];\n"
                 "  initial begin\n"
                 "    arr = '{30, 40};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {40u, 30u});
}

TEST(ArrayLiteralSim, ReplicationMultiElement) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:3];\n"
                 "  initial arr = '{2{5, 10}};\n"
                 "endmodule\n",
                 "arr", {5u, 10u, 5u, 10u});
}

TEST(ArrayLiteralSim, SingleElementInit) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:0] = '{42};\n"
                 "endmodule\n",
                 "arr", {42u});
}

TEST(ArrayLiteralSim, IndexKeyOnlyAssignment) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2];\n"
                 "  initial arr = '{0: 10, 1: 20, 2: 30};\n"
                 "endmodule\n",
                 "arr", {10u, 20u, 30u});
}

TEST(ArrayLiteralSim, NarrowToWideContextEval) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:1];\n"
                 "  initial arr = '{1'b1, 1'b1};\n"
                 "endmodule\n",
                 "arr", {1u, 1u});
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
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2] = '{int: 42, default: 0};\n"
                 "endmodule\n",
                 "arr", {42u, 42u, 42u});
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
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2] = '{0: 100, int: 7};\n"
                 "endmodule\n",
                 "arr", {100u, 7u, 7u});
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
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2];\n"
                 "  int k;\n"
                 "  initial begin\n"
                 "    k = 5;\n"
                 "    arr = '{1: k + 10, default: k};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {5u, 15u, 5u});
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

// §10.9.1: a pattern item is assigned to its element, so the element ends up
// holding the item's value rather than continuing to name the item's storage.
// A bare variable name of the element's own width is the item that tells one
// reading from the other, because nothing about it needs resizing on the way
// in. `p` holds 8'hA5 when the pattern runs, so arr[0] has to keep 8'hA5 while
// a later deposit into a member of `p` -- which rewrites the bits of `p` where
// they stand instead of replacing them, the one write that could reach a
// shared buffer -- carries `p` on to 8'h35. An arr[0] that reads 8'h35 is the
// element and the variable turning out to be one storage. Every bit here is
// known, so ToUint64, which projects aval & ~bval, reads the whole element.
TEST(ArrayLiteralSim, PositionalItemVariableIsCopiedNotAliased) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1];\n"
      "  initial begin\n"
      "    p = 8'hA5;\n"
      "    arr = '{p, 8'h5A};\n"
      "    p.hi = 4'h3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vp = f.ctx.FindVariable("p");
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(vp, nullptr);
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0x35u);
  EXPECT_EQ(e0->value.ToUint64(), 0xA5u);
  EXPECT_EQ(e1->value.ToUint64(), 0x5Au);
}

// §10.9.1 through a nested pattern: the leaves of a multidimensional array are
// reached by their own recursive walk over the dimensions, so a leaf that takes
// a bare variable name is a second place the value has to be copied and needs a
// case of its own. `p` holds 8'hC3 when the pattern runs, so arr[0][0] has to
// keep 8'hC3 while `p` goes on to 8'hC7. The deposit is into `lo` here, the low
// nibble rather than the high one, so a leaf reading 8'hC7 has followed the
// storage of `p` and not a value taken from it. Its neighbours in the same
// pattern are read too: only the leaf named by a variable is in question.
TEST(ArrayLiteralSim, MultidimensionalLeafVariableIsCopiedNotAliased) {
  SimFixture f;
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1][0:1];\n"
      "  initial begin\n"
      "    p = 8'hC3;\n"
      "    arr = '{'{p, 8'h11}, '{8'h22, 8'h33}};\n"
      "    p.lo = 4'h7;\n"
      "  end\n"
      "endmodule\n",
      f);
  auto* vp = f.ctx.FindVariable("p");
  ASSERT_NE(vp, nullptr);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0xC7u);
  EXPECT_EQ(arr.e00->value.ToUint64(), 0xC3u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 0x11u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 0x33u);
}

// §10.9.1 through a key: an index-keyed value is resolved for each element in
// turn, a third route by which a pattern item arrives at an element, so the
// keyed form is asked the same question the positional one is. The key 0 pairs
// `p` with arr[0] and the default fills arr[1], so arr[0] has to hold the 8'h96
// standing in `p` at that moment; `p` afterwards reads 8'h46, and an arr[0]
// reading 8'h46 has been carried along by the deposit into `p.hi` rather than
// holding a value of its own.
TEST(ArrayLiteralSim, IndexKeyedVariableIsCopiedNotAliased) {
  SimFixture f;
  auto* e0 = RunAndFindVar(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1];\n"
      "  initial begin\n"
      "    p = 8'h96;\n"
      "    arr = '{0: p, default: 8'h0F};\n"
      "    p.hi = 4'h4;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[0]");
  ASSERT_NE(e0, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x96u);
  auto* vp = f.ctx.FindVariable("p");
  ASSERT_NE(vp, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0x46u);
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 0x0Fu);
}

// The six leaf pointers of a [1:2][1:3] unpacked array, the shape §10.9.1's own
// replication example declares. The bounds the declaration wrote are what name
// a leaf, so the leaves run arr[1][1] to arr[2][3] and there is no arr[0][0];
// e[i][j] here is the leaf at the declared indices i+1 and j+1.
struct Array2x3 {
  Variable* e[2][3] = {};
};

// Elaborates and runs `src`, then returns the six leaves of the [1:2][1:3]
// array `name`. A leaf the run never declared comes back null, so a caller
// asserts on the pointer before reading a value, and each test keeps its own
// per-leaf expectations local.
Array2x3 RunAndFetch2x3(const std::string& src, SimFixture& f,
                        std::string_view name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  LowerAndRun(design, f);
  Array2x3 out;
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      auto leaf = std::string(name) + "[" + std::to_string(i + 1) + "][" +
                  std::to_string(j + 1) + "]";
      out.e[i][j] = f.ctx.FindVariable(leaf);
      EXPECT_NE(out.e[i][j], nullptr) << leaf;
    }
  }
  return out;
}

// §10.9.1 writes its replication example as a declaration initializer:
// `int n[1:2][1:3] = '{2{'{3{y}}}};  // same as '{'{y,y,y},'{y,y,y}}`. The
// clause's `y` is a parameter here, a static variable's declaration initializer
// being evaluated once before time zero and so needing a constant expression.
// The leaves of a multidimensional array are made by a walk of their own,
// separate from the one that applies a single-dimension declaration
// initializer, and this is the case that asks whether that walk reads the
// initializer at all: a walk that does not read it leaves every leaf at §6.8
// Table 6-7's no-initializer default, which for the 2-state int is '0. That is
// why y is 7 and not 0 -- a leaf holding a written 0 and a leaf the initializer
// never reached read alike. Every bit of an int leaf is known, so ToUint64,
// which projects aval & ~bval, reads the whole of one.
TEST(ArrayLiteralSim, NestedReplicationVarInitFillsEveryLeaf) {
  SimFixture f;
  Array2x3 n = RunAndFetch2x3(
      "module m;\n"
      "  parameter int y = 7;\n"
      "  int n [1:2][1:3] = '{2{'{3{y}}}};\n"
      "endmodule\n",
      f, "n");
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      ASSERT_NE(n.e[i][j], nullptr) << i << " " << j;
      EXPECT_EQ(n.e[i][j]->value.ToUint64(), 7u) << i << " " << j;
    }
  }
}

// §10.9.1: "The expressions shall match element for element, and the braces
// shall match the array dimensions." A nested positional pattern in a
// declaration initializer therefore has an order to get right as well as a set
// of values: the outer pattern's first item is the subarray at the first index
// of the outer dimension, and within it the items run across the inner
// dimension. The declared bounds start at 1, so the first leaf is g[1][1] and
// the sixth g[2][3]; six distinct nonzero bytes tell a leaf that took the right
// item from one that took a neighbour's, and tell either from the 2-state '0 of
// §6.8's Table 6-7 that a leaf keeps when the initializer never reaches it.
// Every bit of a bit [7:0] leaf is known, so ToUint64 reads all eight.
TEST(ArrayLiteralSim, PositionalNestedVarInitIsRowMajor) {
  SimFixture f;
  Array2x3 g = RunAndFetch2x3(
      "module m;\n"
      "  bit [7:0] g [1:2][1:3] = '{'{8'h11, 8'h22, 8'h33},\n"
      "                             '{8'h44, 8'h55, 8'h66}};\n"
      "endmodule\n",
      f, "g");
  ASSERT_NE(g.e[0][0], nullptr);
  ASSERT_NE(g.e[0][1], nullptr);
  ASSERT_NE(g.e[0][2], nullptr);
  ASSERT_NE(g.e[1][0], nullptr);
  ASSERT_NE(g.e[1][1], nullptr);
  ASSERT_NE(g.e[1][2], nullptr);
  EXPECT_EQ(g.e[0][0]->value.ToUint64(), 0x11u);
  EXPECT_EQ(g.e[0][1]->value.ToUint64(), 0x22u);
  EXPECT_EQ(g.e[0][2]->value.ToUint64(), 0x33u);
  EXPECT_EQ(g.e[1][0]->value.ToUint64(), 0x44u);
  EXPECT_EQ(g.e[1][1]->value.ToUint64(), 0x55u);
  EXPECT_EQ(g.e[1][2]->value.ToUint64(), 0x66u);
}

// §10.9.1 describes one array pattern, and nothing in the clause distinguishes
// the pattern that initializes an array in its declaration from the pattern a
// procedural assignment gives the same array: both "match element for element",
// so both arrays here have to end the run holding the same six values. Writing
// the two in one module is what makes the reading exact. Should the leaves of
// `d` differ from the leaves of `p`, the difference is between a declaration
// and a statement and not between one array shape and another, the two arrays
// being declared alike; and should both hold the values, no route to a leaf has
// been left out. The values run 10 to 60 so that a leaf reading 0 is a leaf
// nothing wrote rather than a leaf written from the pattern. Both arrays are
// int, every bit known, so ToUint64 reads each leaf whole.
TEST(ArrayLiteralSim, VarInitLeafMatchesProceduralAssignLeaf) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d [1:2][1:3] = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (uint64_t i = 1; i <= 2; ++i) {
    for (uint64_t j = 1; j <= 3; ++j) {
      auto suffix = "[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* declared = f.ctx.FindVariable("d" + suffix);
      auto* assigned = f.ctx.FindVariable("p" + suffix);
      ASSERT_NE(declared, nullptr) << suffix;
      ASSERT_NE(assigned, nullptr) << suffix;
      uint64_t want = ((i - 1) * 3 + j) * 10;
      EXPECT_EQ(assigned->value.ToUint64(), want) << suffix;
      EXPECT_EQ(declared->value.ToUint64(), want) << suffix;
    }
  }
}

// §10.9.1 counts a pattern's positional items from a dimension's left bound --
// §10.10.1's `int A3[1:3]; A3 = '{1, 2, 3};` fills A3[1] first because 1 is the
// bound written on the left -- while §11.5.2 counts an element's address from
// the smaller of the two bounds, whichever way round the declaration wrote
// them. The two orders coincide only where a dimension ascends. `[2:1]`
// descends, so the outer pattern's first item is the row at address 2 and its
// second the row at address 1; the inner `[1:3]` ascends, so within a row the
// items run to addresses 1, 2, 3 in order. '{'{1, 2, 3}, '{4, 5, 6}} therefore
// puts 1, 2, 3 at a[2][1..3] and 4, 5, 6 at a[1][1..3]. A descending dimension
// names its leaves by address like any other, so the six names are a[1][1] to
// a[2][3] and only the order they are filled in differs.
//
// Nothing in §10.9.1 distinguishes the pattern that initializes an array in its
// declaration from the pattern a procedural assignment gives the same array, so
// `a` and `b` -- declared alike and given the same pattern -- have to end the
// run holding the same six values. Each leaf is read against the value the
// clause requires and against its counterpart in the other array. Reading the
// two arrays against each other alone would say only that they disagree;
// reading both against the clause says which of them is right. Every leaf is an
// int with all bits known, so ToUint64, which projects aval & ~bval, reads one
// whole.
TEST(ArrayLiteralSim, DescendingOuterDimVarInitAndAssignAgree) {
  SimFixture f;
  Array2x3 a = RunAndFetch2x3(
      "module m;\n"
      "  int a [2:1][1:3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  int b [2:1][1:3];\n"
      "  initial b = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "endmodule\n",
      f, "a");
  // Indexed by address, lowest first: the row at address 1 took the pattern's
  // second item and the row at address 2 its first.
  const uint64_t kRows[2][3] = {{4u, 5u, 6u}, {1u, 2u, 3u}};
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::string leaf =
          "b[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* proc = f.ctx.FindVariable(leaf);
      ASSERT_NE(a.e[i][j], nullptr) << leaf;
      ASSERT_NE(proc, nullptr) << leaf;
      EXPECT_EQ(a.e[i][j]->value.ToUint64(), kRows[i][j]) << leaf;
      EXPECT_EQ(proc->value.ToUint64(), kRows[i][j]) << leaf;
      EXPECT_EQ(proc->value.ToUint64(), a.e[i][j]->value.ToUint64()) << leaf;
    }
  }
}

// §10.9.1's left-bound counting applies to each dimension on its own, and which
// dimension descends decides what the pattern rearranges. `c[2:1][1:3]`
// descends outermost, so the outer items go to addresses 2 then 1 while each
// row's items go to 1, 2, 3: the rows are exchanged and their contents are
// not. `d[1:2][3:1]` descends innermost, so the rows go to addresses 1 then 2
// while the items within a row go to addresses 3, 2, 1: the rows stay put and
// each one is reversed. One pattern, '{'{10, 20, 30}, '{40, 50, 60}}, put into
// both arrays therefore has to come back two different ways, which is what
// tells a distributor that reads each dimension's own bounds from one that
// reads the array's first dimension for all of them or reads none at all. The
// inner-descending array is the harder half: a single-dimension array cannot
// pose the question, and ArrayInfo carries lo and size per dimension but one
// is_descending for the whole array, so an inner dimension's direction is not
// among the things the run-time distributor is handed. Both arrays are int with
// every bit known, so ToUint64 reads each leaf whole.
TEST(ArrayLiteralSim, DescendingInnerDimTakesItemsFromLeftBound) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int c [2:1][1:3];\n"
      "  int d [1:2][3:1];\n"
      "  initial begin\n"
      "    c = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "    d = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // Both tables are indexed by address, lowest first, so a row of one lines up
  // with the same pair of names in the other.
  const uint64_t kOuterDesc[2][3] = {{40u, 50u, 60u}, {10u, 20u, 30u}};
  const uint64_t kInnerDesc[2][3] = {{30u, 20u, 10u}, {60u, 50u, 40u}};
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::string addr =
          "[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* outer = f.ctx.FindVariable("c" + addr);
      auto* inner = f.ctx.FindVariable("d" + addr);
      ASSERT_NE(outer, nullptr) << addr;
      ASSERT_NE(inner, nullptr) << addr;
      EXPECT_EQ(outer->value.ToUint64(), kOuterDesc[i][j]) << addr;
      EXPECT_EQ(inner->value.ToUint64(), kInnerDesc[i][j]) << addr;
    }
  }
}

// The control on the two cases above. Where every dimension ascends, §10.9.1's
// left bound and §11.5.2's smaller bound are the same bound, so the item at
// position k belongs at address lo+k however the two rules are combined, and
// `[1:2][1:3]` must read row-major: 1, 2, 3 across the row at address 1 and 4,
// 5, 6 across the row at address 2. Both the declaration and the procedural
// spelling already read that way, and a distributor taught to count from the
// left bound has to leave both alone -- a fix that reversed something here
// would have swapped the two rules rather than told them apart. Every leaf is
// an int with all bits known, so ToUint64 reads one whole.
TEST(ArrayLiteralSim, AscendingDimsUnchangedByPerDimensionDirection) {
  SimFixture f;
  Array2x3 e = RunAndFetch2x3(
      "module m;\n"
      "  int e [1:2][1:3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "endmodule\n",
      f, "e");
  for (uint64_t i = 0; i < 2; ++i) {
    for (uint64_t j = 0; j < 3; ++j) {
      uint64_t want = i * 3 + j + 1;
      std::string cell =
          "p[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* assigned = f.ctx.FindVariable(cell);
      ASSERT_NE(e.e[i][j], nullptr) << cell;
      ASSERT_NE(assigned, nullptr) << cell;
      EXPECT_EQ(e.e[i][j]->value.ToUint64(), want) << cell;
      EXPECT_EQ(assigned->value.ToUint64(), want) << cell;
    }
  }
}

// §10.9.1 gives a keyed array pattern three rules -- "For index:value ...",
// "For type:value, if the element or subarray type of the array matches this
// type, then each element or subarray that has not already been set by an
// index key above shall be set to the value", and the default that covers what
// neither reached -- and writes none of the three for one dimension only. The
// element type of `p [1:2][1:3]` is int, which matches the `int` key, so the
// type key has to reach all six leaves just as it reaches all three elements of
// the one-dimensional `int arr [0:2] = '{int: 42}` above. A multidimensional
// array's leaves are filled by a walk of their own, and this is the case that
// asks whether that walk consults the type key at all: a walk that asks only
// for an index key and then a default finds neither in '{int: 7} and leaves
// each leaf at §6.8 Table 6-7's no-initializer default, which for a 2-state int
// is '0. `d` carries the same pattern in its declaration, a route that resolved
// type keys already, so reading the two arrays together says which spelling of
// the one pattern is wrong rather than only that a leaf holds the wrong number.
// 7 is not 0, so a leaf nothing wrote is never mistaken for one the pattern
// filled. Every bit of an int leaf is known, so ToUint64, which projects
// aval & ~bval, reads one whole.
TEST(ArrayLiteralSim, TypeKeyReachesEveryLeafOfMultidimAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d [1:2][1:3] = '{int: 7};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{int: 7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const std::string kLeaves[6] = {"[1][1]", "[1][2]", "[1][3]",
                                  "[2][1]", "[2][2]", "[2][3]"};
  for (const auto& leaf : kLeaves) {
    auto* declared = f.ctx.FindVariable("d" + leaf);
    auto* assigned = f.ctx.FindVariable("p" + leaf);
    ASSERT_NE(declared, nullptr) << leaf;
    ASSERT_NE(assigned, nullptr) << leaf;
    EXPECT_EQ(declared->value.ToUint64(), 7u) << leaf;
    EXPECT_EQ(assigned->value.ToUint64(), 7u) << leaf;
  }
}

// §10.9.1 states the three rules in an order and says so: an index key sets its
// element, "For type:value ... each element or subarray that has not already
// been set by an index key above shall be set to the value", and
// "The default:value applies to elements or subarrays that are not matched by
// either index or type key." One pattern carrying all three settles the order
// on a multidimensional target, where each of the two rows of `q [1:2][1:3]` is
// a subarray the outer pattern's keys are matched against. Address 1 is named
// by the index key, so that row takes 100 although the `int` key matches its
// type as well; address 2 is named by no index key, so the type key takes it
// and the row reads 7; and 55 appears nowhere, the default having nothing left
// to cover. Each row would read differently under any other order -- type
// before index puts 7 in both rows, default before type puts 55 at address 2 --
// so the three values separate the clause's order from the alternatives rather
// than merely showing a key was read. A row is broadcast whole, so all three of
// its leaves are checked and a partial fill cannot pass for a complete one.
// Every leaf is an int with all bits known, so ToUint64 reads one whole.
TEST(ArrayLiteralSim, MultidimKeyOrderIsIndexThenTypeThenDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [1:2][1:3];\n"
      "  initial q = '{1: 100, int: 7, default: 55};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // Indexed by outer address, lowest first: the row an index key claimed, then
  // the row the type key had to reach.
  const uint64_t kRowValue[2] = {100u, 7u};
  for (uint32_t i = 1; i <= 2; ++i) {
    for (uint32_t j = 1; j <= 3; ++j) {
      std::string leaf =
          "q[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* e = f.ctx.FindVariable(leaf);
      ASSERT_NE(e, nullptr) << leaf;
      EXPECT_EQ(e->value.ToUint64(), kRowValue[i - 1]) << leaf;
    }
  }
}

}  // namespace

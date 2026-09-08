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
  for (int i = 1; i <= 2; ++i) {
    for (int j = 1; j <= 3; ++j) {
      auto suffix = "[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* declared = f.ctx.FindVariable("d" + suffix);
      auto* assigned = f.ctx.FindVariable("p" + suffix);
      ASSERT_NE(declared, nullptr) << suffix;
      ASSERT_NE(assigned, nullptr) << suffix;
      uint64_t want = static_cast<uint64_t>(((i - 1) * 3 + j) * 10);
      EXPECT_EQ(assigned->value.ToUint64(), want) << suffix;
      EXPECT_EQ(declared->value.ToUint64(), want) << suffix;
    }
  }
}

}  // namespace



#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void RunAndExpectArray(
    SimFixture& f, RtlirDesign* design, const std::string& name,
    std::initializer_list<std::pair<int, uint64_t>> expected) {
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (const auto& [idx, val] : expected) {
    auto key = name + "[" + std::to_string(idx) + "]";
    auto* var = f.ctx.FindVariable(key);
    ASSERT_NE(var, nullptr) << key;
    EXPECT_EQ(var->value.ToUint64(), val) << key;
  }
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInPositionalPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{A3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ArrayItemInReplicatedPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{3{A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, ReplicationTargetingUnpackedArrayError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §10.10.1: the element-type rule ("every element item shall be of the same
// type as the element type of the target array") also governs an assignment
// pattern that initializes the array in its declaration, not only a procedural
// assignment. An array-typed item is illegal there too.
TEST(UnpackedArrayConcatElaboration, ArrayItemInDeclInitPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9] = '{A3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Precision guard: a declaration-initializer pattern whose items are all plain
// scalars of the element type is legal and must not trip the element-type
// check.
TEST(UnpackedArrayConcatElaboration, ScalarItemsInDeclInitPatternOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9] = '{1, 2, 3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.1: unpacked array concatenations forbid replication. The ban holds in
// a declaration initializer (`int A9[1:9] = {9{1}};`), an assignment-like
// context the procedural walk never reaches.
TEST(UnpackedArrayConcatElaboration, ReplicationInDeclInitTargetingArrayError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9] = {9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Precision guard: replication into a packed vector target (not an unpacked
// array) is ordinary §11.4.12.1 replication and must not be flagged.
TEST(UnpackedArrayConcatElaboration, ReplicationInDeclInitPackedTargetOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [8:0] x = {9{1'b1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.1 (SHALL#1): the element-type rule rejects an array-typed item even
// when the pattern replicates that item, and even when the pattern initializes
// the array in its declaration. `'{3{A3}}` repeats the wrong element type.
TEST(UnpackedArrayConcatElaboration,
     ArrayItemInReplicatedDeclInitPatternError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9] = '{3{A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §10.10.1 (SHALL#1) accept guard: a procedural assignment pattern whose items
// are all element-typed scalars is legal and must not trip the element-type
// check.
TEST(UnpackedArrayConcatElaboration, PositionalScalarPatternAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{1, 2, 3, 4, 5, 6, 7, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.1 (N1) boundary: replication is forbidden only in an unpacked array
// *concatenation* `{...}`. The identical replication count inside an assignment
// pattern `'{9{1}}` is legal, so the no-replication check must not fire here.
TEST(UnpackedArrayConcatElaboration, PatternReplicationIntoArrayAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A9[1:9];\n"
      "  initial A9 = '{9{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10.1 (N1): the no-replication rule holds regardless of how the count is
// written — a replication whose count is a §11.2.1 parameter is rejected just
// as a literal count is.
TEST(UnpackedArrayConcatElaboration, ReplicationWithParameterCountRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 9;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {N{1}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatScalarElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{0, 1}, {1, 2}, {2, 3}});
}

TEST(ArrayItemExpansionElaborates, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatDescending, UnpackedArrayConcatDescending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [2:0];\n"
      "  initial begin\n"
      "    arr = {10, 20, 30};\n"
      "  end\n"
      "endmodule\n",
      f);
  RunAndExpectArray(f, design, "arr", {{2, 10}, {1, 20}, {0, 30}});
}

}  // namespace

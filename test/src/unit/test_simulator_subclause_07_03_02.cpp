#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TaggedUnionSimulation, TaggedAssignment_SetsTagAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Valid 42;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(TaggedUnionSimulation, TaggedAssignment_OverwriteTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 10;\n"
      "    u = tagged B 20;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(TaggedUnionSimulation, VoidMemberTaggedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Invalid;\n"
      "    u = tagged Valid 99;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

// §7.3.2: a tagged union member may be read only through the name matching the
// current tag. Driven end-to-end from real source: the tag is set by a real
// `tagged` assignment (not a hand-set tag), then a read through the sibling
// member that does not match the tag is not type-consistent and yields unknown
// bits. This observes the read-consistency rule rather than the synthetic
// hand-built-type path above.
TEST(TaggedUnionSimulation, MismatchedMemberReadIsUnknownFromRealSource) {
  auto unknown = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 42;\n"
      "    result = $isunknown(u.B);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(unknown, 1u);
}

// The contrast to the mismatch case: reading through the member that does match
// the active tag is type-consistent and returns known bits. Sharing the same
// initialized value with the mismatch test shows the unknown result there comes
// from the tag mismatch, not from uninitialized storage.
TEST(TaggedUnionSimulation, MatchingMemberReadIsKnownFromRealSource) {
  auto known = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 42;\n"
      "    result = $isunknown(u.A);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(known, 0u);
}

// §7.3.2 packed representation, observed at run time end-to-end: the packed
// size of a tagged union is the tag width plus the widest member. A two-arm
// union whose widest arm is 32 bits needs one tag bit, so its bit count is 33.
TEST(TaggedUnionSimulation, PackedTaggedUnionBitsIsTagPlusMaxMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged packed { void Invalid; bit [31:0] Valid; } "
      "VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $bits(VInt);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

// Without the packed qualifier the tag is not part of the in-vector layout, so
// the same tagged union reports only its widest member's width at run time.
TEST(TaggedUnionSimulation, UnpackedTaggedUnionBitsHasNoTagBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; bit [31:0] Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $bits(VInt);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 32u);
}

}  // namespace

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

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
// hand-built-type path above. §11.9 (printed page 304) makes the read a
// run-time error as well, so the fixture is read directly: RunAndGet fails a
// case on any error the run raises.
TEST(TaggedUnionSimulation, MismatchedMemberReadIsUnknownFromRealSource) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 42;\n"
      "    result = $isunknown(u.B);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 1u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member 'B' of tagged "
                            "union 'u' which currently has tag 'A'",
                            7, "11.9"));
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

// §7.3.2 puts a packed tagged union's tag in the value's most significant bits,
// so a write naming another member rewrites the tag as well as the member:
// after `tagged v2` sets the tag bit to 1, `tagged v1 (85)` reads 0 followed by
// 1010101. Kept at 1, the stale tag read 11010101.
TEST(TaggedUnionSimulation, PackedTaggedUnionRetagRewritesTagBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  union tagged packed { bit [6:0] v1; bit [6:0] v2; } "
                       "un;\n"
                       "  initial begin\n"
                       "    un = tagged v2 (10);\n"
                       "    un = tagged v1 (85);\n"
                       "    $display(\"%b\", un);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "01010101\n");
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

// §7.3.2 has a tagged union hold the member its tag names, with that member's
// type, and §6.11.2 drops x and z only on the way into a 2-state type. A
// 4-state member keeps its z whatever the member declared before it: an
// unpacked union led by a `bit` member read the `logic` member back as 1001,
// and one led by a `logic` member read 1z01, so the two unions together tell
// the first member's type from the written member's.
TEST(TaggedUnionSimulation, FourStateMemberAfterTwoStateMemberKeepsZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  typedef union tagged { logic [3:0] A; logic [3:0] B; "
                       "} W;\n"
                       "  U u; W w;\n"
                       "  initial begin\n"
                       "    u = tagged B (4'b1z01);\n"
                       "    w = tagged B (4'b1z01);\n"
                       "    $display(\"%b %b\", u.B, w.B);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1z01 1z01\n");
}

// The contrast: a write of the same value into the 2-state member of that union
// drops the z to 0 by the member's type, after the 4-state member has held one.
TEST(TaggedUnionSimulation, TwoStateMemberBesideFourStateMemberDropsZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  U u;\n"
                       "  initial begin\n"
                       "    u = tagged B (4'b1z01);\n"
                       "    u = tagged A (4'b1z01);\n"
                       "    $display(\"%b\", u.A);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1001\n");
}

// The same union declared in a procedural block is the same object (§6.21), so
// its 4-state member keeps the z and its 2-state member drops it there too.
TEST(TaggedUnionSimulation, BlockLocalUnionKeepsFourStateMemberZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  initial begin : blk\n"
                       "    U bu;\n"
                       "    bu = tagged B (4'b1z01);\n"
                       "    $display(\"%b\", bu.B);\n"
                       "    bu = tagged A (4'b1z01);\n"
                       "    $display(\"%b\", bu.A);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1z01\n1001\n");
}

// §7.3 gives an unpacked union the default initial value of its first member,
// so a union led by a `bit` member starts at 0 even though a later member is
// 4-state and could hold x.
TEST(TaggedUnionSimulation, UnionLedByTwoStateMemberStartsAtZero) {
  SimFixture f;
  auto* u = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { bit [3:0] A; logic [3:0] B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(u->value.IsKnown());
  EXPECT_EQ(u->value.ToUint64(), 0u);
}

// §7.3.2 has every tagged union value carry its tag, a member that is itself a
// tagged union included, and §11.9 builds `tagged Jmp (tagged JmpV 10)` from
// the inner tagged value, tag and all. §21.2.1.6 prints a tagged union as its
// tag and its member's value, so the member prints in the same tagged form;
// with the inner tag lost it printed as the bare 10.
TEST(TaggedUnionSimulation, NestedTaggedValuePrintsInnerTag) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr instr;\n"
                       "  initial begin\n"
                       "    instr = tagged Jmp (tagged JmpV 10);\n"
                       "    $display(\"%p\", instr);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{Jmp:'{JmpV:10}}\n");
}

// §12.6 matches `tagged Jmp (tagged JmpV .v)` against the member's own tag as
// well as the outer one, so the inner tag the assignment gave the member
// selects the item; a pattern naming the other inner member, JmpU, is passed
// over.
TEST(TaggedUnionSimulation, NestedTaggedValueMatchesInnerTagPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr instr;\n"
                       "  initial begin\n"
                       "    instr = tagged Jmp (tagged JmpV 10);\n"
                       "    case (instr) matches\n"
                       "      tagged Jmp (tagged JmpU .u): $display(\"u=%0d\", "
                       "u);\n"
                       "      tagged Jmp (tagged JmpV .v): $display(\"v=%0d\", "
                       "v);\n"
                       "      default: $display(\"none\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "v=10\n");
}

}  // namespace

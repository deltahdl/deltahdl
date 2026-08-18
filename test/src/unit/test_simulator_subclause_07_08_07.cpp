#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(AssocArrayAllocation, AssignToNonexistentIntKeyCreatesEntry) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 42);
  auto rhs = MakeLogic4VecVal(f.arena, 32, 100);
  TryAssocIndexedWrite(sel, rhs, f.ctx, f.arena);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_EQ(aa->int_data.count(42), 1u);
  EXPECT_EQ(aa->int_data[42].ToUint64(), 100u);
}

TEST(AssocArrayAllocation, AssignToNonexistentStringKeyCreatesEntry) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);

  aa->str_data["newkey"] = MakeLogic4VecVal(f.arena, 32, 77);

  ASSERT_EQ(aa->str_data.count("newkey"), 1u);
  EXPECT_EQ(aa->str_data["newkey"].ToUint64(), 77u);
}

TEST(AssocArrayAllocation, AssignToExistingKeyOverwrites) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 5);
  auto rhs1 = MakeLogic4VecVal(f.arena, 32, 100);
  TryAssocIndexedWrite(sel, rhs1, f.ctx, f.arena);

  auto rhs2 = MakeLogic4VecVal(f.arena, 32, 200);
  TryAssocIndexedWrite(sel, rhs2, f.ctx, f.arena);

  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[5].ToUint64(), 200u);
}

TEST(AssocArrayAllocation, MultipleNonexistentKeysEachAllocated) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  for (int64_t k = 0; k < 5; ++k) {
    auto* sel = MakeAssocSelect(f.arena, k);
    auto rhs = MakeLogic4VecVal(f.arena, 32, static_cast<uint64_t>(k * 10));
    TryAssocIndexedWrite(sel, rhs, f.ctx, f.arena);
  }

  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 5u);
  for (int64_t k = 0; k < 5; ++k) {
    EXPECT_EQ(aa->int_data[k].ToUint64(), static_cast<uint64_t>(k * 10));
  }
}

TEST(AssocArrayAllocation, EndToEndAssignCreatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 55;\n"
      "    result = aa[10];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

// §7.8.7: a string-keyed nonexistent element is allocated the same way when it
// is the target of a plain assignment. Driven end-to-end through the write
// path so the allocation is observed via production, not a direct map insert.
TEST(AssocArrayAllocation, EndToEndStringKeyAssignCreatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 33;\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

TEST(AssocArrayAllocation, IncrementNonexistentUsesZeroDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, IncrementNonexistentUsesUserDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:10};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

TEST(AssocArrayAllocation, PrefixIncrementNonexistentAllocatesFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    ++aa[1];\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, DecrementNonexistentAllocatesWithDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:5};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3]--;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(AssocArrayAllocation, CompoundAddAssignNonexistentAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] += 7;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(AssocArrayAllocation, CompoundAddAssignNonexistentUsesUserDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:100};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] += 7;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 107u);
}

TEST(AssocArrayAllocation, IncrementThenReadSameKey) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    aa[1]++;\n"
      "    aa[1]++;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayAllocation, AssignAfterIncrementOverwrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1]++;\n"
      "    aa[1] = 99;\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(AssocArrayAllocation, StringKeyIncrementAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"key\"]++;\n"
      "    result = aa[\"key\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// §7.8.7: a nonexistent element shall be allocated when used as the actual to
// an argument passed by reference. The callee's write to the ref then persists
// back into the freshly allocated entry.
TEST(AssocArrayAllocation, RefArgToNonexistentElementAllocatesAndPersists) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic set_ref(ref int x);\n"
      "    x = 42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    set_ref(aa[7]);\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAllocation, RefArgAllocationGrowsArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic touch(ref int x);\n"
      "  endtask\n"
      "  initial begin\n"
      "    touch(aa[9]);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, RefArgToNonexistentStringKeyAllocates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  task automatic set_ref(ref int x);\n"
      "    x = 8;\n"
      "  endtask\n"
      "  initial begin\n"
      "    set_ref(aa[\"k\"]);\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 8u);
}

// §7.8.7's own example. b[2] does not exist when the member write executes, so
// the element is allocated holding the initial values its members declare and
// the write then updates x. The read of b[2].x observes the update.
TEST(AssocArrayAllocation, MemberWriteAllocatesElementThenUpdatesTheMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b[2].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// The other half of the same example: y is not written, so it holds the value
// the element type initializes it to rather than zero. This is what separates
// §7.8.7's allocation value from Table 7-1's nonexistent-entry value.
TEST(AssocArrayAllocation, MemberWriteLeavesTheOtherMemberAtItsInitialValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b[2].y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayAllocation, MemberWriteAllocatesExactlyOneEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    result = b.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// A second member write finds the element already allocated, so it updates its
// own member and leaves the one the first write set.
TEST(AssocArrayAllocation, MemberWriteToExistingElementKeepsTheOtherMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[2].y = 7;\n"
      "    result = b[2].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// §7.8.7 allocates for a write, not for a read: reading a member of an element
// that does not exist leaves the array empty. §7.8.6 governs what that read
// yields.
TEST(AssocArrayAllocation, MemberReadOfNonexistentElementAllocatesNothing) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int unused;\n"
      "  int result;\n"
      "  initial begin\n"
      "    unused = b[9].x;\n"
      "    result = b.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// §7.8.7: a bit within an element is still a target of an assignment, so the
// element is allocated. The other bits hold the 2-state element type's initial
// value, which is what makes the whole element read back as 8'h04.
TEST(AssocArrayAllocation, BitSelectWriteAllocatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][2] = 1'b1;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(AssocArrayAllocation, PartSelectWriteAllocatesElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

// The entry the bit-select write allocated is an entry of the array, not a
// variable standing beside it named "aa[3]".
TEST(AssocArrayAllocation, BitSelectWriteAllocatesExactlyOneEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][2] = 1'b1;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAllocation, PartSelectWriteToExistingElementKeepsItsOtherBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 16'hFF00;\n"
      "    aa[3][3:0] = 4'hA;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFF0Au);
}

// §7.8.7 allocates a referenced element with the array's user-specified initial
// value. The task reads its formal without writing it, so the value observed is
// the one the entry was allocated holding rather than one a later read of the
// array could have supplied.
TEST(AssocArrayAllocation, RefArgAllocatesWithTheUserSpecifiedDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:9};\n"
      "  int result;\n"
      "  task automatic grab(ref int x);\n"
      "    result = x;\n"
      "  endtask\n"
      "  initial begin\n"
      "    grab(aa[7]);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

}  // namespace

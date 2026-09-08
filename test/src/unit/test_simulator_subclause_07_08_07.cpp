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

// §7.8.7: the nonexistent element "shall be allocated with its default or
// user-specified initial value". Allocated *with* the value -- the entry takes
// it, and §6.8 then makes the entry "an abstraction of a data storage element"
// that "shall store a value from one assignment to the next". AssocAllocValue
// returned the array's own default_value rather than a copy of it, and
// Logic4Vec carries its `words` pointer rather than the words, so the entry
// this write allocates was the stored default. The write is a part-select,
// which deposits into the words it finds instead of replacing them, so the
// deposit landed in the default too and the array's default read 16'h00AB
// from then on. The read is of a key that was never allocated, which §7.8.6
// answers with the user-specified default of §7.9.11.
TEST(AssocArrayAllocation, PartSelectWriteLeavesTheUserDefaultIntact) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int] = '{default:16'h00FF};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x00FFu);
}

// The same defect between two entries rather than between an entry and the
// default: both keys are allocated from the default, so both were the default,
// so both were each other. The two writes are to disjoint halves of the
// element and the read is of the first key, which holds 16'h00AB where the
// entries are two storage elements and 16'hCDAB where they are one.
TEST(AssocArrayAllocation, PartSelectWriteToOneKeyLeavesAnotherKeyAlone) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] aa[int] = '{default:16'h00FF};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3][7:0] = 8'hAB;\n"
      "    aa[5][15:8] = 8'hCD;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x00ABu);
}

// §7.8.7's own example, with a second key added. The clause's element type
// carries its members' initializers, which the array stores as the initial
// value every allocation copies, and TryWriteAssocMemberField deposits a
// member into the entry it finds. So `b[2].x = 5` followed by `b[3].y = 7`
// wrote both members into the one buffer the stored initial value was, and
// b[3].x read the 5 the other key was given. Where the two entries are two
// storage elements, b[3].x is the x its own allocation gave it.
TEST(AssocArrayAllocation, MemberWriteToOneKeyLeavesAnotherKeysMemberAtInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[3].y = 7;\n"
      "    result = b[3].x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// The same pair read the other way round, which is the claim the first one
// cannot make: the second key's write must not reach the first key either.
TEST(AssocArrayAllocation, MemberWriteToASecondKeyLeavesTheFirstKeyAlone) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    b[2].x = 5;\n"
      "    b[3].y = 7;\n"
      "    result = b[2].y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// §7.9.11's default key may name a variable, and the value it names is the
// array's from then on rather than a second name for that variable's storage:
// §6.8 gives the variable its own storage and the array keeps a value. The
// literal was stored as the Logic4Vec EvalExpr answers a bare identifier with,
// which is the variable's own, so a bit-select write to seed -- a deposit into
// the words rather than a replacement of them -- rewrote the array's default,
// and with it every entry allocated from the default. The read is of a key
// that was never allocated, so what it answers is the default itself.
TEST(AssocArrayAllocation, UserDefaultDoesNotShareWithTheVariableItNames) {
  auto v = RunAndGet(
      "module t;\n"
      "  int seed = 9;\n"
      "  int aa[int] = '{default:seed};\n"
      "  int result;\n"
      "  initial begin\n"
      "    seed[3:0] = 4'hF;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// The stored initial value of a struct element is read back off the element
// model, a live Variable created under the array's own name, so it is copied
// on the way into the array. Nothing in SystemVerilog names that variable --
// `b` names the array -- so the claim is made against the storage: equal bits
// in two buffers rather than one buffer read twice. Its worth is that the two
// go on being independent as the model gains writers; the entries allocated
// from the stored value are already covered above.
TEST(AssocArrayAllocation, StoredElementInitialValueOwnsItsWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int x = 1; int y = 2; } xy_t;\n"
      "  xy_t b[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* aa = f.ctx.FindAssocArray("b");
  ASSERT_NE(aa, nullptr);
  ASSERT_TRUE(aa->has_elem_init);
  auto* model = f.ctx.FindVariable("b");
  ASSERT_NE(model, nullptr);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(model->value, aa->elem_init));
}

}  // namespace

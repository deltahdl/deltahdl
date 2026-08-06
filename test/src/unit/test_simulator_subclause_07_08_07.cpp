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

}  // namespace

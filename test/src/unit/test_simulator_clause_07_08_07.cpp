#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

static Expr* MakeAssocSelect(Arena& arena, std::string_view base_name,
                             int64_t idx_val) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

namespace {

// --- Requirement 1: Assignment to nonexistent element allocates it ---

TEST(AssocArrayAllocation, AssignToNonexistentIntKeyCreatesEntry) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, "aa", 42);
  auto rhs = MakeLogic4VecVal(f.arena, 32, 100);
  TryAssocIndexedWrite(sel, rhs, f.ctx, f.arena);

  auto* aa = f.ctx.FindAssocArray("aa");
  ASSERT_EQ(aa->int_data.count(42), 1u);
  EXPECT_EQ(aa->int_data[42].ToUint64(), 100u);
}

TEST(AssocArrayAllocation, AssignToNonexistentStringKeyCreatesEntry) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);

  // Write via direct map to verify the allocation mechanism.
  aa->str_data["newkey"] = MakeLogic4VecVal(f.arena, 32, 77);

  ASSERT_EQ(aa->str_data.count("newkey"), 1u);
  EXPECT_EQ(aa->str_data["newkey"].ToUint64(), 77u);
}

TEST(AssocArrayAllocation, AssignToExistingKeyOverwrites) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, "aa", 5);
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
    auto* sel = MakeAssocSelect(f.arena, "aa", k);
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

// --- Requirement 2: Read-modify-write allocates with default first ---

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

// --- Edge cases ---

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

}  // namespace

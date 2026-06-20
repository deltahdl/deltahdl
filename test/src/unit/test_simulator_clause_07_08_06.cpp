#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(AssocArray, ReadMissingKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* sel = MakeAssocSelect(f.arena, 99);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadExistingKeyNoWarning) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* sel = MakeAssocSelect(f.arena, 10);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexWriteWarns) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false, 32);

  MakeXTaintedKeyVar(f);
  auto* sel = MakeAssocSelectIdent(f.arena, "aa", "__xkey");

  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  uint32_t warns_before = f.diag.WarningCount();
  TryAssocIndexedWrite(sel, rhs_val, f.ctx, f.arena);

  EXPECT_GT(f.diag.WarningCount(), warns_before);
  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 0u);
}

TEST(AssocArray, XzIndexReadWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  MakeXTaintedKeyVar(f);
  auto* sel = MakeAssocSelectIdent(f.arena, "aa", "__xkey");

  uint32_t warns_before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), warns_before);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(AssocArray, ReadMissingKeyWithDefaultDoesNotWarn) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 77);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* sel = MakeAssocSelect(f.arena, 99);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 77u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexReadWithDefaultDoesNotWarn) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 55);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  MakeXTaintedKeyVar(f);
  auto* sel = MakeAssocSelectIdent(f.arena, "aa", "__xkey");

  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 55u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadMissingStringKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("bb", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = MakeAssocSelectStr(f.arena, "bb", "\"missing\"");

  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexWriteDoesNotClobberExistingEntries) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  MakeXTaintedKeyVar(f);
  auto* sel = MakeAssocSelectIdent(f.arena, "aa", "__xkey");

  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryAssocIndexedWrite(sel, rhs_val, f.ctx, f.arena);

  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[5].ToUint64(), 42u);
}

TEST(AssocArray, ReadMissing4StateKeyReturnsX) {
  SimFixture f;
  // For a 4-state element type, the nonexistent-entry value (Table 7-1, §7.4.5)
  // is all-x. §7.8.6 requires an invalid read to return that type value, so a
  // missing key must yield x rather than zero.
  f.ctx.CreateAssocArray("aa", 32, false, 32, false, true);

  auto* sel = MakeAssocSelect(f.arena, 7);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_TRUE(HasUnknownBits(result));
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadMissingStringKeyWithDefaultDoesNotWarn) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("bb", 32, true);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 88);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = MakeAssocSelectStr(f.arena, "bb", "\"missing\"");

  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 88u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

}  // namespace

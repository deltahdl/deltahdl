#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

static Expr* MakeAssocSelect(Arena& arena, int64_t idx_val) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

static Expr* MakeAssocSelectStr(Arena& arena, std::string_view base_name,
                                std::string_view key) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kStringLiteral;
  idx->text = key;
  sel->index = idx;
  return sel;
}

namespace {

TEST(AssocMethods, LiteralInitIntKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
}

TEST(AssocMethods, LiteralInitWithDefault) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_TRUE(aa->has_default);
  EXPECT_EQ(aa->default_value.ToUint64(), 99u);
}

TEST(AssocMethods, LiteralInitStringKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["Peter"] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->str_data["Paul"] = MakeLogic4VecVal(f.arena, 32, 22);
  aa->str_data["Mary"] = MakeLogic4VecVal(f.arena, 32, 23);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, static_cast<uint64_t>(-1));
  EXPECT_EQ(aa->str_data.size(), 3u);
  EXPECT_EQ(aa->str_data["Peter"].ToUint64(), 20u);
  EXPECT_TRUE(aa->has_default);
}

TEST(AssocMethods, LiteralInitDefaultOnly) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 42);
  EXPECT_EQ(aa->int_data.size(), 0u);
  EXPECT_TRUE(aa->has_default);
  EXPECT_EQ(aa->default_value.ToUint64(), 42u);
}

TEST(AssocMethods, EndToEndLiteralIntKeysWithDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  integer tab[string] = '{\"Peter\":20, \"Paul\":22, \"Mary\":23, "
      "default:-1};\n"
      "  int result;\n"
      "  initial result = tab[\"Peter\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocMethods, EndToEndLiteralDefaultOnlyReturnsDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:99};\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(AssocMethods, ReadMissingKeyWithDefaultReturnsDefaultNoWarning) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 77);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = MakeAssocSelect(f.arena, 99);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 77u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocMethods, ReadMissingStringKeyWithDefaultReturnsDefaultNoWarning) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 55);
  aa->str_data["exists"] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = MakeAssocSelectStr(f.arena, "aa", "\"missing\"");
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 55u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocMethods, ReadMissingKeyWithoutDefaultReturnsZero) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  EXPECT_FALSE(aa->has_default);

  auto* sel = MakeAssocSelect(f.arena, 99);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(AssocMethods, ReadMissingStringKeyWithoutDefaultReturnsZero) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["a"] = MakeLogic4VecVal(f.arena, 32, 1);
  EXPECT_FALSE(aa->has_default);

  auto* sel = MakeAssocSelectStr(f.arena, "aa", "\"b\"");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §7.9.11: with no literal default, a missing read yields the element type's
// Table 7-1 default (§7.4.5). For a 4-state element type that default is all-x,
// which exercises the 4-state branch of the read path rather than the 2-state
// zero branch covered above.
TEST(AssocMethods, ReadMissingKeyWithoutDefault4StateReturnsX) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->is_4state = true;
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  EXPECT_FALSE(aa->has_default);

  auto* sel = MakeAssocSelect(f.arena, 99);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  // Every bit unknown: both planes set across the element width.
  EXPECT_EQ(result.words[0].aval & 0xFFFFFFFFull, 0xFFFFFFFFull);
  EXPECT_EQ(result.words[0].bval & 0xFFFFFFFFull, 0xFFFFFFFFull);
}

TEST(AssocMethods, DefaultDoesNotAffectNum) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 99);

  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "num");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 2u);
}

TEST(AssocMethods, DefaultDoesNotAffectSize) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 50);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 0);

  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "size");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(AssocMethods, DefaultDoesNotAffectExists) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 99);

  Logic4Vec out{};
  auto* found = MkAssocCallInt(f.arena, "aa", "exists", 1);
  ASSERT_TRUE(TryEvalAssocMethodCall(found, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);

  Logic4Vec out2{};
  auto* missing = MkAssocCallInt(f.arena, "aa", "exists", 999);
  ASSERT_TRUE(TryEvalAssocMethodCall(missing, f.ctx, f.arena, out2));
  EXPECT_EQ(out2.ToUint64(), 0u);
}

TEST(AssocMethods, DefaultDoesNotAffectFirst) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);

  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 10u);
}

TEST(AssocMethods, DefaultDoesNotAffectLast) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);

  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 20u);
}

TEST(AssocMethods, DefaultDoesNotAffectNext) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 10);

  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 20u);
}

TEST(AssocMethods, DefaultDoesNotAffectPrev) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 20);

  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 10u);
}

TEST(AssocMethods, DefaultDoesNotAffectDelete) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 99);

  Logic4Vec out{};
  auto* call = MkAssocCallInt(f.arena, "aa", "delete", 1);
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_TRUE(aa->has_default);
}

// §7.9.11: the whole array contents can be replaced using an array literal,
// not just at declaration but in a procedural assignment.
TEST(AssocMethods, RuntimeLiteralReplacesWholeContents) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocMethods, RuntimeLiteralDropsPriorEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocMethods, RuntimeLiteralEstablishesNewEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[6];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

// §7.9.11 cross §7.8.6: a default supplied by the replacement literal governs
// subsequent reads of nonexistent indices.
TEST(AssocMethods, RuntimeLiteralDefaultGovernsMissingRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa = '{5:50, default:77};\n"
      "    result = aa[999];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(AssocMethods, RuntimeLiteralStringKeyedReplaces) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"old\"] = 1;\n"
      "    aa = '{\"x\":5, \"y\":9};\n"
      "    result = aa[\"y\"] + aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

}  // namespace

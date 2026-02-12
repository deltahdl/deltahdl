// Tests for aggregate value runtime: struct types, assignment patterns,
// pattern matching, tagged unions, and unpacked array concatenation.
// Covers §10.9, §10.10, §11.2.2, §11.4.14.4, §11.9, §12.6.

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// Helper fixture
// =============================================================================

struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* ParseExprFrom(const std::string& src, AggFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

// =============================================================================
// §7.2 Struct type metadata — StructTypeInfo registration
// =============================================================================

TEST(StructType, RegisterAndFind) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});  // MSB field: bits [15:8]
  info.fields.push_back({"y", 0, 8});  // LSB field: bits [7:0]

  f.ctx.RegisterStructType("point_t", info);
  auto* found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->type_name, "point_t");
  EXPECT_TRUE(found->is_packed);
  EXPECT_EQ(found->total_width, 16u);
  ASSERT_EQ(found->fields.size(), 2u);
  EXPECT_EQ(found->fields[0].name, "x");
  EXPECT_EQ(found->fields[0].bit_offset, 8u);
  EXPECT_EQ(found->fields[0].width, 8u);
  EXPECT_EQ(found->fields[1].name, "y");
  EXPECT_EQ(found->fields[1].bit_offset, 0u);
  EXPECT_EQ(found->fields[1].width, 8u);
}

TEST(StructType, FindNonexistent) {
  AggFixture f;
  EXPECT_EQ(f.ctx.FindStructType("no_such_type"), nullptr);
}

TEST(StructType, SetVariableStructType) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "color_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8});
  info.fields.push_back({"g", 8, 8});
  info.fields.push_back({"b", 0, 8});
  f.ctx.RegisterStructType("color_t", info);

  f.ctx.CreateVariable("pixel", 24);
  f.ctx.SetVariableStructType("pixel", "color_t");

  auto* type = f.ctx.GetVariableStructType("pixel");
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->type_name, "color_t");
  EXPECT_EQ(type->fields.size(), 3u);
}

TEST(StructType, GetVariableStructTypeUnknown) {
  AggFixture f;
  EXPECT_EQ(f.ctx.GetVariableStructType("nonexistent"), nullptr);
}

TEST(StructType, FieldTypeKindPreserved) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "typed_s";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});
  f.ctx.RegisterStructType("typed_s", info);
  auto* found = f.ctx.FindStructType("typed_s");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->fields[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(found->fields[1].type_kind, DataTypeKind::kByte);
}

// =============================================================================
// §10.9.2 Structure assignment patterns — named member
// =============================================================================

static Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

TEST(StructPattern, NamedMemberTwoFields) {
  // '{x: 5, y: 10} on struct { logic [7:0] x; logic [7:0] y; }
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"x", "y"};
  pat->elements = {MakeIntLit(f.arena, 5), MakeIntLit(f.arena, 10)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberReversedOrder) {
  // '{y: 10, x: 5} — order-independent, same result
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"y", "x"};
  pat->elements = {MakeIntLit(f.arena, 10), MakeIntLit(f.arena, 5)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberThreeFields) {
  // '{r: 0xFF, g: 0x80, b: 0x00} on 24-bit struct
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "rgb_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8, DataTypeKind::kLogic});
  info.fields.push_back({"g", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"r", "g", "b"};
  pat->elements = {MakeIntLit(f.arena, 0xFF), MakeIntLit(f.arena, 0x80),
                   MakeIntLit(f.arena, 0x00)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFF8000u);
}

// =============================================================================
// §10.9.2 Structure assignment patterns — default and type-keyed
// =============================================================================

TEST(StructPattern, DefaultAllFields) {
  // '{default: 0xFF} → all fields filled with 0xFF
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"default"};
  pat->elements = {MakeIntLit(f.arena, 0xFF)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFFFu);
}

TEST(StructPattern, DefaultWithNamedOverride) {
  // '{a: 1, default: 0} → a=1, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 0)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0100u);
}

TEST(StructPattern, TypeKeyedInt) {
  // '{int: 42} on struct { int a; logic [7:0] b; } → a=42, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "mixed_t";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"int"};
  pat->elements = {MakeIntLit(f.arena, 42)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), uint64_t{42} << 8);
}

TEST(StructPattern, MixedPrecedence) {
  // '{a: 1, byte: 2, default: 3} — member > type > default
  // struct { byte a; byte b; logic [7:0] c; }
  // a=1 (explicit member overrides byte key), b=2 (byte type key), c=3
  // (default)
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "multi_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"a", 16, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "byte", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 2),
                   MakeIntLit(f.arena, 3)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(result.ToUint64(), expected);
}

// =============================================================================
// §10.9 Assignment pattern evaluation
// =============================================================================

TEST(AssignmentPattern, PositionalTwoElements) {
  // '{a, b} with 8-bit variables → 16-bit packed result
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 8);
  auto* b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {a=5, b=10} → MSB-first: 5 in [15:8], 10 in [7:0] = 16'h050A
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPattern, PositionalThreeElements) {
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 4);
  auto* b = f.ctx.CreateVariable("b", 4);
  auto* c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {1, 2, 3} → 12-bit: 0x123
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

TEST(AssignmentPattern, SingleElement) {
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto* expr = ParseExprFrom("'{a}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(AssignmentPattern, EmptyPattern) {
  AggFixture f;
  auto* expr = ParseExprFrom("'{}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 0u);
}

TEST(AssignmentPattern, SizedLiterals) {
  // Test the parser fix for integer literal first elements
  AggFixture f;
  auto* expr = ParseExprFrom("'{32'd5, 32'd10}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Both are 32-bit (evaluator returns 32-bit for all int literals)
  // {32'd5, 32'd10} → 64-bit: upper=5, lower=10
  EXPECT_EQ(result.width, 64u);
  uint64_t expected = (uint64_t{5} << 32) | 10;
  EXPECT_EQ(result.ToUint64(), expected);
}

// =============================================================================
// §12.6 Pattern matching — matches operator
// =============================================================================

TEST(Matches, ExactMatchTrue) {
  // 42 matches 42 should be 1
  AggFixture f;
  auto* expr = ParseExprFrom("42 matches 42", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kBinary);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, ExactMatchFalse) {
  // 42 matches 99 should be 0
  AggFixture f;
  auto* expr = ParseExprFrom("42 matches 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, VariableMatch) {
  AggFixture f;
  auto* var = f.ctx.CreateVariable("sig", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  auto* expr = ParseExprFrom("sig matches 8'hAB", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// =============================================================================
// §11.9 Tagged union — tag tracking
// =============================================================================

TEST(TaggedUnion, SetAndGetTag) {
  AggFixture f;
  auto* var = f.ctx.CreateVariable("u", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  f.ctx.SetVariableTag("u", "field_a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "field_a");
}

TEST(TaggedUnion, TagDefaultEmpty) {
  AggFixture f;
  EXPECT_TRUE(f.ctx.GetVariableTag("nonexistent").empty());
}

TEST(TaggedUnion, ChangeTag) {
  AggFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

// =============================================================================
// §10.10 Unpacked array concatenation
// =============================================================================

TEST(UnpackedArrayConcat, BasicConcat) {
  // Create two array elements as flat variables, verify concatenation concept.
  AggFixture f;
  auto* a0 = f.ctx.CreateVariable("a[0]", 8);
  auto* a1 = f.ctx.CreateVariable("a[1]", 8);
  a0->value = MakeLogic4VecVal(f.arena, 8, 10);
  a1->value = MakeLogic4VecVal(f.arena, 8, 20);

  // Verify the flat naming convention for array elements.
  auto* found0 = f.ctx.FindVariable("a[0]");
  auto* found1 = f.ctx.FindVariable("a[1]");
  ASSERT_NE(found0, nullptr);
  ASSERT_NE(found1, nullptr);
  EXPECT_EQ(found0->value.ToUint64(), 10u);
  EXPECT_EQ(found1->value.ToUint64(), 20u);
}

// =============================================================================
// §11.2.2 Aggregate expressions — struct in set membership
// =============================================================================

TEST(AggregateExpr, PackedStructInsideSet) {
  // A packed struct is just a bitvector — inside should work by value.
  AggFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(AggregateExpr, PackedStructNotInSet) {
  AggFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 7);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// =============================================================================
// §7.8.6: Accessing invalid associative array indices
// =============================================================================

TEST(AssocArray, ReadMissingKeyWarns) {
  AggFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 99 (does not exist).  Should return default and warn.
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 99;
  sel->index = idx;
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadExistingKeyNoWarning) {
  AggFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 10 (exists).  Should NOT warn.
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 10;
  sel->index = idx;
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

// =============================================================================
// §7.4.5: Out-of-bounds array/queue access returns X
// =============================================================================

// Helper: build arr[idx] select expression.
static Expr* MkSelect(Arena& arena, std::string_view name, uint64_t idx) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* idx_expr = arena.Create<Expr>();
  idx_expr->kind = ExprKind::kIntegerLiteral;
  idx_expr->int_val = idx;
  sel->index = idx_expr;
  return sel;
}

TEST(ArrayAccess, OutOfBoundsReturnsX) {
  AggFixture f;
  // Register a 4-element array arr[0:3], each element 8 bits.
  f.ctx.RegisterArray("arr", {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
  // In-bounds: arr[2] should return 30.
  auto in_result = EvalExpr(MkSelect(f.arena, "arr", 2), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 30u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: arr[10] should return X.
  auto oob_result = EvalExpr(MkSelect(f.arena, "arr", 10), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

TEST(QueueAccess, OutOfBoundsReturnsX) {
  AggFixture f;
  auto* q = f.ctx.CreateQueue("q", 16);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 100));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 200));
  // In-bounds: q[1] should return 200.
  auto in_result = EvalExpr(MkSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 200u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: q[5] should return X.
  auto oob_result = EvalExpr(MkSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

// =============================================================================
// §7.4.5: Unpacked array slices
// =============================================================================

// Helper: build arr[hi:lo] range select expression.
static Expr* MkSlice(Arena& arena, std::string_view name, uint64_t hi,
                     uint64_t lo) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* hi_expr = arena.Create<Expr>();
  hi_expr->kind = ExprKind::kIntegerLiteral;
  hi_expr->int_val = hi;
  sel->index = hi_expr;
  auto* lo_expr = arena.Create<Expr>();
  lo_expr->kind = ExprKind::kIntegerLiteral;
  lo_expr->int_val = lo;
  sel->index_end = lo_expr;
  return sel;
}

// Helper: register a 4-element array and populate variables.
static void MakeArray4(AggFixture& f, std::string_view name) {
  f.ctx.RegisterArray(name, {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = std::string(name) + "[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
}

TEST(ArraySlice, ReadSliceConcat) {
  AggFixture f;
  MakeArray4(f, "arr");
  // arr = {10, 20, 30, 40}.  arr[2:1] should give {arr[2], arr[1]} = {30, 20}.
  // Concatenated into a 16-bit value: arr[2] in high byte, arr[1] in low byte.
  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  // arr[2]=30, arr[1]=20  →  (30 << 8) | 20 = 7700
  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

// =============================================================================
// §7.4.6: Array equality / inequality
// =============================================================================

// Helper: build (lhs == rhs) binary expression.
static Expr* MkEq(Arena& arena, std::string_view a, std::string_view b) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kEqEq;
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = a;
  auto* rhs = arena.Create<Expr>();
  rhs->kind = ExprKind::kIdentifier;
  rhs->text = b;
  expr->lhs = lhs;
  expr->rhs = rhs;
  return expr;
}

TEST(ArrayEquality, EqualArrays) {
  AggFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayEquality, UnequalArrays) {
  AggFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  // Modify b[2] to differ.
  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace

// §6.12: Real, shortreal, and realtime data types

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// §6.12: Realtime type — alias for real
// =========================================================================
TEST(ParserSection6, RealtimeWithInit) {
  // §6.12: realtime is equivalent to real for simulation.
  auto r = Parse("module t;\n"
                 "  realtime ts = 100.0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  ASSERT_NE(item->init_expr, nullptr);
}
// 5. Real variable declaration.
TEST(ParserSection6, Sec6_5_RealVarDeclKind) {
  auto r = Parse("module t;\n"
                 "  real voltage;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_FALSE(item->data_type.is_net);
}
// Non-integer types (real, shortreal, realtime).
TEST(ParserSection8, DataTypeSyntaxNonInteger) {
  auto r = Parse("module m;\n"
                 "  real r;\n"
                 "  shortreal sr;\n"
                 "  realtime rt;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kRealtime);
}
// =========================================================================
// §6.12: Real, shortreal, and realtime data types
// =========================================================================
TEST(ParserSection6, RealVarDecl) {
  auto r = Parse("module t;\n"
                 "  real r;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
}

TEST(ParserSection6, ShortrealVarDecl) {
  auto r = Parse("module t;\n"
                 "  shortreal sr;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
}

TEST(ParserSection6, RealtimeVarDecl) {
  auto r = Parse("module t;\n"
                 "  realtime rt;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
}

TEST(ParserSection6, RealTypesInProcedural) {
  // All real types declared inside initial block
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial begin\n"
                      "    real r;\n"
                      "    shortreal sr;\n"
                      "    realtime rt;\n"
                      "  end\n"
                      "endmodule\n"));
}
// =============================================================================
// LRM section 6.12 -- Real, shortreal, and realtime data types
// =============================================================================
TEST(ParserSection6, RealDecl) {
  // real is same as C double (LRM 6.12)
  auto r = Parse("module m;\n"
                 "  real r;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(item->name, "r");
}

TEST(ParserSection6, ShortrealDecl) {
  // shortreal is same as C float (LRM 6.12)
  auto r = Parse("module m;\n"
                 "  shortreal sr;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_EQ(item->name, "sr");
}

TEST(ParserSection6, RealtimeDecl) {
  // realtime is synonymous with real (LRM 6.12)
  auto r = Parse("module m;\n"
                 "  realtime rt;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  EXPECT_EQ(item->name, "rt");
}

TEST(ParserSection6, MultipleRealDecls) {
  auto r = Parse("module m;\n"
                 "  real a, b, c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, AllRealTypes) {
  // All three real-family types in one module
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  real r;\n"
                      "  shortreal sr;\n"
                      "  realtime rt;\n"
                      "endmodule\n"));
}

// --- Shortreal specifics (LRM 6.12) ---
TEST(ParserSection6, ShortrealInModule) {
  // shortreal is same as C float (LRM 6.12)
  auto r = Parse("module m;\n"
                 "  shortreal x = 1.0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
}

TEST(ParserSection6, ShortrealInFunctionArg) {
  // shortreal as function argument type
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function shortreal scale(shortreal val, shortreal factor);\n"
              "    return val * factor;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// --- non_integer_type ---
// shortreal | real | realtime
TEST(ParserA221, NonIntegerTypes) {
  auto r = Parse("module m;\n"
                 "  shortreal a;\n"
                 "  real b;\n"
                 "  realtime c;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind,
            DataTypeKind::kShortreal);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind,
            DataTypeKind::kRealtime);
}

} // namespace

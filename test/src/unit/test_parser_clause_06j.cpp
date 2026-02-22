#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string &src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FirstItem(ParseResult6j &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto &items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.7.1 -- Net declarations with built-in net types
// =============================================================================

// 1. wire logic [7:0] w; — explicit data type after net keyword, no errors.
TEST(ParserSection6, Sec6_7_1_WireExplicitLogicNoErrors) {
  auto r = Parse("module t;\n"
                 "  wire logic [7:0] w;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

// 2. wire addressT w1; — user-defined type after net keyword (§6.7.1 example).
TEST(ParserSection6, Sec6_7_1_WireWithUserDefinedType) {
  auto r = Parse("module t;\n"
                 "  typedef logic [31:0] addressT;\n"
                 "  wire addressT w1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(items[1]->data_type.type_name, "addressT");
  EXPECT_EQ(items[1]->name, "w1");
}

// 3. wire struct packed { ... } memsig; — struct type after net keyword.
TEST(ParserSection6, Sec6_7_1_WireWithPackedStructType) {
  auto r =
      Parse("module t;\n"
            "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "memsig");
}

// 4. trireg (large) logic cap1; — charge strength + explicit type (LRM §6.7.1).
TEST(ParserSection6, Sec6_7_1_TriregChargeStrengthWithLogic) {
  auto r = Parse("module t;\n"
                 "  trireg (large) logic cap1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "cap1");
}

// 5. Multiple nets with explicit type: wire logic a, b, c;
TEST(ParserSection6, Sec6_7_1_MultipleNetsExplicitType) {
  auto r = Parse("module t;\n"
                 "  wire logic a, b, c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[2]->data_type.is_net);
  EXPECT_EQ(items[2]->name, "c");
}

// 6. wire vectored logic [7:0] v; — vectored with explicit type.
TEST(ParserSection6, Sec6_7_1_VectoredWithExplicitType) {
  auto r = Parse("module t;\n"
                 "  wire vectored logic [7:0] v;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "v");
}

// 7. wire scalared logic [7:0] s; — scalared with explicit type.
TEST(ParserSection6, Sec6_7_1_ScalaredWithExplicitType) {
  auto r = Parse("module t;\n"
                 "  wire scalared logic [7:0] s;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "s");
}

// 8. tri bit [3:0] b; — non-logic 4-state type after net keyword (parser
// accepts).
TEST(ParserSection6, Sec6_7_1_NetWithExplicitBitType) {
  auto r = Parse("module t;\n"
                 "  tri bit [3:0] b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "b");
}

// 9. wire (strong0, weak1) logic [7:0] w; — drive strength + explicit type.
TEST(ParserSection6, Sec6_7_1_DriveStrengthWithExplicitType) {
  auto r = Parse("module t;\n"
                 "  wire (strong0, weak1) logic [7:0] w;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// 10. wire signed [7:0] w; — implicit type with signing (already works,
// baseline).
TEST(ParserSection6, Sec6_7_1_NetImplicitSigned) {
  auto r = Parse("module t;\n"
                 "  wire signed [7:0] ws;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ws");
}

// =============================================================================
// LRM section 6.21 -- Scope and lifetime (automatic/static)
// =============================================================================

TEST(ParserSection6, Sec6_21_LifetimeAutomaticAndStatic) {
  // Module lifetime qualifiers
  EXPECT_TRUE(ParseOk("module automatic m; endmodule\n"));
  EXPECT_TRUE(ParseOk("module static m; endmodule\n"));
  auto fa = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b); return a+b; endfunction\n"
      "endmodule\n");
  ASSERT_NE(fa.cu, nullptr);
  EXPECT_FALSE(fa.has_errors);
  EXPECT_EQ(fa.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(fa.cu->modules[0]->items[0]->is_automatic);
  auto fs =
      Parse("module m;\n"
            "  function static int mul(int a, int b); return a*b; endfunction\n"
            "endmodule\n");
  ASSERT_NE(fs.cu, nullptr);
  EXPECT_FALSE(fs.has_errors);
  EXPECT_TRUE(fs.cu->modules[0]->items[0]->is_static);
  auto ta =
      Parse("module m; task automatic t(input int x); endtask endmodule\n");
  ASSERT_NE(ta.cu, nullptr);
  EXPECT_FALSE(ta.has_errors);
  EXPECT_TRUE(ta.cu->modules[0]->items[0]->is_automatic);
  auto ts = Parse("module m; task static t(input int x); endtask endmodule\n");
  ASSERT_NE(ts.cu, nullptr);
  EXPECT_FALSE(ts.has_errors);
  EXPECT_TRUE(ts.cu->modules[0]->items[0]->is_static);
  // Top-level function with automatic lifetime
  auto tl = Parse("function automatic int foo(int x);\n"
                  "  return x + 1;\n"
                  "endfunction\n");
  ASSERT_NE(tl.cu, nullptr);
  EXPECT_FALSE(tl.has_errors);
  ASSERT_GE(tl.cu->cu_items.size(), 1u);
  EXPECT_EQ(tl.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(tl.cu->cu_items[0]->is_automatic);
  EXPECT_EQ(tl.cu->cu_items[0]->name, "foo");
  // Top-level task in compilation-unit scope
  auto tt = Parse("task automatic my_task(input int x); endtask\n");
  ASSERT_NE(tt.cu, nullptr);
  EXPECT_FALSE(tt.has_errors);
  ASSERT_GE(tt.cu->cu_items.size(), 1u);
  EXPECT_EQ(tt.cu->cu_items[0]->kind, ModuleItemKind::kTaskDecl);
  // Program with automatic lifetime
  EXPECT_TRUE(ParseOk("program automatic test_prog;\n"
                      "  initial begin $display(\"hello\"); end\n"
                      "endprogram\n"));
}

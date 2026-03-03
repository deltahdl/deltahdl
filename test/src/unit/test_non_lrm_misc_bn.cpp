// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult6i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static Stmt* FirstInitialStmt(ParseResult6i& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock && item->body != nullptr)
      return item->body;
  }
  return nullptr;
}

// Helper: find a module item by name.
static ModuleItem* FindItemByName(ParseResult6i& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6j& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// 12. type() comparison with !== (case inequality).
TEST(ParserSection6, Sec6_11_1_TypeRefCaseNeq) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) !== type(real)) $display(\"not exact\");\n"
              "  end\n"
              "endmodule\n"));
}

// 13. type() used in case statement as matching expression.
TEST(ParserSection6, Sec6_11_1_TypeRefInCaseExpr) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    case (type(T))\n"
              "      type(int) : $display(\"int\");\n"
              "      type(real) : $display(\"real\");\n"
              "      default : $display(\"other\");\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

// 14. type() on logic data type produces kTypeRef expression.
TEST(ParserSection6, Sec6_11_1_TypeRefOnLogic) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(logic);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTypeRef);
}

// 15. type() on bit data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnBit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(bit);\n"
              "endmodule\n"));
}

// 16. type() on byte data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnByte) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(byte);\n"
              "endmodule\n"));
}

// 17. type() on shortint data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnShortint) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(shortint);\n"
              "endmodule\n"));
}

// 18. type() on longint data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnLongint) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(longint);\n"
              "endmodule\n"));
}

// 19. type() on real data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnReal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(real);\n"
              "endmodule\n"));
}

// 20. type() on string data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnString) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(string);\n"
              "endmodule\n"));
}

// 21. type() with packed array dimension: type(logic [15:0]).
TEST(ParserSection6, Sec6_11_1_TypeRefPackedArray) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(logic [15:0]);\n"
              "endmodule\n"));
}

// 22. var type(expr) with ternary expression.
TEST(ParserSection6, Sec6_11_1_VarTypeRefTernary) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  real b;\n"
      "  var type(1 ? a : b) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c_item = FindItemByName(r, "c");
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto* ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kTernary);
}

// 23. type() used in case pattern with logic packed dimension.
TEST(ParserSection6, Sec6_11_1_TypeRefCaseLogicPacked) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [11:0]))\n"
              "  ();\n"
              "  initial begin\n"
              "    case (type(T))\n"
              "      type(logic [11:0]) : $display(\"12-bit\");\n"
              "      default : $stop;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

// 24. Multiple var type() declarations in one module.
TEST(ParserSection6, Sec6_11_1_MultipleVarTypeRefDecls) {
  auto r = Parse(
      "module t;\n"
      "  int x;\n"
      "  real y;\n"
      "  var type(x) a;\n"
      "  var type(y) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  int type_ref_count = 0;
  for (auto* item : items) {
    if (item->data_type.type_ref_expr != nullptr) {
      ++type_ref_count;
    }
  }
  EXPECT_EQ(type_ref_count, 2);
}

// 25. type() on integer literal expression in expression context.
TEST(ParserSection6, Sec6_11_1_TypeRefOnLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTypeRef);
  // The inner expression is the literal 42, stored in lhs.
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kIntegerLiteral);
}

// 26. var type(concatenation) declaration.
TEST(ParserSection6, Sec6_11_1_VarTypeRefConcat) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  var type({a, b}) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c_item = FindItemByName(r, "c");
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto* ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kConcatenation);
}

// 27. type() on shortreal data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnShortreal) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(shortreal);\n"
              "endmodule\n"));
}

// 28. type() in parameter type default with type(int).
TEST(ParserSection6, Sec6_11_1_ParamTypeDefaultInt) {
  auto r = Parse(
      "module t #(parameter type T = type(int));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 29. var type() where inner is member access expression.
TEST(ParserSection6, Sec6_11_1_VarTypeRefMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  var type(pkg.field) x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(item->data_type.type_ref_expr, nullptr);
}

// 30. type() on time data type.
TEST(ParserSection6, Sec6_11_1_TypeRefOnTime) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = type(time);\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 6.7.1 -- Net declarations with built-in net types
// =============================================================================
// 1. wire logic [7:0] w; — explicit data type after net keyword, no errors.
TEST(ParserSection6, Sec6_7_1_WireExplicitLogicNoErrors) {
  auto r = Parse(
      "module t;\n"
      "  wire logic [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

}  // namespace

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult6i Parse(const std::string &src) {
  ParseResult6i result;
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

static ModuleItem *FirstItem(ParseResult6i &r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

static Stmt *FirstInitialStmt(ParseResult6i &r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock && item->body != nullptr)
      return item->body;
  }
  return nullptr;
}

// =============================================================================
// LRM section 6.11.1 -- Type operator
// =============================================================================

// 1. type(expr) used as expression produces kTypeRef node.
TEST(ParserSection6, Sec6_11_1_TypeRefExprKind) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
}

// 2. type(expr) inner expression is stored in lhs for identifiers.
TEST(ParserSection6, Sec6_11_1_TypeRefInnerIdent) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "y");
}

// 3. type(data_type) stores the data type name in text field.
TEST(ParserSection6, Sec6_11_1_TypeRefDataTypeText) {
  auto r = Parse(
      "module t;\n"
      "  initial x = type(int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTypeRef);
}

// 4. var type(expr) declaration produces kVarDecl with type_ref_expr.
TEST(ParserSection6, Sec6_11_1_VarTypeRefDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(items[1]->data_type.type_ref_expr, nullptr);
  EXPECT_EQ(items[1]->name, "b");
}

// 5. var type(expr) stores the reference expression as an identifier.
TEST(ParserSection6, Sec6_11_1_VarTypeRefExprIdent) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  var type(x) y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  auto *ref = items[1]->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ref->text, "x");
}

// 6. var type(binary_expr) stores a binary expression reference.
TEST(ParserSection6, Sec6_11_1_VarTypeRefBinaryExpr) {
  auto r = Parse(
      "module t;\n"
      "  real a, b;\n"
      "  var type(a + b) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  // a, b are separate VarDecl items, c is the type(a+b) item.
  ModuleItem *c_item = nullptr;
  for (auto *item : items) {
    if (item->name == "c") {
      c_item = item;
      break;
    }
  }
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto *ref = c_item->data_type.type_ref_expr;
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(ref->kind, ExprKind::kBinary);
}

// 7. type() used in parameter type default: parameter type T = type(logic).
TEST(ParserSection6, Sec6_11_1_TypeRefParamDefault) {
  auto r = Parse(
      "module t #(parameter type T = type(logic));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 8. type() used in parameter default with packed dimension.
TEST(ParserSection6, Sec6_11_1_TypeRefParamPackedDim) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = type(logic [7:0]));\n"
              "endmodule\n"));
}

// 9. type() comparison with == in expression context.
TEST(ParserSection6, Sec6_11_1_TypeRefEqComparison) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) == type(int)) $display(\"match\");\n"
              "  end\n"
              "endmodule\n"));
}

// 10. type() comparison with != in expression context.
TEST(ParserSection6, Sec6_11_1_TypeRefNeqComparison) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) != type(real)) $display(\"differ\");\n"
              "  end\n"
              "endmodule\n"));
}

// 11. type() comparison with === (case equality).
TEST(ParserSection6, Sec6_11_1_TypeRefCaseEq) {
  EXPECT_TRUE(
      ParseOk("module t #(parameter type T = int)\n"
              "  ();\n"
              "  initial begin\n"
              "    if (type(T) === type(int)) $display(\"exact\");\n"
              "  end\n"
              "endmodule\n"));
}

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
  auto *stmt = FirstInitialStmt(r);
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
  ModuleItem *c_item = nullptr;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->name == "c") {
      c_item = item;
      break;
    }
  }
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto *ref = c_item->data_type.type_ref_expr;
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
  auto &items = r.cu->modules[0]->items;
  int type_ref_count = 0;
  for (auto *item : items) {
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
  auto *stmt = FirstInitialStmt(r);
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
  ModuleItem *c_item = nullptr;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->name == "c") {
      c_item = item;
      break;
    }
  }
  ASSERT_NE(c_item, nullptr);
  EXPECT_EQ(c_item->kind, ModuleItemKind::kVarDecl);
  auto *ref = c_item->data_type.type_ref_expr;
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
  auto *item = FirstItem(r);
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

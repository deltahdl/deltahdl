// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult6b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static Stmt* FirstInitialStmt(ParseResult6b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

namespace {

// §20.6 — Bare type keyword in expression context ($typename(logic))
TEST(ParserSection6, BareTypeKeywordInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial $display($typename(logic));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// §6.3.2.2: Drive strength on net declaration with inline assignment.
TEST(ParserSection6, NetDeclDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  // 2=weak, 4=strong (parser encoding)
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

// =========================================================================
// §6.6.8: Void data type (additional tests)
// =========================================================================
TEST(ParserSection6, VoidCastExpression) {
  auto r = Parse(
      "module t;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection6, VoidFunctionInClass) {
  auto r = Parse(
      "class C;\n"
      "  function void setup();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection6, VoidTaskReturnType) {
  // Tasks implicitly return void; verify parse is correct.
  auto r = Parse(
      "module t;\n"
      "  task do_nothing();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
}

// =========================================================================
// §6.20.3: Type parameters (additional tests)
// =========================================================================
TEST(ParserSection6, TypeParameterWithMultipleParams) {
  EXPECT_TRUE(
      ParseOk6("module m #(parameter type T = int, parameter type U = real)\n"
               "  ();\n"
               "  T x;\n"
               "  U y;\n"
               "endmodule\n"));
}

TEST(ParserSection6, TypeParameterDefaultShortint) {
  EXPECT_TRUE(
      ParseOk6("module ma #(parameter p1 = 1, parameter type p2 = shortint)\n"
               "  (input logic [p1:0] i, output logic [p1:0] o);\n"
               "  p2 j = 0;\n"
               "endmodule\n"));
}

// =========================================================================
// §6.21: Scope and lifetime (additional tests)
// =========================================================================
TEST(ParserSection6, AutomaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task automatic my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection6, StaticTaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task static my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserSection6, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

// =========================================================================
// §6.22.1 -- Matching types
// =========================================================================
TEST(ParserSection6, MatchingTypesBuiltinTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  node n1;\n"
      "  bit n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(ParserSection6, MatchingTypesNamedTypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  AB_t x1;\n"
      "  AB_t x2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSignedBitVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  BYTE b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  MEM_BYTES mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

// =========================================================================
// §6.22: Type compatibility — additional tests
// =========================================================================
TEST(ParserSection6, TypesMatchNamedSame) {
  // Two named types with the same name should match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferent) {
  // Two named types with different names should not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentSameKind) {
  // §6.22.2: Same kind, same signedness, same state-ness -> equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

}  // namespace

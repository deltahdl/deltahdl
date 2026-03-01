// §6.16: String data type

#include "fixture_parser.h"

using namespace delta;

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserA212, VarDataTypeString) {
  // var_data_type: data_type (non_integer_type)
  auto r = Parse("module m(input string name); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// string
TEST(ParserA221, DataTypeString) {
  auto r = Parse("module m; string s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kString);
}

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =========================================================================
// §6.16: String in block scope
// =========================================================================
TEST(ParserSection6, StringBlockDecl) {
  // §6.16: string declared inside an initial block.
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string msg;\n"
      "    msg = \"test\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringFunctionArg) {
  // §6.16: string as a function argument type.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function void print_msg(string s);\n"
              "  endfunction\n"
              "endmodule\n"));
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

// 23. String variable declaration.
TEST(ParserSection6, Sec6_5_StringVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  string msg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "msg");
}

TEST(ParserCh509, StringLiteral_AsParameter) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter string MSG = \"default message\";\n"
              "endmodule"));
}

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

// Step 1a: string type in block-level declarations (fixes 6.19.5.6)
TEST(ParserSection6, BlockVarDecl_StringType) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string s;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
  EXPECT_EQ(stmt->var_name, "s");
}

}  // namespace

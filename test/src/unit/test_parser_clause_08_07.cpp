// §8.7: Constructors

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

TEST(ParserA602, BlockingAssignment_ClassNew) {
  // class_new: obj = new;
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA602, BlockingAssignment_ClassNewWithArgs) {
  // class_new with arguments: obj = new(arg1, arg2)
  auto r = Parse(
      "module m;\n"
      "  initial begin obj = new(1, 2); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// §8.7 — Constructor (function new)
TEST(ParserSection8, ClassConstructor) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new();\n"
      "    data = 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->name, "new");
}

// §8.7 — Constructor with parameters
TEST(ParserSection8, ClassConstructorWithParams) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new(int val);\n"
      "    data = val;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §8.4 — Class instantiation with 'new' expression
TEST(ParserSection8, NewExpression) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "  endclass\n"
      "  test_cls obj;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace

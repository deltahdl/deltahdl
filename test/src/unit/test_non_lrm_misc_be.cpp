// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult4e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4e Parse(const std::string& src) {
  ParseResult4e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ClassMember* FindClassMethod(ParseResult4e& r) {
  if (r.cu->classes.empty()) return nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod) return m;
  }
  return nullptr;
}

namespace {

// =============================================================================
// 24. Static var in class method
// =============================================================================
TEST(ParserSection4, Sec4_9_4_StaticVarInClassMethod) {
  auto r = Parse(
      "class Counter;\n"
      "  function int next();\n"
      "    static int id = 0;\n"
      "    id = id + 1;\n"
      "    return id;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Counter");
  auto* method_member = FindClassMethod(r);
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_static);
}

// =============================================================================
// 25. Automatic var in class method
// =============================================================================
TEST(ParserSection4, Sec4_9_4_AutoVarInClassMethod) {
  auto r = Parse(
      "class Worker;\n"
      "  task run();\n"
      "    automatic int local_data = 42;\n"
      "    $display(local_data);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* method_member = FindClassMethod(r);
  ASSERT_NE(method_member, nullptr);
  ASSERT_NE(method_member->method, nullptr);
  ASSERT_GE(method_member->method->func_body_stmts.size(), 1u);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->kind,
            StmtKind::kVarDecl);
  EXPECT_TRUE(method_member->method->func_body_stmts[0]->var_is_automatic);
  EXPECT_EQ(method_member->method->func_body_stmts[0]->var_name, "local_data");
}

}  // namespace

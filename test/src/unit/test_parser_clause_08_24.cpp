// §8.24: Out-of-block declarations

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// method_prototype ::= task_prototype | function_prototype
TEST(SourceText, ClassMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function int get_val();\n"
      "  extern task do_work();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->method->name, "get_val");
  EXPECT_EQ(members[1]->method->name, "do_work");
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ---------------------------------------------------------------------------
// function_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// task_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------
TEST(ParserA27, TaskBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern task my_task(input int x);\n"
      "endclass\n"
      "task C::my_task(input int x);\n"
      "  $display(\"x=%0d\", x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskBodyOutOfBlockMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace

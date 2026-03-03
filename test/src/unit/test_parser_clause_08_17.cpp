// §8.17: Chaining constructors

#include "fixture_parser.h"

using namespace delta;

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

namespace {

// §8.13 — Extends with constructor arguments
TEST(ParserSection8, ExtendsWithArgs) {
  auto r = Parse(
      "class Base;\n"
      "endclass\n"
      "class Child extends Base(1, 2);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->base_class, "Base");
}

// §8.13 — Super.new() call
TEST(ParserSection8, ConstructorSuperNew) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

// §8.15 — super.new() expression
TEST(ParserSection8, SuperNewExpression) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

// §8.17 — Chaining constructors with super.new() and default
TEST(ParserSection8, ConstructorChainingDefault) {
  auto r = Parse(
      "class Base;\n"
      "  function new(int x = 0);\n"
      "  endfunction\n"
      "endclass\n"
      "class Child extends Base;\n"
      "  function new();\n"
      "    super.new(5);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

}  // namespace

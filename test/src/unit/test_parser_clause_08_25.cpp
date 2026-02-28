// §8.25: Parameterized classes

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

// §8.5 — Parameterized classes
TEST(ParserSection8, ParameterizedClass) {
  auto r = Parse(
      "class stack #(parameter int DEPTH = 8);\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "stack");
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassMultipleParams) {
  auto r = Parse(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 2u);
  EXPECT_EQ(cls->params[0].first, "WIDTH");
  EXPECT_EQ(cls->params[1].first, "DEPTH");
}

TEST(ParserSection8, ParameterizedClassTypeParam) {
  auto r = Parse(
      "class container #(type T = int);\n"
      "  T data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "T");
}

// §8.5 — Parameterized class with extends
TEST(ParserSection8, ParameterizedClassExtendsName) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  EXPECT_EQ(cls->name, "Derived");
  EXPECT_EQ(cls->base_class, "Base");
}

TEST(ParserSection8, ParameterizedClassExtendsParams) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* cls = r.cu->classes[1];
  ASSERT_EQ(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "N");
}

}  // namespace

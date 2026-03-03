// §8.13: Inheritance and subclasses

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

// §8.15 — Extends with scoped class name
TEST(ParserSection8, ExtendsScopedName) {
  auto r = Parse(
      "class Child extends pkg::Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);

  EXPECT_EQ(r.cu->classes[0]->name, "Child");
}

TEST(Parser, ClassExtends) {
  auto r = Parse("class child extends parent; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "child");
  EXPECT_EQ(cls->base_class, "parent");
}

// Class with extends.
TEST(SourceText, ClassWithExtends) {
  auto r = Parse("class Child extends Parent; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Parent");
}

// =============================================================================
// A.1.2 class_declaration — additional forms
// =============================================================================
// Class with final_specifier: class :final C;
TEST(SourceText, ClassWithFinal) {
  auto r = Parse("class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(ParserSection8, ClassExtendsBase) {
  auto r = Parse(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "Base");
  EXPECT_TRUE(r.cu->classes[0]->base_class.empty());
}

}  // namespace

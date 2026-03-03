// §8.3: Syntax

#include "fixture_parser.h"

using namespace delta;

namespace {

// description: class_declaration
TEST(SourceText, DescriptionClass) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// class_item ::= { attribute_instance } covergroup_declaration
TEST(SourceText, ClassCovergroupDecl) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kCovergroup);
  EXPECT_EQ(members[0]->name, "cg");
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

// §8.3 — Lifetime specifier on class
TEST(ParserSection8, ClassWithLifetime) {
  auto r = Parse(
      "class automatic MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
}

// §8.5 — Parameter inside class body
TEST(ParserSection8, ClassWithParameter) {
  auto r = Parse(
      "class par_cls;\n"
      "  parameter int b = 23;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "par_cls");
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection23, EndLabelClass) {
  auto r = Parse("class myclass; endclass : myclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "myclass");
}

// --- Class tests ---
TEST(Parser, EmptyClass) {
  auto r = Parse("class empty_cls; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "empty_cls");
  EXPECT_FALSE(r.cu->classes[0]->is_virtual);
}

// §8.15 — Constructor end label
TEST(ParserSection8, ConstructorEndLabel) {
  auto r = Parse(
      "class Base;\n"
      "  function new();\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// class_item ::= local_parameter_declaration ; | parameter_declaration ;
TEST(SourceText, ClassParameters) {
  auto r = Parse(
      "class C;\n"
      "  localparam int LP = 10;\n"
      "  parameter int P = 20;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kProperty);
}

// class_item ::= ; (empty statement)
TEST(SourceText, ClassEmptyItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  // Empty semicolons are consumed, only real members remain.
  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u);
}

// §8.3 — Multiple properties on one line (comma-separated)
TEST(ParserSection8, MultiplePropertiesCommaSeparated) {
  auto r = Parse(
      "class MyClass;\n"
      "  int a, b, c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 3u);
  const std::string kExpectedNames[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

}  // namespace

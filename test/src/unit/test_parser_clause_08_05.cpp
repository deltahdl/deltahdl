// §8.5: Object properties and object parameter data

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// These unit tests embed SystemVerilog source as inline C++ string literals
// rather than loading external .sv files. This is intentional: each test is
// fully self-contained with the input source and structural assertions in one
// place, so a reader can understand what is being tested without
// cross-referencing a second file. When a test fails, the input and expected
// AST shape are visible together in the test output. Integration and
// conformance testing uses external .sv files instead: the CHIPS Alliance
// sv-tests suite validates broad language coverage, and the sim-tests under
// test/src/e2e/ verify end-to-end simulation behavior against .expected output
// files. This inline pattern is standard practice for compiler parser unit
// tests (used by LLVM, Clang, rustc, etc.).
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

struct StructMemberExpected {
  const char *name;
  DataTypeKind type_kind;
};

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

namespace {

TEST(Parser, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto *cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// A.1.9 Class items
// =============================================================================
// class_item ::= { attribute_instance } class_property (property_qualifier
// path)
TEST(SourceText, ClassPropertyWithQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  randc bit [3:0] y;\n"
      "  static int count;\n"
      "  protected int secret;\n"
      "  local int hidden;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand);
  EXPECT_EQ(members[0]->name, "x");
  EXPECT_TRUE(members[1]->is_randc);
  EXPECT_EQ(members[1]->name, "y");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_local);
}

// class_item_qualifier / property_qualifier / method_qualifier (footnote 10)
TEST(SourceText, ClassQualifierCombinations) {
  auto r = Parse(
      "class C;\n"
      "  static local int a;\n"
      "  protected rand int b;\n"
      "  static virtual function void sv_fn(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_TRUE(members[0]->is_static);
  EXPECT_TRUE(members[0]->is_local);
  EXPECT_TRUE(members[1]->is_protected);
  EXPECT_TRUE(members[1]->is_rand);
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[2]->is_virtual);
}

struct ParseResult313 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string &src) {
  ParseResult313 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem *> &items,
                                 ModuleItemKind kind, const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem *> &items,
                         const std::string &name) {
  for (const auto *item : items)
    for (const auto &attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

// 12. Class scope -- members in class name space
TEST(ParserClause03, Cl3_13_ClassScopeMembers) {
  auto r = Parse(
      "class my_cls;\n"
      "  int data;\n"
      "  string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto *cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "my_cls");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[1]->name, "name");
}

}  // namespace

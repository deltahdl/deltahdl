// §6.19: Enumerations

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
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static void VerifyEnumMemberNames(const std::vector<EnumMember> &members,
                                  const std::string expected[], size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
  }
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

TEST(Parser, TypedefEnum) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { A, B, C } state_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "state_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  std::string expected[] = {"A", "B", "C"};
  VerifyEnumMemberNames(item->typedef_type.enum_members, expected,
                        std::size(expected));
}

TEST(Parser, EnumWithValues) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { IDLE=0, RUN=1, STOP=2 } cmd_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  std::string expected[] = {"IDLE", "RUN", "STOP"};
  ASSERT_EQ(members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
    EXPECT_NE(members[i].value, nullptr) << "member " << i;
  }
}

TEST(Parser, InlineEnumVar) {
  auto r = Parse(
      "module t;\n"
      "  enum { X, Y } my_var;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "my_var");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(item->data_type.enum_members.size(), 2);
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

// 23. Enum in module scope
TEST(ParserClause03, Cl3_13_EnumInModuleScope) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
      "  state_t current_state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  bool found_typedef = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      found_typedef = true;
      EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
    }
  }
  EXPECT_TRUE(found_typedef);
}

// enum [enum_base_type] { ... } {packed_dimension}
TEST(ParserA221, DataTypeEnum) {
  auto r = Parse("module m; enum logic [1:0] {A, B, C} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

TEST(ParserA221, EnumBaseVectorWithDim) {
  auto r = Parse("module m; enum logic [7:0] {A=0, B=255} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->items[0]->data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, EnumBaseTypeIdentifier) {
  // enum type_identifier { ... }
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "  enum nibble_t {A, B} x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace

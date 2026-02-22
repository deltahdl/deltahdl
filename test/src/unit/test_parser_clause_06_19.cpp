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

}  // namespace

// §23.2: Module definitions

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
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static void VerifyEnumMemberNames(const std::vector<EnumMember>& members,
                                  const std::string expected[], size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
  }
}

struct StructMemberExpected {
  const char* name;
  DataTypeKind type_kind;
};

static void VerifyStructMembers(const std::vector<StructMember>& members,
                                const StructMemberExpected expected[],
                                size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected[i].name) << "member " << i;
    EXPECT_EQ(members[i].type_kind, expected[i].type_kind) << "member " << i;
  }
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static void VerifyGenerateCaseItem(const GenerateCaseItem& ci, size_t idx,
                                   bool expect_default,
                                   size_t expect_pattern_count) {
  EXPECT_EQ(ci.is_default, expect_default) << "case item " << idx;
  EXPECT_EQ(ci.patterns.size(), expect_pattern_count) << "case item " << idx;
  EXPECT_FALSE(ci.body.empty()) << "case item " << idx;
}

struct ModportPortExpected {
  Direction dir;
  const char* name;
};

static void VerifyModportPorts(const std::vector<ModportPort>& ports,
                               const ModportPortExpected expected[],
                               size_t count) {
  ASSERT_EQ(ports.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(ports[i].name, expected[i].name) << "port " << i;
  }
}

namespace {

TEST(Parser, EmptyModule) {
  auto r = Parse("module empty; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(Parser, MultipleModules) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

}  // namespace

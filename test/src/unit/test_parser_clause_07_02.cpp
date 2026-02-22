// §7.2: Structures

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include <gtest/gtest.h>

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

struct StructMemberExpected {
  const char *name;
  DataTypeKind type_kind;
};

static void VerifyStructMembers(const std::vector<StructMember> &members,
                                const StructMemberExpected expected[],
                                size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected[i].name) << "member " << i;
    EXPECT_EQ(members[i].type_kind, expected[i].type_kind) << "member " << i;
  }
}

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

namespace {

TEST(Parser, TypedefStruct) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    logic [7:0] a;\n"
                 "    int b;\n"
                 "  } my_struct_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_struct_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  StructMemberExpected expected[] = {
      {"a", DataTypeKind::kLogic},
      {"b", DataTypeKind::kInt},
  };
  VerifyStructMembers(item->typedef_type.struct_members, expected,
                      std::size(expected));
}

TEST(Parser, TypedefStructPacked) {
  auto r = Parse("module t;\n"
                 "  typedef struct packed {\n"
                 "    logic [3:0] hi;\n"
                 "    logic [3:0] lo;\n"
                 "  } byte_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

TEST(Parser, InlineStructVar) {
  auto r = Parse("module t;\n"
                 "  struct { int x; int y; } point;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "point");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  ASSERT_EQ(item->data_type.struct_members.size(), 2);
}

} // namespace

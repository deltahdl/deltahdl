// §9.4.2: Event control

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

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

namespace {

TEST(Parser, EventWaitWithParens) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "  initial @(ev) ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[1];
  auto *stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

TEST(Parser, EventWaitBareIdentifier) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "  initial @ev ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[1];
  auto *stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

} // namespace

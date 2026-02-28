// §23.5: Extern modules

#include "fixture_parser.h"

using namespace delta;

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

namespace {

// --- Extern module declarations (LRM §23.2.1) ---
TEST(ParserSection23, ExternModuleHeader) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

// Verify a 2-port module has expected names and directions.
static void VerifyTwoPortModule(ParseResult& r, const char* n0, Direction d0,
                                const char* n1, Direction d1) {
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, n0);
  EXPECT_EQ(mod->ports[0].direction, d0);
  EXPECT_EQ(mod->ports[1].name, n1);
  EXPECT_EQ(mod->ports[1].direction, d1);
}

TEST(ParserSection23, ExternModulePorts) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

}  // namespace

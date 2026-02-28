// §23.2.2.1: Non-ANSI style port declarations

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfInterfaceIdentifiersMultiple) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
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

// --- Non-ANSI port declarations (LRM §23.2.2.1) ---
TEST(ParserSection23, NonAnsiPortsBasic) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

}  // namespace

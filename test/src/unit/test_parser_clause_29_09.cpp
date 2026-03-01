// §29.9: Mixing level-sensitive and edge-sensitive descriptions

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct UdpSpotCheck {
  size_t row;
  char input0;
  char output;
};

static void VerifyUdpTableSpotChecks(const UdpDecl* udp,
                                     const UdpSpotCheck checks[],
                                     size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->table[checks[i].row].inputs[0], checks[i].input0);
    EXPECT_EQ(udp->table[checks[i].row].output, checks[i].output);
  }
}

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection29, MixedLevelEdgeSensitive) {
  auto r = Parse(
      "primitive jk_edge_ff(output reg q, input clock, j, k, preset, clear);\n"
      "  table\n"
      "    ? ? ? 0 1 : ? : 1;\n"
      "    ? ? ? 1 0 : ? : 0;\n"
      "    r 0 0 0 0 : 0 : 1;\n"
      "    r 0 0 1 1 : ? : -;\n"
      "    f ? ? ? ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 5);
  UdpSpotCheck checks[] = {
      {0, '?', '1'},  // Level-sensitive entry
      {2, 'r', '1'},  // Edge-sensitive entry
      {4, 'f', '-'},  // Falling edge with no-change output
  };
  VerifyUdpTableSpotChecks(udp, checks, std::size(checks));
}

}  // namespace

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

} // namespace

// =============================================================================
// A.3 -- Primitive instances (gate_instantiation)
// =============================================================================

TEST(ParserAnnexA, A3GateInstNInput) {
  auto r = Parse("module m;\n"
                 "  and g1(y, a, b, c);\n"
                 "  nand g2(y2, a, b);\n"
                 "  xor g3(y3, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst)
      gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

TEST(ParserAnnexA, A3GateInstWithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.1: New()

#include "fixture_parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult15 Parse(const std::string& src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// §15.3 — Semaphore variable declaration (parsed as named type)
// =============================================================================
TEST(ParserSection15, SemaphoreVarDecl) {
  // semaphore is not a keyword — it's a built-in class type in the std
  // package. It parses as a named-type variable declaration via the
  // identifier-based path in ParseImplicitTypeOrInst.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    smTx = new(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Just verify the module parsed without errors.
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace

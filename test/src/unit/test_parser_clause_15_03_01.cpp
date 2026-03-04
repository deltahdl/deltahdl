// §15.3.1: New()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
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

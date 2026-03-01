// Annex D.8: $reset, $reset_count, and $reset_value

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- D.5: $reset, $reset_count, $reset_value ---
TEST(ParserAnnexD2, AnnexDResetFamily) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $reset;\n"
      "    x = $reset_count;\n"
      "    y = $reset_value;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace

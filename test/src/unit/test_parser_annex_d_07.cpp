// Annex D.7: $log and $nolog

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD, AnnexDLog) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $log(\"sim.log\"); $nolog; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace

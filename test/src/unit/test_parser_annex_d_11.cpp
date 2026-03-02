// Annex D.11: $scope

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD, AnnexDScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $scope(m); $showscopes; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace

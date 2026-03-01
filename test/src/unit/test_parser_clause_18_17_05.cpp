// §18.17.5: Interleaving productions—rand join

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// rand join production list
TEST(ParserA612, RsProductionListRandJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join a b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace

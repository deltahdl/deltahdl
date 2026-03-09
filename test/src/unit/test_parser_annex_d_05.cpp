#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD2, AnnexDKeyNokey) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $key(\"keylog.txt\");\n"
      "    $nokey;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace

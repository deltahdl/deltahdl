// §19.4.1: Embedded covergroup inheritance

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

TEST(ParserA211, CovergroupDecl_WithExtends) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup child extends parent;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace

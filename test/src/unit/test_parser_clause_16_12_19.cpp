#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyPortItem_LocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input int x);\n"
              "    x > 0;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace

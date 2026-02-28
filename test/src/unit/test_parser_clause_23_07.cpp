// §23.7: Member selects and hierarchical names

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_ChainedAccess) {
  // Chained member accesses: a.b.c().
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = obj.sub.method();\n"
              "endmodule"));
}

}  // namespace

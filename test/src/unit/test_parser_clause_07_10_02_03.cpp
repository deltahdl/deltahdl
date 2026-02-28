// §7.10.2.3: Delete()

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_Delete) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.delete();\n"
              "endmodule"));
}

}  // namespace

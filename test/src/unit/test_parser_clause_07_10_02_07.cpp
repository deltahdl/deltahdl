// §7.10.2.7: Push_back()

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_PushBack) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q.push_back(42);\n"
              "endmodule"));
}

}  // namespace

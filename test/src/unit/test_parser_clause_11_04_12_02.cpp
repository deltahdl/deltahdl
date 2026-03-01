// §11.4.12.2: String concatenation and replication

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =========================================================================
// Section 11.4.12.2 -- Replication (string concatenation and replication)
// =========================================================================
TEST(ParserSection11, StringConcatenation) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  string hello, s;\n"
              "  initial begin\n"
              "    hello = \"hello\";\n"
              "    s = {hello, \" \", \"world\"};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection11, StringReplication) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    int n;\n"
              "    string s;\n"
              "    n = 3;\n"
              "    s = {n{\"boo \"}};\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace

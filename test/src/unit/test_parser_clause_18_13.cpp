#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection18, GetSetRandstateRoundtrip) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void save_and_restore();\n"
      "    string s;\n"
      "    s = this.get_randstate();\n"
      "    this.randomize();\n"
      "    this.set_randstate(s);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace

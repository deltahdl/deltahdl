#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection18, GetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function string save_state();\n"
      "    return this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, GetRandstateAssignToVar) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string state;\n"
      "    p = process::self();\n"
      "    state = p.get_randstate();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, GetRandstateInFunction) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void checkpoint(output string s);\n"
      "    s = this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace

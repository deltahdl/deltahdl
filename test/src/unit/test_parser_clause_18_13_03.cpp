#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ConstrainedRandomParsing, SrandomMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it();\n"
      "    this.srandom(42);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstrainedRandomParsing, SrandomInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.srandom(123);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ConstrainedRandomParsing, SrandomWithExpression) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it(int seed_val);\n"
      "    this.srandom(seed_val + 1);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace

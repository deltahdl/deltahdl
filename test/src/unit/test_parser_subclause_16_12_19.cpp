#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12.19: it shall be illegal to declare a local variable formal argument
// of a named property with direction `inout`. (Note that §16.8.2 permits this
// for sequences; properties carve it out.)
TEST(PropertyLocalLvarArgumentParsing, LocalInoutInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local inout logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.19: it shall be illegal to declare a local variable formal argument
// of a named property with direction `output`.
TEST(PropertyLocalLvarArgumentParsing, LocalOutputInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local output bit a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.19: a local variable formal argument whose direction `input` is
// specified explicitly is legal and must parse without diagnostic.
TEST(PropertyLocalLvarArgumentParsing, ExplicitInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

// §16.12.19: a local variable formal argument shall have direction `input`
// either specified explicitly or inferred. With `local` and no direction
// keyword, the inferred direction is `input`, so the declaration is legal.
TEST(PropertyLocalLvarArgumentParsing, InferredInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

// §16.12.19: the direction restriction applies to every local variable formal
// argument, not just the first. A legal `local input` formal followed by a
// `local inout` formal is still illegal because of the second formal.
TEST(PropertyLocalLvarArgumentParsing, InoutOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local inout int b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.19: likewise, a `local output` formal in a non-first position is
// illegal even when a valid `local input` formal precedes it.
TEST(PropertyLocalLvarArgumentParsing, OutputOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local output bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.12.19: multiple local variable formal arguments all of direction
// `input` (explicit or inferred) are legal; every formal name is harvested.
TEST(PropertyLocalLvarArgumentParsing, MultipleInputLocalsParse) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
}

}  // namespace

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BindDirective, CuScopeBindGoesToBindDirectives) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "bind target binder b1();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->bind_directives.empty());
}

TEST(BindDirective, BindDirectiveInModule) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "module m;\n"
      "  bind target checker_m inst(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BindDirective, BindDirectiveInInterface) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "interface ifc;\n"
      "  bind target checker_m inst(.*);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Second bind_directive alternative: a bind_target_instance directly precedes
// the bind_instantiation, with no bind_target_instance_list. The directive is
// recorded with a hierarchical target and an empty instance list.
TEST(BindDirective, SecondFormBindsHierarchicalInstanceTarget) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind top.c1 probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.c1");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
}

// bind_target_instance_list production: the colon-introduced list collects each
// comma-separated bind_target_instance into the directive.
TEST(BindDirective, FirstFormParsesTargetInstanceList) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "bind cpu : top.c1, top.c3 probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "cpu");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "top.c1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "top.c3");
}

// A bind_target_instance carries a constant_bit_select, used to single out one
// element of an instance array. The parser records the select expression
// alongside the hierarchical name it qualifies.
TEST(BindDirective, TargetInstanceCarriesConstantBitSelect) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "bind cpu : top.c[0] probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "top.c");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instance_bit_selects.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->target_instance_bit_selects[0], nullptr);
}

}  // namespace

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

// The same bind_target_instance production also governs the second form's own
// target: a hierarchical_identifier followed by a constant_bit_select. Here the
// select rides on the directive target itself (not a list entry), so the parser
// records it in target_bit_select while the instance list stays empty.
TEST(BindDirective, SecondFormTargetCarriesConstantBitSelect) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind top.c[1] probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.c");
  EXPECT_NE(r.cu->bind_directives[0]->target_bit_select, nullptr);
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
}

// §23.11 states the bind_instantiation admits the full range of instantiation
// syntax, so parameter associations may ride on it. Named form: the override is
// recorded on the instantiation's inst_params keyed by parameter name.
TEST(BindDirective, BindInstantiationCarriesNamedParameterOverride) {
  auto r = Parse(
      "module cpu; endmodule\n"
      "module m; endmodule\n"
      "bind cpu m #(.P(4)) i(.*);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto* inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "P");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

// Companion positional form of a bind_instantiation parameter association: the
// override has no parameter name and travels by position, a distinct parser
// path from the named form above.
TEST(BindDirective, BindInstantiationCarriesPositionalParameterOverride) {
  auto r = Parse(
      "module cpu; endmodule\n"
      "module m; endmodule\n"
      "bind cpu m #(4) i();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto* inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->inst_params.size(), 1u);
  EXPECT_TRUE(inst->inst_params[0].first.empty());
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

}  // namespace

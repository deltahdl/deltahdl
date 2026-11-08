#include <gtest/gtest.h>

#include "fixture_parser.h"

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

TEST(BindDirective, SecondFormBindsHierarchicalInstanceTarget) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind top.c1 probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "top.c1");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
}

TEST(BindDirective, FirstFormParsesTargetInstanceList) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "bind cpu : top.c1, top.c3 probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "cpu");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0].path, "top.c1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1].path, "top.c3");
}

TEST(BindDirective, TargetInstanceCarriesConstantBitSelect) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "bind cpu : top.c[0] probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0].path, "top.c");
  const auto& segments = r.cu->bind_directives[0]->target_instances[0].segments;
  ASSERT_EQ(segments.size(), 2u);
  EXPECT_TRUE(segments[0].selects.empty());
  ASSERT_EQ(segments[1].selects.size(), 1u);
  EXPECT_NE(segments[1].selects[0], nullptr);
}

TEST(BindDirective, SecondFormTargetCarriesConstantBitSelect) {
  auto r = Parse(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind top.c[1] probe p();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "top.c");
  const auto& segments = r.cu->bind_directives[0]->target.segments;
  ASSERT_EQ(segments.size(), 2u);
  ASSERT_EQ(segments[1].selects.size(), 1u);
  EXPECT_NE(segments[1].selects[0], nullptr);
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
}

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

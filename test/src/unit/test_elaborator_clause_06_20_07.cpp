#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DollarConstantElaboration, DollarBodyParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarPortListParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter int P = $);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, BoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

// §6.20.7: assigning a $ parameter to another parameter is legal, and the
// assigned-to parameter is itself unbounded.
TEST(DollarConstantElaboration, DollarParameterAssignedToAnotherIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") EXPECT_TRUE(p.is_unbounded);
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

// The same propagation applies when the chain appears in a parameter port list,
// where a later parameter can depend on an earlier one.
TEST(DollarConstantElaboration, DollarPortListParameterChainIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter Q = $, parameter P = Q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

// A parameter assigned a bounded parameter is not unbounded.
TEST(DollarConstantElaboration, ParameterAssignedBoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = 7;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") EXPECT_FALSE(p.is_unbounded);
  }
}

// §6.20.7: unboundedness propagates transitively along a chain of parameters,
// since each link is marked unbounded as it is elaborated.
TEST(DollarConstantElaboration, DollarParameterChainThreeDeepAllUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = $;\n"
      "  parameter B = A;\n"
      "  parameter C = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int seen = 0;
  for (auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") {
      ++seen;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_EQ(seen, 3);
}

// §6.20.7: $ may be assigned to a value parameter; a localparam is a value
// parameter, so it too becomes unbounded when assigned $.
TEST(DollarConstantElaboration, DollarLocalparamSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.7: $ must be self-contained; combining it with an operator in a
// parameter value is illegal.
TEST(DollarConstantElaboration, NonSelfContainedDollarParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = $ + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The same restriction holds for a parameter declared in a port list.
TEST(DollarConstantElaboration, NonSelfContainedDollarPortParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter int P = $ + 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(DollarConstantElaboration, DollarParameterNotResolved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_resolved);
    }
  }
}

}

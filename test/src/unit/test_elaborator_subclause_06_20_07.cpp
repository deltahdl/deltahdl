#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §6.20.7: $ may be assigned to a value parameter of a simple bit vector type
// (§6.11.1). This drives that dependency's real syntax — an explicitly declared
// packed logic vector — through parse+elaborate and observes the parameter
// being flagged unbounded.
TEST(DollarConstantElaboration, DollarSimpleBitVectorTypeParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter logic [7:0] P = $;\n"
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

// §6.20.7: a parameter assigned $ may be used anywhere a literal $ is allowed.
// This mirrors the clause's own example — the unbounded parameter supplies the
// upper bound of a sequence cycle-delay range — and confirms the parameter is
// flagged unbounded and is accepted in that context without error.
TEST(DollarConstantElaboration, DollarParameterUsableAsUnboundedRangeBound) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter r1 = 1;\n"
      "  parameter r2 = $;\n"
      "  logic clk, a, b, c;\n"
      "  property inq1;\n"
      "    @(posedge clk) a ##[r1:r2] b |=> c;\n"
      "  endproperty\n"
      "  assert property (inq1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_r2 = false;
  for (auto& p : mod->params) {
    if (p.name == "r2") {
      found_r2 = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_r2);
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
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
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
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
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

// §6.20.7: the referenced unbounded constant may itself be a localparam (a
// §11.2.1 constant form) rather than a parameter; assigning it to a later
// parameter propagates unboundedness just as a parameter reference does.
TEST(DollarConstantElaboration,
     DollarLocalparamReferencedByParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            2, "6.20.7"));
}

// The same restriction holds for a parameter declared in a port list.
TEST(DollarConstantElaboration, NonSelfContainedDollarPortParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter int P = $ + 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            1, "6.20.7"));
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

// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// and rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree". Block 'a' is not higher in the module's own branch,
// so the P that block 'a' assigned $ is not what the module-level Q names, and
// the §6.20.7 propagation this file's
// DollarParameterAssignedToAnotherIsUnbounded asserts does not reach it.
//
// The test fails when Q comes out unbounded. Elaborator::RefersToUnboundedParam
// in src/elaborator/elaborator_items_scope.cpp matches RtlirParamDecl::name,
// which Elaborator::ElaborateParamDecl writes bare whatever scope declared the
// parameter, so block 'a''s P answers for a reference anywhere in the module
// unless RtlirParamDecl::gen_block_prefix is consulted beside it.
TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockDoesNotMakeAModuleLevelParameterUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "    end\n"
      "  endgenerate\n"
      "  localparam Q = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q" || !p.gen_block_prefix.empty()) continue;
    found_q = true;
    EXPECT_FALSE(p.is_unbounded)
        << "block 'a' localparam P should not reach a module-level Q";
  }
  EXPECT_TRUE(found_q);
}

// The direction the scope test must not lose. §23.9 rules that an identifier
// "declared locally" is what a direct reference names, so block 'a''s own P is
// what block 'a''s Q names, and §6.20.7's propagation carries the unbounded
// flag across it exactly as this file's
// DollarParameterAssignedToAnotherIsUnbounded has it do at module level.
//
// The test fails when Q comes out bounded, which is what a check that dropped
// every parameter carrying a generate block prefix would produce.
TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockStillReachesThatBlocksParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "      localparam Q = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q") continue;
    found_q = true;
    EXPECT_TRUE(p.is_unbounded)
        << "block 'a' localparam P should reach block 'a' localparam Q";
  }
  EXPECT_TRUE(found_q);
}

}  // namespace

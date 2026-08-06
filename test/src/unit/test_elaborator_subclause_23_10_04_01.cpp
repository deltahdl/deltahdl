#include "fixture_elaborator.h"

using namespace delta;

namespace {

RtlirParamDecl* FindParamInModule(RtlirModule* mod,
                                  std::string_view param_name) {
  for (auto& q : mod->params) {
    if (q.name == param_name) {
      return &q;
    }
  }
  return nullptr;
}

RtlirParamDecl* FindParamUnderChild(RtlirModule* parent,
                                    std::string_view inst_name,
                                    std::string_view param_name) {
  for (auto& child : parent->children) {
    if (child.inst_name == inst_name && child.resolved) {
      RtlirParamDecl* p = FindParamInModule(child.resolved, param_name);
      if (p != nullptr) {
        return p;
      }
    }
  }
  return nullptr;
}

size_t CountChildrenByModule(RtlirModule* mod, std::string_view module_name) {
  size_t n = 0;
  for (auto& child : mod->children) {
    if (child.module_name == module_name) {
      ++n;
    }
  }
  return n;
}

TEST(ElaborationOrder, GenerateConditionObservesInstanceParameterOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module marker; endmodule\n"
      "module picker #(parameter int P = 1)();\n"
      "  if (P == 2) begin\n"
      "    marker m();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  picker #(.P(2)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_FALSE(u->children.empty());
  EXPECT_EQ(u->children[0].module_name, "marker");
}

TEST(ElaborationOrder, GenerateConditionObservesDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module marker; endmodule\n"
      "module picker #(parameter int P = 1)();\n"
      "  if (P == 2) begin\n"
      "    marker m();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  picker u();\n"
      "  defparam u.P = 2;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_FALSE(u->params.empty());
  EXPECT_EQ(u->params[0].resolved_value, 2);
  ASSERT_FALSE(u->children.empty());
  EXPECT_EQ(u->children[0].module_name, "marker");
}

TEST(ElaborationOrder, GenerateDrivesFurtherGenerateEvaluationOnNextIteration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module inner #(parameter int Q = 0)();\n"
      "  if (Q == 1) begin\n"
      "    leaf l();\n"
      "  end\n"
      "endmodule\n"
      "module outer;\n"
      "  if (1) begin\n"
      "    inner #(.Q(1)) i1();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  outer u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_FALSE(u->children.empty());
  auto* i1 = u->children[0].resolved;
  ASSERT_NE(i1, nullptr);
  ASSERT_FALSE(i1->children.empty());
  EXPECT_EQ(i1->children[0].module_name, "leaf");
}

TEST(ElaborationOrder, DefparamResolvesTargetCreatedByGenerate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inner #(parameter int P = 5)();\n"
      "endmodule\n"
      "module outer;\n"
      "  if (1) begin\n"
      "    inner i1();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  outer u();\n"
      "  defparam u.i1.P = 99;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  RtlirParamDecl* p = FindParamUnderChild(u, "i1", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_resolved);
  EXPECT_EQ(p->resolved_value, 99);
}

TEST(ElaborationOrder, DesignWithoutGeneratesTerminatesInSinglePass) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  leaf l();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* leaf = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  ASSERT_FALSE(leaf->params.empty());
  EXPECT_TRUE(leaf->params[0].is_resolved);
  EXPECT_EQ(leaf->params[0].resolved_value, 7);
}

// The ordering rule governs every kind of generate construct, not just the
// conditional (if) form. Here a loop generate's iteration bound reads a
// parameter that a defparam overrides. Because step (b) finalizes the
// parameter before step (c) evaluates the generate scheme, the loop must run
// the overridden number of times (3), not the default zero. The three marker
// instances the loop body creates surface as children of the fanout instance.
TEST(ElaborationOrder, GenerateForBoundObservesDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module marker; endmodule\n"
      "module fanout #(parameter int N = 0)();\n"
      "  genvar i;\n"
      "  for (i = 0; i < N; i = i + 1) begin : g\n"
      "    marker m();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  fanout u();\n"
      "  defparam u.N = 3;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_FALSE(u->params.empty());
  EXPECT_EQ(u->params[0].resolved_value, 3);
  EXPECT_EQ(CountChildrenByModule(u, "marker"), 3u);
}

// Same ordering rule for the case form of a generate construct. The case
// selector reads a parameter overridden by a defparam; the finalized value
// (1) must pick the matching branch rather than the default branch that the
// declared default (0) would select. The instance in the chosen branch is
// hoisted into the picker instance's children.
TEST(ElaborationOrder, GenerateCaseSelectorObservesDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module wide_marker; endmodule\n"
      "module narrow_marker; endmodule\n"
      "module picker #(parameter int SEL = 0)();\n"
      "  case (SEL)\n"
      "    1: begin wide_marker w(); end\n"
      "    default: begin narrow_marker n(); end\n"
      "  endcase\n"
      "endmodule\n"
      "module top;\n"
      "  picker u();\n"
      "  defparam u.SEL = 1;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_FALSE(u->params.empty());
  EXPECT_EQ(u->params[0].resolved_value, 1);
  EXPECT_EQ(CountChildrenByModule(u, "wide_marker"), 1u);
  EXPECT_EQ(CountChildrenByModule(u, "narrow_marker"), 0u);
}

}  // namespace

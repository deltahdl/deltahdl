#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
  RtlirParamDecl* p = nullptr;
  for (auto& child : u->children) {
    if (child.inst_name == "i1" && child.resolved) {
      for (auto& q : child.resolved->params) {
        if (q.name == "P") {
          p = &q;
          break;
        }
      }
    }
  }
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

}  // namespace

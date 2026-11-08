#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Generates : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Generates, SizeCountsGenScopeElements) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  VpiObject not_an_element;
  not_an_element.type = vpiNet;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.size = 99;
  array.children = {&elem0, &not_an_element, &elem1};

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&array)), 2);
}

TEST_F(Generates, SizeIsZeroForEmptyGenScopeArray) {
  VpiObject array;
  array.type = vpiGenScopeArray;
  array.size = 7;

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&array)), 0);
}

TEST_F(Generates, ElementsAccessedByIndex) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  elem0.index = 0;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  elem1.index = 1;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.children = {&elem0, &elem1};

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(VpiHandleOf(&array), 0)), &elem0);
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(VpiHandleOf(&array), 1)), &elem1);
  EXPECT_EQ(vpi_handle_by_index(VpiHandleOf(&array), 2), nullptr);
}

TEST_F(Generates, ElementSelectedByMultiIndex) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  elem0.index = 0;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  elem1.index = 1;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.children = {&elem0, &elem1};

  int indices[] = {1};
  EXPECT_EQ(
      VpiObjectOf(vpi_handle_by_multi_index(VpiHandleOf(&array), 1, indices)),
      &elem1);
}

TEST_F(Generates, IndexReachesArrayMemberIndexExpression) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject gen_scope;
  gen_scope.type = vpiGenScope;
  gen_scope.array_member = true;
  gen_scope.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&gen_scope))),
            &index_expr);
}

TEST_F(Generates, IndexIsNullWhenGenScopeIsNotAnArrayMember) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject gen_scope;
  gen_scope.type = vpiGenScope;
  gen_scope.array_member = false;
  gen_scope.index_expr = &stray_expr;

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&gen_scope)), nullptr);
}

TEST_F(Generates, ImplicitlyDeclaredScopeReportsTrue) {
  VpiObject implicit_scope;
  implicit_scope.type = vpiGenScope;
  implicit_scope.implicit_decl = true;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, VpiHandleOf(&implicit_scope)), 1);

  VpiObject named_scope;
  named_scope.type = vpiGenScope;
  named_scope.implicit_decl = false;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, VpiHandleOf(&named_scope)), 0);
}

TEST_F(Generates, ParameterInAGenScopeIsALocalParameter) {
  VpiObject gen_scope;
  gen_scope.type = vpiGenScope;

  VpiObject plain_parameter;
  plain_parameter.type = vpiParameter;
  plain_parameter.local_param = false;
  plain_parameter.parent = &gen_scope;

  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&plain_parameter)), 1);

  VpiObject module;
  module.type = vpiModule;

  VpiObject outside;
  outside.type = vpiParameter;
  outside.local_param = false;
  outside.parent = &module;

  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&outside)), 0);
}

class GeneratesOfARun : public VpiDesignRun {};

constexpr const char* kGenerates =
    "module top;\n"
    "  for (genvar i = 0; i < 3; i++) begin : g logic v; end\n"
    "  if (1) begin : c logic w; end\n"
    "endmodule\n";

TEST_F(GeneratesOfARun, ALoopBlockInstanceIsAGenScope) {
  Run(kGenerates);
  vpiHandle block = By("top.g[2]");
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiType, block), vpiGenScope);
  EXPECT_EQ(vpi_get(vpiArrayMember, block), 1);
  vpiHandle index = vpi_handle(vpiIndex, block);
  ASSERT_NE(index, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(index, &value);
  EXPECT_EQ(value.value.integer, 2);
}

TEST_F(GeneratesOfARun, ALoopsBlocksAreAGenScopeArray) {
  Run(kGenerates);
  EXPECT_EQ(KindsOf(vpiGenScopeArray, By("top")),
            std::vector<int>{vpiGenScopeArray});
  vpiHandle it = vpi_iterate(vpiGenScopeArray, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle array = vpi_scan(it);
  ASSERT_NE(array, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, array), "g");
  EXPECT_EQ(vpi_get(vpiSize, array), 3);
  EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(array, 1)),
            VpiObjectOf(By("top.g[1]")));
}

TEST_F(GeneratesOfARun, AConditionalBlockInstanceIsAGenScope) {
  Run(kGenerates);
  vpiHandle block = By("top.c");
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiType, block), vpiGenScope);
  EXPECT_EQ(vpi_get(vpiArrayMember, block), 0);
  EXPECT_EQ(vpi_handle(vpiIndex, block), nullptr);
}

TEST_F(GeneratesOfARun, ABlockDeclaringNoDataIsAGenScope) {
  Run("module top;\n"
      "  if (1) begin : t task run(); endtask end\n"
      "  if (1) begin : e end\n"
      "  if (1) begin : o if (1) begin : i end end\n"
      "endmodule\n");
  for (const char* name : {"top.t", "top.e", "top.o", "top.o.i"}) {
    vpiHandle block = By(name);
    ASSERT_NE(block, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, block), vpiGenScope) << name;
    EXPECT_STREQ(vpi_get_str(vpiFullName, block), name);
  }
  EXPECT_NE(Named(vpiTaskFunc, By("top.t"), "run"), nullptr);
}

TEST_F(GeneratesOfARun, AnUnnamedBlockIsAnImplicitGenScope) {
  Run("module top;\n"
      "  if (1) begin task t(); endtask end\n"
      "  for (genvar i = 0; i < 2; i++) begin end\n"
      "  if (1) begin : named end\n"
      "endmodule\n");
  for (const char* name : {"top.genblk1", "top.genblk2[1]"}) {
    vpiHandle block = By(name);
    ASSERT_NE(block, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, block), vpiGenScope) << name;
    EXPECT_EQ(vpi_get(vpiImplicitDecl, block), 1) << name;
    EXPECT_STREQ(vpi_get_str(vpiFullName, block), name);
  }
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.named")), 0);
  EXPECT_NE(Named(vpiTaskFunc, By("top.genblk1"), "t"), nullptr);
}

TEST_F(Generates, TheTypedefIterationPassesOverATypeParameter) {
  VpiObject type_param;
  type_param.type = vpiTypeParameter;
  VpiObject typedef_spec;
  typedef_spec.type = vpiIntTypespec;
  VpiObject scope;
  scope.type = vpiGenScope;
  scope.children = {&type_param, &typedef_spec};
  vpiHandle it = vpi_iterate(vpiTypedef, VpiHandleOf(&scope));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &typedef_spec);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(GeneratesOfARun, AGenScopeReachesTheTypedefsItsBlockDeclares) {
  Run("module top; logic clk;\n"
      "  if (1) begin : g\n"
      "    typedef logic [3:0] nib_t;\n"
      "    property p(nib_t v); @(posedge clk) v[0]; endproperty\n"
      "  end\n"
      "endmodule\n");
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  vpiHandle nib = Named(vpiTypedef, g, "nib_t");
  ASSERT_NE(nib, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nib), vpiLogicTypespec);
  vpiHandle decl = Named(vpiPropertyDecl, g, "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_TRUE(vpi_compare_objects(
      vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v")), nib));
}

TEST_F(GeneratesOfARun, AnInstanceOfAGenerateBlockIsInItsGenScope) {
  Run("module deep; initial begin : b t(); end endmodule\n"
      "module top; task t; endtask\n"
      "  if (1) begin : g deep d2 (); end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiModule, By("top")), std::vector<std::string>{});
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(NamesOf(vpiModule, g), std::vector<std::string>{"d2"});
  vpiHandle d2 = By("top.g.d2");
  ASSERT_NE(d2, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, d2), "top.g.d2");
  EXPECT_EQ(By("top.g_d2"), nullptr);
  vpiHandle b = By("top.g.d2.b");
  ASSERT_NE(b, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, b), "top.g.d2.b");
  vpiHandle call = CallOf(vpiTaskCall, b, "t");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "t")));
}

TEST_F(GeneratesOfARun, ALoopsGenScopeArrayReachesItsGenVar) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 3; i++) begin : g logic v; end\n"
      "  for (genvar j = 0; j < 2; j++) begin end\n"
      "endmodule\n");
  vpiHandle g = vpi_handle(vpiGenScopeArray, By("top.g[0]"));
  ASSERT_NE(g, nullptr);
  vpiHandle i = vpi_handle(vpiGenVar, g);
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(vpi_get(vpiType, i), vpiGenVar);
  EXPECT_STREQ(vpi_get_str(vpiName, i), "i");
  EXPECT_STREQ(vpi_get_str(vpiFullName, i), "top.i");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiGenScopeArray, i)), VpiObjectOf(g));
  EXPECT_EQ(vpi_get(vpiSize, g), 3);
  EXPECT_EQ(vpi_handle_by_index(g, -1), nullptr);
  vpiHandle unnamed = vpi_handle(vpiGenScopeArray, By("top.genblk2[1]"));
  ASSERT_NE(unnamed, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiGenVar, unnamed)), "j");
}

TEST_F(GeneratesOfARun, AGenScopeAnswersProtectedAndArray) {
  Run(kGenerates);
  EXPECT_EQ(vpi_get(vpiProtected, By("top.g[1]")), 0);
  EXPECT_EQ(vpi_get(vpiArray, By("top.g[1]")), 1);
  EXPECT_EQ(vpi_get(vpiProtected, By("top.c")), 0);
  EXPECT_EQ(vpi_get(vpiArray, By("top.c")), 0);
}

TEST_F(GeneratesOfARun, AGenVarReferenceIsALocalParameter) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    wire [31:0] w;\n"
      "    assign w = i + 5;\n"
      "  end\n"
      "endmodule\n");
  std::vector<int> values;
  for (const char* scope : {"top.g[0]", "top.g[1]"}) {
    vpiHandle it = vpi_iterate(vpiContAssign, By(scope));
    ASSERT_NE(it, nullptr);
    const std::vector<vpiHandle> kOperands =
        OperandsOf(vpi_handle(vpiRhs, vpi_scan(it)));
    ASSERT_EQ(kOperands.size(), 2u);
    vpiHandle ref = kOperands[0];
    EXPECT_EQ(vpi_get(vpiType, ref), vpiParameter);
    EXPECT_EQ(vpi_get(vpiLocalParam, ref), 1);
    EXPECT_STREQ(vpi_get_str(vpiName, ref), "i");
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(ref, &value);
    values.push_back(value.value.integer);
  }
  EXPECT_EQ(values, (std::vector<int>{0, 1}));
}

TEST_F(GeneratesOfARun, AGenerateBlocksAssignmentIsOneOfItsGenScope) {
  Run("module top;\n"
      "  wire a;\n"
      "  assign a = 1;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    wire w;\n"
      "    if (1) begin : h wire x; assign x = i; end\n"
      "    assign w = i;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<std::pair<const char*, const char*>> kAssigned = {
      {"top", "a"}, {"top.g[0]", "w"}, {"top.g[1]", "w"}, {"top.g[1].h", "x"}};
  for (const auto& [scope, target] : kAssigned) {
    EXPECT_EQ(KindsOf(vpiContAssign, By(scope)),
              std::vector<int>{vpiContAssign});
    vpiHandle it = vpi_iterate(vpiContAssign, By(scope));
    ASSERT_NE(it, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, vpi_scan(it))),
                 target);
  }
}

TEST_F(GeneratesOfARun, AnIterationsGenvarLocalparamIsAParameterOfItsScope) {
  Run(kGenerates);
  vpiHandle i = Named(vpiParameter, By("top.g[2]"), "i");
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalParam, i), 1);
  EXPECT_STREQ(vpi_get_str(vpiFullName, i), "top.g[2].i");
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(i, &value);
  EXPECT_EQ(value.value.integer, 2);
  EXPECT_EQ(NamesOf(vpiVariables, By("top.g[2]")),
            std::vector<std::string>{"v"});
}

TEST_F(GeneratesOfARun, AGenerateBlocksParameterIsALocalParameterOfItsScope) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    parameter P = 3 + i;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle p = Named(vpiParameter, By("top.g[1]"), "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalParam, p), 1);
  EXPECT_STREQ(vpi_get_str(vpiFullName, p), "top.g[1].P");
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(p, &value);
  EXPECT_EQ(value.value.integer, 4);
  EXPECT_EQ(NamesOf(vpiVariables, By("top.g[1]")), std::vector<std::string>{});
  EXPECT_EQ(By("top.g_1_P"), nullptr);
}

}  // namespace
}  // namespace delta

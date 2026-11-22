#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class GenScopeArrays : public VpiDesignRun {
 protected:
  static vpiHandle ArrayOf(const char* element) {
    vpiHandle scope = By(element);
    return scope == nullptr ? nullptr : vpi_handle(vpiGenScopeArray, scope);
  }

  static std::vector<std::string> FullNamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      names.emplace_back(vpi_get_str(vpiFullName, obj));
    }
    return names;
  }

  static int IndexValueOf(const char* element) {
    vpiHandle scope = By(element);
    if (scope == nullptr) return -1000;
    vpiHandle index = vpi_handle(vpiIndex, scope);
    return index == nullptr ? -1000 : IntegerOf(index);
  }

  static std::string SelectedBy(vpiHandle array, int index) {
    vpiHandle element = vpi_handle_by_index(array, index);
    return element == nullptr ? "" : vpi_get_str(vpiFullName, element);
  }

  static std::string SelectedByMulti(vpiHandle array, int index) {
    PLI_INT32 indices[1] = {index};
    vpiHandle element = vpi_handle_by_multi_index(array, 1, indices);
    return element == nullptr ? "" : vpi_get_str(vpiFullName, element);
  }
};

constexpr const char* kSteppedLoops =
    "module top;\n"
    "  for (genvar i = 4; i < 7; i++) begin : up end\n"
    "  for (genvar i = -2; i < 1; i++) begin : neg end\n"
    "  for (genvar i = 0; i < 8; i += 2) begin : step end\n"
    "  for (genvar i = 5; i > 0; i--) begin : down end\n"
    "endmodule\n";

TEST_F(GenScopeArrays, AnArrayIteratesExactlyItsElementScopes) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 3; i++) begin : g logic v; end\n"
      "endmodule\n");
  vpiHandle array = ArrayOf("top.g[0]");
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(FullNamesOf(vpiGenScope, array),
            (std::vector<std::string>{"top.g[0]", "top.g[1]", "top.g[2]"}));
  for (vpiHandle scope : ObjectsOf(vpiGenScope, array)) {
    EXPECT_EQ(vpi_get(vpiType, scope), vpiGenScope);
  }
}

TEST_F(GenScopeArrays, AConditionalScopeReachesNoArray) {
  Run("module top;\n"
      "  if (1) begin : c logic w; end\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    if (1) begin : c logic x; end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(By("top.c"), nullptr);
  EXPECT_EQ(vpi_handle(vpiGenScopeArray, By("top.c")), nullptr);
  ASSERT_NE(By("top.g[0].c"), nullptr);
  EXPECT_EQ(vpi_handle(vpiGenScopeArray, By("top.g[0].c")), nullptr);
}

TEST_F(GenScopeArrays, AnArrayAnswersItsNames) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g end\n"
      "  for (genvar j = 0; j < 2; j++) begin end\n"
      "  if (1) begin : o for (genvar k = 0; k < 2; k++) begin : g end end\n"
      "endmodule\n");
  vpiHandle named = ArrayOf("top.g[0]");
  ASSERT_NE(named, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, named), "g");
  EXPECT_STREQ(vpi_get_str(vpiFullName, named), "top.g");
  vpiHandle unnamed = ArrayOf("top.genblk2[0]");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, unnamed), "genblk2");
  EXPECT_STREQ(vpi_get_str(vpiFullName, unnamed), "top.genblk2");
  vpiHandle nested = ArrayOf("top.o.g[1]");
  ASSERT_NE(nested, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, nested), "g");
  EXPECT_STREQ(vpi_get_str(vpiFullName, nested), "top.o.g");
}

TEST_F(GenScopeArrays, TheSizeIsTheNumberOfIterations) {
  Run(kSteppedLoops);
  EXPECT_EQ(vpi_get(vpiSize, ArrayOf("top.up[4]")), 3);
  EXPECT_EQ(vpi_get(vpiSize, ArrayOf("top.neg[-2]")), 3);
  EXPECT_EQ(vpi_get(vpiSize, ArrayOf("top.step[6]")), 4);
  EXPECT_EQ(vpi_get(vpiSize, ArrayOf("top.down[1]")), 5);
}

TEST_F(GenScopeArrays, AnUnnamedLoopsSizeIsItsIterationCount) {
  Run("module top;\n"
      "  if (1) begin : c end\n"
      "  for (genvar j = 0; j < 2; j++) begin end\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, ArrayOf("top.genblk2[1]")), 2);
}

TEST_F(GenScopeArrays, ALoopOfNoIterationsHoldsNoScope) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 0; i++) begin : z end\n"
      "endmodule\n");
  vpiHandle array = Named(vpiGenScopeArray, By("top"), "z");
  if (array != nullptr) {
    EXPECT_EQ(vpi_get(vpiSize, array), 0);
    EXPECT_EQ(vpi_iterate(vpiGenScope, array), nullptr);
  }
  EXPECT_EQ(By("top.z[0]"), nullptr);
}

TEST_F(GenScopeArrays, AnElementsIndexIsItsGenvarValue) {
  Run(kSteppedLoops);
  EXPECT_EQ(IndexValueOf("top.up[4]"), 4);
  EXPECT_EQ(IndexValueOf("top.up[6]"), 6);
  EXPECT_EQ(IndexValueOf("top.neg[-2]"), -2);
  EXPECT_EQ(IndexValueOf("top.neg[0]"), 0);
  EXPECT_EQ(IndexValueOf("top.step[6]"), 6);
  EXPECT_EQ(IndexValueOf("top.down[5]"), 5);
}

TEST_F(GenScopeArrays, ACaseGenerateScopeIsNoArrayMember) {
  Run("module top;\n"
      "  localparam int K = 2;\n"
      "  case (K) 1: begin : one end 2: begin : two logic v; end endcase\n"
      "endmodule\n");
  vpiHandle two = By("top.two");
  ASSERT_NE(two, nullptr);
  EXPECT_EQ(vpi_get(vpiType, two), vpiGenScope);
  EXPECT_EQ(vpi_handle(vpiIndex, two), nullptr);
  EXPECT_EQ(vpi_get(vpiArrayMember, two), 0);
  EXPECT_EQ(vpi_get(vpiArray, two), 0);
  EXPECT_EQ(vpi_get(vpiProtected, two), 0);
  EXPECT_EQ(vpi_handle(vpiGenScopeArray, two), nullptr);
  EXPECT_EQ(By("top.one"), nullptr);
}

TEST_F(GenScopeArrays, AnElementIsSelectedByItsGenvarValue) {
  Run(kSteppedLoops);
  vpiHandle up = ArrayOf("top.up[4]");
  ASSERT_NE(up, nullptr);
  EXPECT_EQ(SelectedBy(up, 4), "top.up[4]");
  EXPECT_EQ(SelectedBy(up, 6), "top.up[6]");
  EXPECT_EQ(SelectedBy(up, 0), "");
  EXPECT_EQ(SelectedBy(up, 7), "");
  vpiHandle neg = ArrayOf("top.neg[0]");
  ASSERT_NE(neg, nullptr);
  EXPECT_EQ(SelectedBy(neg, -2), "top.neg[-2]");
  EXPECT_EQ(SelectedBy(neg, 1), "");
  vpiHandle step = ArrayOf("top.step[0]");
  ASSERT_NE(step, nullptr);
  EXPECT_EQ(SelectedBy(step, 2), "top.step[2]");
  EXPECT_EQ(SelectedBy(step, 6), "top.step[6]");
  EXPECT_EQ(SelectedBy(step, 3), "");
  EXPECT_EQ(SelectedBy(step, 1), "");
  vpiHandle down = ArrayOf("top.down[5]");
  ASSERT_NE(down, nullptr);
  EXPECT_EQ(SelectedBy(down, 5), "top.down[5]");
  EXPECT_EQ(SelectedBy(down, 1), "top.down[1]");
  EXPECT_EQ(SelectedBy(down, 0), "");
}

TEST_F(GenScopeArrays, AnElaboratedElementIsSelectedByMultiIndex) {
  Run(kSteppedLoops);
  vpiHandle up = ArrayOf("top.up[4]");
  ASSERT_NE(up, nullptr);
  EXPECT_EQ(SelectedByMulti(up, 5), "top.up[5]");
  EXPECT_EQ(SelectedByMulti(up, 1), "");
  EXPECT_EQ(SelectedByMulti(up, 9), "");
  vpiHandle neg = ArrayOf("top.neg[0]");
  ASSERT_NE(neg, nullptr);
  EXPECT_EQ(SelectedByMulti(neg, -1), "top.neg[-1]");
}

TEST_F(GenScopeArrays, AnArrayReachesTheInstanceHoldingIt) {
  Run("interface ifc; for (genvar i = 0; i < 2; i++) begin : g end\n"
      "endinterface\n"
      "program pg; for (genvar i = 0; i < 2; i++) begin : g end endprogram\n"
      "module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g end\n"
      "  if (1) begin : o for (genvar k = 0; k < 2; k++) begin : n end end\n"
      "  ifc i0(); pg p0();\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* element : {"top.g[0]", "top.o.n[1]"}) {
    vpiHandle array = ArrayOf(element);
    ASSERT_NE(array, nullptr) << element;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiModule, array), top), 1)
        << element;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiInstance, array), top), 1)
        << element;
  }
  vpiHandle in_interface = ArrayOf("top.i0.g[0]");
  ASSERT_NE(in_interface, nullptr);
  EXPECT_EQ(
      vpi_compare_objects(vpi_handle(vpiInstance, in_interface), By("top.i0")),
      1);
  vpiHandle in_program = ArrayOf("top.p0.g[0]");
  ASSERT_NE(in_program, nullptr);
  EXPECT_EQ(
      vpi_compare_objects(vpi_handle(vpiInstance, in_program), By("top.p0")),
      1);
}

TEST_F(GenScopeArrays, APredeclaredGenvarIsEachArraysGenVar) {
  Run("module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i++) begin : a end\n"
      "  for (i = 0; i < 3; i++) begin : b end\n"
      "endmodule\n");
  for (const char* element : {"top.a[0]", "top.b[0]"}) {
    vpiHandle array = ArrayOf(element);
    ASSERT_NE(array, nullptr) << element;
    vpiHandle gen_var = vpi_handle(vpiGenVar, array);
    ASSERT_NE(gen_var, nullptr) << element;
    EXPECT_EQ(vpi_get(vpiType, gen_var), vpiGenVar) << element;
    EXPECT_STREQ(vpi_get_str(vpiName, gen_var), "i") << element;
    EXPECT_STREQ(vpi_get_str(vpiFullName, gen_var), "top.i") << element;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiGenScopeArray, gen_var), array),
              1)
        << element;
  }
}

}  // namespace
}  // namespace delta

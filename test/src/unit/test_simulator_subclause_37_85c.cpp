#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class GenScopeContents : public VpiDesignRun {
 protected:
  static void ExpectHeldBy(int relation, vpiHandle scope, const char* name) {
    ASSERT_NE(scope, nullptr) << name;
    vpiHandle obj = Named(relation, scope, name);
    ASSERT_NE(obj, nullptr) << name;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiGenScope, obj), scope), 1)
        << name;
  }

  static vpiHandle FirstOf(int type, vpiHandle ref) {
    if (ref == nullptr) return nullptr;
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }

  static void ExpectFirstHeldBy(int relation, vpiHandle scope) {
    vpiHandle obj = FirstOf(relation, scope);
    ASSERT_NE(obj, nullptr) << relation;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiGenScope, obj), scope), 1)
        << relation;
  }
};

constexpr const char* kHolder =
    "module sub; endmodule\n"
    "interface ifc; endinterface\n"
    "program pg; endprogram\n"
    "module top;\n"
    "  if (1) begin : g\n"
    "    logic v; wire w; wire wa[2]; logic va[2];\n"
    "    event e; event ea[2];\n"
    "    wire a1, a2; alias a1 = a2;\n"
    "    assign w = v;\n"
    "    initial v = 0;\n"
    "    sub u(); sub ua[1:0]();\n"
    "    and gt (w, v, v); and gta[1:0] (wa, v, v);\n"
    "    ifc i0(); ifc ia[1:0]();\n"
    "    pg p0(); pg pa[1:0]();\n"
    "    if (1) begin : inner logic x; end\n"
    "    for (genvar i = 0; i < 2; i++) begin : loop end\n"
    "    initial begin : nb logic y; end\n"
    "    task t; endtask\n"
    "    function int f; return 0; endfunction\n"
    "  end\n"
    "endmodule\n";

TEST_F(GenScopeContents, EachKindTheBlockHoldsReachesItsGenScope) {
  Run(kHolder);
  vpiHandle g = By("top.g");
  ExpectHeldBy(vpiVariables, g, "v");
  ExpectHeldBy(vpiNet, g, "w");
  ExpectFirstHeldBy(vpiContAssign, g);
  ExpectFirstHeldBy(vpiProcess, g);
  ExpectHeldBy(vpiModule, g, "u");
  ExpectHeldBy(vpiInternalScope, g, "inner");
  ExpectHeldBy(vpiGenScopeArray, g, "loop");
}

TEST_F(GenScopeContents, EachKindAnIterationHoldsReachesThatIteration) {
  Run("module sub; endmodule\n"
      "module top;\n"
      "  for (genvar k = 0; k < 2; k++) begin : g\n"
      "    logic v; wire w;\n"
      "    assign w = v;\n"
      "    initial v = 0;\n"
      "    sub u();\n"
      "    if (1) begin : inner logic x; end\n"
      "    for (genvar i = 0; i < 2; i++) begin : loop end\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"top.g[0]", "top.g[1]"}) {
    vpiHandle g = By(name);
    ExpectHeldBy(vpiVariables, g, "v");
    ExpectHeldBy(vpiNet, g, "w");
    ExpectFirstHeldBy(vpiContAssign, g);
    ExpectFirstHeldBy(vpiProcess, g);
    ExpectHeldBy(vpiModule, g, "u");
    ExpectHeldBy(vpiInternalScope, g, "inner");
    ExpectHeldBy(vpiGenScopeArray, g, "loop");
  }
}

TEST_F(GenScopeContents, AGenScopeReachesEachDeclarationKind) {
  Run(kHolder);
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_NE(Named(vpiLogicVar, g, "v"), nullptr);
  EXPECT_NE(Named(vpiNet, g, "w"), nullptr);
  EXPECT_NE(Named(vpiArrayNet, g, "wa"), nullptr);
  EXPECT_NE(Named(vpiArrayVar, g, "va"), nullptr);
  EXPECT_NE(Named(vpiMemory, g, "va"), nullptr);
  EXPECT_NE(Named(vpiNamedEvent, g, "e"), nullptr);
  EXPECT_NE(Named(vpiNamedEventArray, g, "ea"), nullptr);
}

TEST_F(GenScopeContents, AGenScopeReachesItsInterfaceProgramAndLoop) {
  Run(kHolder);
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_NE(Named(vpiInterface, g, "i0"), nullptr);
  EXPECT_NE(Named(vpiProgram, g, "p0"), nullptr);
  EXPECT_NE(Named(vpiGenScopeArray, g, "loop"), nullptr);
}

TEST_F(GenScopeContents, DISABLED_AGenScopeReachesItsArraysPrimitivesAndAlias) {
  Run(kHolder);
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_NE(Named(vpiModuleArray, g, "ua"), nullptr);
  EXPECT_NE(Named(vpiPrimitive, g, "gt"), nullptr);
  EXPECT_NE(Named(vpiPrimitiveArray, g, "gta"), nullptr);
  EXPECT_NE(Named(vpiInterfaceArray, g, "ia"), nullptr);
  EXPECT_NE(Named(vpiProgramArray, g, "pa"), nullptr);
  EXPECT_NE(FirstOf(vpiAliasStmt, g), nullptr);
}

TEST_F(GenScopeContents,
       AGenScopesInternalScopesIncludeItsBlocksAndSubroutines) {
  Run(kHolder);
  const std::vector<std::string> kScopes =
      NamesOf(vpiInternalScope, By("top.g"));
  for (const char* name : {"f", "i0", "inner", "nb", "p0", "t", "u"}) {
    EXPECT_NE(std::ranges::find(kScopes, name), kScopes.end()) << name;
  }
}

TEST_F(GenScopeContents, DISABLED_AGenScopeReachesItsDefParam) {
  Run("module sub #(parameter int P = 1); endmodule\n"
      "module top;\n"
      "  if (1) begin : g sub u(); defparam u.P = 2; end\n"
      "endmodule\n");
  vpiHandle param = FirstOf(vpiDefParam, By("top.g"));
  ASSERT_NE(param, nullptr);
  EXPECT_EQ(vpi_get(vpiType, param), vpiDefParam);
}

constexpr const char* kNettypes =
    "module top;\n"
    "  nettype logic [7:0] m_t;\n"
    "  if (1) begin : g nettype logic [3:0] nt_t; end\n"
    "  if (1) begin : h logic q; end\n"
    "endmodule\n";

TEST_F(GenScopeContents, AGenScopeDeclaringNoNettypeIteratesNone) {
  Run(kNettypes);
  ASSERT_NE(By("top.h"), nullptr);
  EXPECT_EQ(vpi_iterate(vpiNetTypedef, By("top.h")), nullptr);
}

TEST_F(GenScopeContents, DISABLED_AGenScopeIteratesTheNettypeItDeclares) {
  Run(kNettypes);
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(NamesOf(vpiNetTypedef, g), std::vector<std::string>{"nt_t"});
  vpiHandle nt = Named(vpiNetTypedef, g, "nt_t");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nt), vpiNettypeDecl);
  EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiParent, nt), g), 1);
}

TEST_F(GenScopeContents, EachIterationReachesItsOwnTypedef) {
  Run("module top;\n"
      "  typedef int m_t;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g typedef logic [3:0] t; end\n"
      "  if (1) begin : c typedef bit b_t; end\n"
      "endmodule\n");
  vpiHandle t0 = Named(vpiTypedef, By("top.g[0]"), "t");
  vpiHandle t1 = Named(vpiTypedef, By("top.g[1]"), "t");
  ASSERT_NE(t0, nullptr);
  ASSERT_NE(t1, nullptr);
  EXPECT_EQ(vpi_compare_objects(t0, t1), 0);
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.c")), std::vector<std::string>{"b_t"});
  const std::vector<std::string> kTops = NamesOf(vpiTypedef, By("top"));
  EXPECT_NE(std::ranges::find(kTops, "m_t"), kTops.end());
  EXPECT_EQ(std::ranges::find(kTops, "b_t"), kTops.end());
}

TEST_F(GenScopeContents, AGenScopeAnswersItsShortName) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 3; i++) begin : g end\n"
      "  if (1) begin : c end\n"
      "  if (1) begin logic u; end\n"
      "  for (genvar j = 0; j < 2; j++) begin end\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiName, By("top.g[2]")), "g[2]");
  EXPECT_STREQ(vpi_get_str(vpiName, By("top.c")), "c");
  EXPECT_STREQ(vpi_get_str(vpiName, By("top.genblk3")), "genblk3");
  EXPECT_STREQ(vpi_get_str(vpiName, By("top.genblk4[1]")), "genblk4[1]");
}

TEST_F(GenScopeContents, EveryUnnamedBlockIsAnImplicitScope) {
  Run("interface ifc; if (1) begin logic a; end endinterface\n"
      "program pg; if (1) begin int b; end endprogram\n"
      "module top;\n"
      "  localparam int K = 1;\n"
      "  if (1) begin end\n"
      "  case (K) 1: begin logic v; end endcase\n"
      "  ifc i0(); pg p0();\n"
      "endmodule\n");
  for (const char* name :
       {"top.genblk1", "top.genblk2", "top.i0.genblk1", "top.p0.genblk1"}) {
    vpiHandle block = By(name);
    ASSERT_NE(block, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, block), vpiGenScope) << name;
    EXPECT_EQ(vpi_get(vpiImplicitDecl, block), 1) << name;
  }
}

}  // namespace
}  // namespace delta

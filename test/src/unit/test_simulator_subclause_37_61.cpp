#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class DynamicPrefixing : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(DynamicPrefixing, PrefixSourceClassifier) {
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiRefObj));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiBitSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiPartSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiIndexedPartSelect));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsDynamicPrefixSourceType(vpiNamedEventArray));

  EXPECT_FALSE(VpiIsDynamicPrefixSourceType(vpiMethodFuncCall));
  EXPECT_FALSE(VpiIsDynamicPrefixSourceType(vpiModule));
  for (int simple : {vpiNet, vpiNetBit, vpiIntVar, vpiRegBit, vpiParameter,
                     vpiSpecParam, vpiVarSelect}) {
    EXPECT_TRUE(VpiIsDynamicPrefixSourceType(simple)) << simple;
  }
}

TEST_F(DynamicPrefixing, PrefixReachesEachPrefixTargetKind) {
  for (int prefix_kind :
       {vpiClassVar, vpiVirtualInterfaceVar, vpiClockingBlock}) {
    VpiObject prefix;
    prefix.type = prefix_kind;

    VpiObject part_select;
    part_select.type = vpiPartSelect;
    part_select.prefix = &prefix;

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, VpiHandleOf(&part_select))),
              &prefix)
        << "prefix kind " << prefix_kind;
  }
}

TEST_F(DynamicPrefixing, PrefixIsNullWhenObjectIsNotPrefixed) {
  VpiObject child;
  child.type = vpiOperation;

  VpiObject simple_expr;
  simple_expr.type = vpiRefObj;
  simple_expr.children = {&child};

  EXPECT_EQ(vpi_handle(vpiPrefix, VpiHandleOf(&simple_expr)), nullptr);
}

TEST_F(DynamicPrefixing, AllocSchemeFollowsClassVarAndVifPrefix) {
  for (int prefix_kind : {vpiClassVar, vpiVirtualInterfaceVar}) {
    VpiObject prefix;
    prefix.type = prefix_kind;
    prefix.alloc_scheme = kVpiAutomaticScheme;

    VpiObject part_select;
    part_select.type = vpiPartSelect;
    part_select.alloc_scheme = kVpiOtherScheme;
    part_select.prefix = &prefix;

    EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&part_select)),
              kVpiAutomaticScheme)
        << "prefix kind " << prefix_kind;
  }

  VpiObject unprefixed;
  unprefixed.type = vpiPartSelect;
  unprefixed.alloc_scheme = kVpiDynamicScheme;
  EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&unprefixed)),
            kVpiDynamicScheme);
}

TEST_F(DynamicPrefixing, AllocSchemeIgnoresClockingBlockPrefix) {
  VpiObject prefix;
  prefix.type = vpiClockingBlock;
  prefix.alloc_scheme = kVpiAutomaticScheme;

  VpiObject part_select;
  part_select.type = vpiPartSelect;
  part_select.alloc_scheme = kVpiOtherScheme;
  part_select.prefix = &prefix;

  EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&part_select)),
            kVpiOtherScheme);
}

TEST_F(DynamicPrefixing, HasActualThroughVpiGet) {
  VpiObject actual;
  actual.type = vpiNamedEvent;

  VpiObject sim_bound;
  sim_bound.type = vpiNamedEvent;
  sim_bound.actual = &actual;
  EXPECT_EQ(vpi_get(vpiHasActual, VpiHandleOf(&sim_bound)), 1);

  VpiObject sim_unbound;
  sim_unbound.type = vpiNamedEvent;
  EXPECT_EQ(vpi_get(vpiHasActual, VpiHandleOf(&sim_unbound)), 0);

  for (int origin : {kVpiActualStaticElab, kVpiActualFrameVar}) {
    VpiObject obj;
    obj.type = vpiRefObj;
    obj.actual_origin = origin;
    EXPECT_EQ(vpi_get(vpiHasActual, VpiHandleOf(&obj)), 1)
        << "origin " << origin;
  }

  for (int origin : {kVpiActualLexicalDefn, kVpiActualClassTypespec,
                     kVpiActualTaskFuncVar}) {
    VpiObject obj;
    obj.type = vpiRefObj;
    obj.actual = &actual;
    obj.actual_origin = origin;
    EXPECT_EQ(vpi_get(vpiHasActual, VpiHandleOf(&obj)), 0)
        << "origin " << origin;
  }
}

TEST_F(DynamicPrefixing, HasActualIsUndefinedForNonSourceKind) {
  VpiObject module;
  module.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiHasActual, VpiHandleOf(&module)), vpiUndefined);
}

std::string g_arg_name;
std::string g_prefix_name;
int g_arg_type = 0;
int g_arg_size = 0;
int g_arg_has_actual = -1;
int g_prefix_type = 0;
bool g_second_arg_has_prefix = true;

PLI_INT32 ReadPrefixCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiArgument, call);
  if (itr == nullptr) return 0;
  vpiHandle arg = vpi_scan(itr);
  if (arg == nullptr) return 0;

  g_arg_type = vpi_get(vpiType, arg);
  g_arg_size = vpi_get(vpiSize, arg);
  if (const char* name = vpi_get_str(vpiName, arg)) g_arg_name = name;
  g_arg_has_actual = vpi_get(vpiHasActual, arg);

  vpiHandle prefix = vpi_handle(vpiPrefix, arg);
  if (prefix != nullptr) {
    g_prefix_type = vpi_get(vpiType, prefix);
    if (const char* name = vpi_get_str(vpiName, prefix)) g_prefix_name = name;
  }

  if (vpiHandle plain = vpi_scan(itr)) {
    g_second_arg_has_prefix = vpi_handle(vpiPrefix, plain) != nullptr;
  }
  return 0;
}

class DynamicPrefixingOfADesign : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_arg_name.clear();
    g_prefix_name.clear();
    g_arg_type = 0;
    g_arg_size = 0;
    g_arg_has_actual = -1;
    g_prefix_type = 0;
    g_second_arg_has_prefix = true;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void Probe(const char* src) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ReadPrefixCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);

    auto* design = ElaborateSrc(src, f_);
    ASSERT_NE(design, nullptr);
    LowerAndRun(design, f_);
  }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(DynamicPrefixingOfADesign, PrefixOfAVirtualInterfaceArgument) {
  Probe(
      "interface simple_bus;\n"
      "  logic [7:0] a;\n"
      "endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  logic [3:0] plain;\n"
      "  initial begin\n"
      "    vif = u;\n"
      "    $probe(vif.a, plain);\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(g_arg_type, vpiRefObj);
  EXPECT_EQ(g_arg_name, "vif.a");
  EXPECT_EQ(g_arg_size, 8);
  EXPECT_EQ(g_prefix_type, vpiVirtualInterfaceVar);
  EXPECT_EQ(g_prefix_name, "vif");
  EXPECT_FALSE(g_second_arg_has_prefix);

  EXPECT_EQ(g_arg_has_actual, 1);
}

TEST_F(DynamicPrefixingOfADesign, UnboundPrefixHasNoActual) {
  Probe(
      "interface simple_bus;\n"
      "  logic [7:0] a;\n"
      "endinterface\n"
      "module top;\n"
      "  simple_bus u();\n"
      "  virtual simple_bus vif;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "    $probe(vif.a);\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(g_arg_type, vpiRefObj);
  EXPECT_EQ(g_prefix_type, vpiVirtualInterfaceVar);
  EXPECT_EQ(g_arg_has_actual, 0);
}

TEST(DynamicPrefixHasActual, AnUnlistedOriginTracksTheCurrentActual) {
  EXPECT_TRUE(VpiObjectHasActual(999, true));
  EXPECT_FALSE(VpiObjectHasActual(999, false));
}
class PrefixingOfARun : public VpiDesignRun {
 protected:
  static vpiHandle RhsOfFirst(const char* instance) {
    vpiHandle it = vpi_iterate(vpiProcess, By(instance));
    if (it == nullptr) return nullptr;
    vpiHandle rhs = nullptr;
    for (vpiHandle proc = vpi_scan(it); proc != nullptr; proc = vpi_scan(it)) {
      if (rhs == nullptr) rhs = vpi_handle(vpiRhs, vpi_handle(vpiStmt, proc));
    }
    return rhs;
  }

  static void ExpectRhsPrefixedBy(const char* instance, int holder) {
    vpiHandle ref = RhsOfFirst(instance);
    ASSERT_NE(ref, nullptr);
    EXPECT_EQ(vpi_get(vpiType, ref), vpiRefObj);
    vpiHandle prefix = vpi_handle(vpiPrefix, ref);
    ASSERT_NE(prefix, nullptr);
    EXPECT_EQ(vpi_get(vpiType, prefix), holder);
  }
};

TEST_F(PrefixingOfARun, AStaticallyDeclaredObjectHasAnActual) {
  Run("module top; event e; wire [3:0] w; int v; endmodule\n");
  for (const char* name : {"top.e", "top.w", "top.v", "top.w[1]"}) {
    EXPECT_EQ(vpi_get(vpiHasActual, By(name)), 1) << name;
  }
}

TEST_F(PrefixingOfARun, AnExpressionThroughAVirtualInterfaceReachesIt) {
  Run("interface ifc; logic a; endinterface\n"
      "module top; ifc i0(); virtual ifc vif = i0; logic y;\n"
      "  initial y = vif.a;\n"
      "endmodule\n");
  ExpectRhsPrefixedBy("top", vpiVirtualInterfaceVar);
}

TEST_F(PrefixingOfARun, APropertyThroughAClassVarReachesIt) {
  Run("class C; int x; endclass\n"
      "module top; C c; int y;\n"
      "  initial y = c.x;\n"
      "endmodule\n");
  ExpectRhsPrefixedBy("top", vpiClassVar);
}

TEST_F(PrefixingOfARun, AnExpressionThroughAClockingBlockReachesIt) {
  Run("module top; logic clk, d, y;\n"
      "  clocking cb @(posedge clk); input d; endclocking\n"
      "  initial y = cb.d;\n"
      "endmodule\n");
  ExpectRhsPrefixedBy("top", vpiClockingBlock);
}

TEST_F(PrefixingOfARun, AnExpressionThroughAnInstancesClockingBlockReachesIt) {
  Run("module m; logic clk, d, y;\n"
      "  clocking cb @(posedge clk); input d; endclocking\n"
      "  initial y = cb.d;\n"
      "endmodule\n"
      "module top; m u(); endmodule\n");
  ExpectRhsPrefixedBy("top.u", vpiClockingBlock);
}

TEST_F(PrefixingOfARun,
       AnInitializerThroughTheFirstTopsClockingBlockReachesIt) {
  Run("module top; logic clk, d;\n"
      "  clocking cb @(posedge clk); input d; endclocking\n"
      "  logic y = cb.d;\n"
      "endmodule\n");
  vpiHandle ref = vpi_handle(vpiExpr, By("top.y"));
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ref), vpiRefObj);
  vpiHandle prefix = vpi_handle(vpiPrefix, ref);
  ASSERT_NE(prefix, nullptr);
  EXPECT_EQ(vpi_get(vpiType, prefix), vpiClockingBlock);
}

}  // namespace
}  // namespace delta

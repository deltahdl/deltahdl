#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(ObjectLifetimes, DefaultObjectIsStaticWithOtherScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&obj)), 0);
  EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&obj)), vpiOtherScheme);
}

TEST(ObjectLifetimes, AutomaticObjectReportsAutomaticScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.automatic = true;
  obj.alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);

  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&obj)), 1);
  EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&obj)), vpiAutomaticScheme);
}

TEST(ObjectLifetimes, DynamicObjectReportsDynamicScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.automatic = true;
  obj.alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kDynamic);

  EXPECT_EQ(vpi_get(vpiAllocScheme, VpiHandleOf(&obj)), vpiDynamicScheme);
}

TEST(ObjectLifetimes, AllocSchemeForCoversAllThreeKinds) {
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread),
            vpiAutomaticScheme);
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kDynamic), vpiDynamicScheme);
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kOther), vpiOtherScheme);
}

TEST(ObjectLifetimes, AutomaticIsAlsoAContainerProperty) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  const int kKinds[] = {vpiModule, vpiProgram, vpiInterface, vpiPackage};
  for (int kind : kKinds) {
    VpiObject automatic_container;
    automatic_container.type = kind;
    automatic_container.automatic = true;
    EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&automatic_container)), 1)
        << "kind=" << kind;

    VpiObject static_container;
    static_container.type = kind;
    static_container.automatic = false;
    EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&static_container)), 0)
        << "kind=" << kind;
  }
}

TEST(ObjectLifetimes, AClassDefnAndClassTypespecAreAutomatic) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  for (int kind : {vpiClassDefn, vpiClassTypespec}) {
    VpiObject obj;
    obj.type = kind;
    EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&obj)), 1) << "kind=" << kind;
  }
}

class LifetimesOfARun : public VpiDesignRun {};

TEST_F(LifetimesOfARun, AnInstanceReportsItsDeclaredLifetime) {
  Run("module automatic am; endmodule\n"
      "module static sm; endmodule\n"
      "module dm; endmodule\n"
      "program automatic ap; endprogram\n"
      "interface automatic ai; endinterface\n"
      "interface si; endinterface\n"
      "package automatic pa; parameter int A = 1; endpackage\n"
      "package ps; parameter int B = 2; endpackage\n"
      "module top; am a(); sm s(); dm d(); ap p(); ai i(); si j();\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.a")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.s")), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.d")), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.p")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.i")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top.j")), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("top")), 0);
  ASSERT_NE(By("pa"), nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("pa")), 1);
  ASSERT_NE(By("ps"), nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, By("ps")), 0);
}

TEST_F(LifetimesOfARun, AClassOfARunIsAutomatic) {
  Run("module top; class C; endclass class D extends C; endclass endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, c), 1);
  vpiHandle typespec =
      vpi_handle(vpiClassTypespec,
                 vpi_handle(vpiExtends, Named(vpiClassDefn, By("top"), "D")));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, typespec), 1);
}

TEST_F(LifetimesOfARun, AnAutomaticVariableHasTheAutomaticScheme) {
  Run("module top; task automatic t(); int x; endtask\n"
      "  function int f(); int y; return 0; endfunction\n"
      "  function automatic int g(); return 0; endfunction endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top"), "t");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  vpiHandle g = Named(vpiTaskFunc, By("top"), "g");
  EXPECT_EQ(vpi_get(vpiAllocScheme, Named(vpiVariables, t, "x")),
            vpiAutomaticScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, Named(vpiVariables, f, "y")),
            vpiOtherScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, vpi_handle(vpiReturn, g)),
            vpiAutomaticScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, vpi_handle(vpiReturn, f)), vpiOtherScheme);
}

TEST_F(LifetimesOfARun, AClassObjectHasTheDynamicScheme) {
  Run("module top; class C; int n; static int s; endclass\n"
      "  C c = new; endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(vpi_get(vpiAllocScheme, obj), vpiDynamicScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, Named(vpiVariables, obj, "n")),
            vpiDynamicScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, Named(vpiVariables, obj, "s")),
            vpiOtherScheme);
}

int g_frame_scheme = 0;
int g_thread_scheme = 0;

PLI_INT32 ProbeSchemesCalltf(PLI_BYTE8*) {
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  g_frame_scheme = vpi_get(vpiAllocScheme, frame);
  g_thread_scheme = vpi_get(vpiAllocScheme, vpi_handle(vpiThread, frame));
  return 0;
}

TEST_F(LifetimesOfARun, AFrameAndItsThreadHaveTheAutomaticScheme) {
  g_frame_scheme = 0;
  g_thread_scheme = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeSchemesCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; int r;\n"
      "  function automatic int one(); $probe; return 1; endfunction\n"
      "  initial r = one(); endmodule\n");
  EXPECT_EQ(g_frame_scheme, vpiAutomaticScheme);
  EXPECT_EQ(g_thread_scheme, vpiAutomaticScheme);
}

TEST_F(LifetimesOfARun, ANestedAutomaticModulesTaskIsAutomatic) {
  Run("module top;\n"
      "  module automatic inner; task t(); int x; endtask endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top.i"), "t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, t), 1);
  EXPECT_EQ(vpi_get(vpiAllocScheme, Named(vpiVariables, t, "x")),
            vpiAutomaticScheme);
}

}  // namespace
}  // namespace delta

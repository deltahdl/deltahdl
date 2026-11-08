#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(NettypeDeclarationModel, WithIsNullWithoutResolutionFunction) {
  VpiContext ctx;

  VpiObject nettype;
  nettype.type = vpiNettypeDecl;

  EXPECT_EQ(ctx.Handle(vpiWith, &nettype), nullptr);
}

TEST(NettypeDeclarationModel, WithReachesResolutionFunction) {
  VpiContext ctx;

  VpiObject resolver;
  resolver.type = vpiFunction;

  VpiObject nettype;
  nettype.type = vpiNettypeDecl;
  nettype.nettype_with = &resolver;

  EXPECT_EQ(ctx.Handle(vpiWith, &nettype), &resolver);
}

TEST(NettypeDeclarationModel, NetTypedefAliasReachesAliasedNettype) {
  VpiContext ctx;

  VpiObject base;
  base.type = vpiNettypeDecl;

  VpiObject alias;
  alias.type = vpiNettypeDecl;
  alias.aliased = &base;

  VpiHandle aliased = ctx.Handle(vpiNetTypedefAlias, &alias);
  EXPECT_NE(aliased, nullptr);
  EXPECT_EQ(aliased, &base);
}

TEST(NettypeDeclarationModel, NetTypedefAliasIsNullWhenNotAnAlias) {
  VpiContext ctx;

  VpiObject nettype;
  nettype.type = vpiNettypeDecl;

  EXPECT_EQ(ctx.Handle(vpiNetTypedefAlias, &nettype), nullptr);
}

int g_nettype_decls = 0;
int g_nettype_decls_of_the_annex_type = 0;
std::string g_plain_nettype_name;
std::string g_resolved_nettype_name;
bool g_plain_with_is_null = false;
std::string g_resolution_function_name;

PLI_INT32 ProbeNettypeDeclsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiNetTypedef, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle decl = vpi_scan(itr)) {
    ++g_nettype_decls;
    if (vpi_get(vpiType, decl) == vpiNettypeDecl) {
      ++g_nettype_decls_of_the_annex_type;
    }
    const char* name = vpi_get_str(vpiName, decl);
    vpiHandle with = vpi_handle(vpiWith, decl);
    if (with == nullptr) {
      g_plain_with_is_null = true;
      if (name != nullptr) g_plain_nettype_name = name;
      continue;
    }
    if (name != nullptr) g_resolved_nettype_name = name;
    if (const char* fn = vpi_get_str(vpiName, with)) {
      g_resolution_function_name = fn;
    }
  }
  return 0;
}

TEST(NettypeDeclarationDesign, ADesignsNettypeDeclarationsAreObjects) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_nettype_decls = 0;
  g_nettype_decls_of_the_annex_type = 0;
  g_plain_nettype_name.clear();
  g_resolved_nettype_name.clear();
  g_plain_with_is_null = false;
  g_resolution_function_name.clear();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeNettypeDeclsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  nettype logic plainnt;\n"
      "  nettype logic [7:0] busnt with my_resolve;\n"
      "  plainnt p;\n"
      "  busnt b;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_nettype_decls, 2);
  EXPECT_EQ(g_nettype_decls_of_the_annex_type, 2);
  EXPECT_EQ(g_plain_nettype_name, "plainnt");
  EXPECT_EQ(g_resolved_nettype_name, "busnt");

  EXPECT_TRUE(g_plain_with_is_null);
  EXPECT_EQ(g_resolution_function_name, "my_resolve");
}

class NettypesOfARun : public VpiDesignRun {};

TEST_F(NettypesOfARun, ANettypeReachesTheTypespecOfItsType) {
  Run("module top;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  nettype logic [3:0] bnt;\n"
      "  nettype bnt alias_nt;\n"
      "  nettype nib_t nnt;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle of_bnt = vpi_handle(vpiTypespec, Named(vpiNetTypedef, top, "bnt"));
  ASSERT_NE(of_bnt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_bnt), vpiLogicTypespec);
  EXPECT_NE(vpi_iterate(vpiRange, of_bnt), nullptr);
  EXPECT_EQ(VpiObjectOf(
                vpi_handle(vpiTypespec, Named(vpiNetTypedef, top, "alias_nt"))),
            VpiObjectOf(of_bnt));
  vpiHandle of_nnt = vpi_handle(vpiTypespec, Named(vpiNetTypedef, top, "nnt"));
  ASSERT_NE(of_nnt, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, of_nnt), "nib_t");
}

TEST_F(NettypesOfARun, ANettypeOfAPackageOrUnitTypedefReachesItsTypespec) {
  Run("typedef logic [5:0] unit_t;\n"
      "package pk; typedef bit [2:0] pk_t; endpackage\n"
      "module top; import pk::*;\n"
      "  typedef int other_t;\n"
      "  nettype unit_t a;\n"
      "  nettype pk_t b;\n"
      "  nettype pk::pk_t c;\n"
      "  nettype a d;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const auto kTypespecOf = [top](const char* nettype) {
    return vpi_handle(vpiTypespec, Named(vpiNetTypedef, top, nettype));
  };
  vpiHandle of_a = kTypespecOf("a");
  ASSERT_NE(of_a, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, of_a), "unit_t");
  vpiHandle of_b = kTypespecOf("b");
  ASSERT_NE(of_b, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, of_b), "pk_t");
  EXPECT_EQ(VpiObjectOf(kTypespecOf("c")), VpiObjectOf(of_b));
  EXPECT_EQ(VpiObjectOf(kTypespecOf("d")), VpiObjectOf(of_a));
}

TEST_F(NettypesOfARun, ANestedModulesInstanceDeclaresItsNettypes) {
  Run("module top;\n"
      "  module inner; nettype logic [1:0] pair_t; endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  vpiHandle pair = Named(vpiNetTypedef, By("top.i"), "pair_t");
  ASSERT_NE(pair, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, pair)), vpiLogicTypespec);
}

}  // namespace
}  // namespace delta

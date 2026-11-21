#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

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
      "  function automatic logic [7:0] my_resolve(input logic [7:0] d[]);\n"
      "    logic [7:0] r = 0;\n"
      "    foreach (d[i]) r |= d[i];\n"
      "    return r;\n"
      "  endfunction\n"
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
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  EXPECT_EQ(g_nettype_decls, 2);
  EXPECT_EQ(g_nettype_decls_of_the_annex_type, 2);
  EXPECT_EQ(g_plain_nettype_name, "plainnt");
  EXPECT_EQ(g_resolved_nettype_name, "busnt");

  EXPECT_TRUE(g_plain_with_is_null);
  EXPECT_EQ(g_resolution_function_name, "my_resolve");
}

std::string Resolver(const std::string& header, const std::string& name) {
  return header + " logic [3:0] " + name +
         "(input logic [3:0] d[]);\n"
         "  logic [3:0] r = 0;\n"
         "  foreach (d[i]) r |= d[i];\n"
         "  return r;\n"
         "endfunction\n";
}

class NettypesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Unit() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }
  static std::string KindAndName(vpiHandle decl) {
    if (decl == nullptr) return "(none)";
    const char* name = vpi_get_str(vpiName, decl);
    return std::string(vpi_get(vpiType, decl) == vpiNettypeDecl
                           ? "nettype decl "
                           : "other ") +
           (name == nullptr ? "(null)" : name);
  }
  static std::string Described(vpiHandle obj) {
    if (obj == nullptr) return "(none)";
    const char* name = vpi_get_str(vpiFullName, obj);
    return std::to_string(vpi_get(vpiType, obj)) + " " +
           (name == nullptr ? "(null)" : name);
  }
  static std::string SameObject(vpiHandle reached, vpiHandle expected) {
    if (reached != nullptr && expected != nullptr &&
        VpiObjectOf(reached) == VpiObjectOf(expected)) {
      return "same";
    }
    return Described(reached) + " in place of " + Described(expected);
  }
  static vpiHandle AliasOf(vpiHandle scope, std::string_view name) {
    return vpi_handle(vpiNetTypedefAlias, Named(vpiNetTypedef, scope, name));
  }
  static vpiHandle WithOf(vpiHandle scope, std::string_view name) {
    return vpi_handle(vpiWith, Named(vpiNetTypedef, scope, name));
  }
  static vpiHandle TypespecOf(vpiHandle scope, std::string_view name) {
    return vpi_handle(vpiTypespec, Named(vpiNetTypedef, scope, name));
  }
};

TEST_F(NettypesOfARun, DISABLED_ResolvedNettypeReachesItsScopesOwnFunction) {
  Run("module top;\n" + Resolver("function automatic", "f") +
      "  nettype logic [3:0] rnt with f;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(SameObject(WithOf(top, "rnt"), Named(vpiTaskFunc, top, "f")),
            "same");
}

TEST_F(NettypesOfARun,
       DISABLED_ResolutionFunctionNamedThroughAPackageIsThePackages) {
  Run("package pk;\n" + Resolver("function automatic", "f") +
      "endpackage\n"
      "module top;\n" +
      Resolver("function automatic", "f") +
      "  nettype logic [3:0] pnt with pk::f;\n"
      "endmodule\n");
  EXPECT_EQ(
      SameObject(WithOf(By("top"), "pnt"), Named(vpiTaskFunc, By("pk"), "f")),
      "same");
}

TEST_F(NettypesOfARun, DISABLED_ClassStaticResolutionFunctionIsTheClassMethod) {
  Run("module top;\n"
      "  class C;\n" +
      Resolver("static function", "f") +
      "  endclass\n"
      "  nettype logic [3:0] cnt with C::f;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(SameObject(WithOf(top, "cnt"),
                       Named(vpiMethods, Named(vpiClassDefn, top, "C"), "f")),
            "same");
}

TEST_F(NettypesOfARun, DISABLED_UnitResolutionFunctionIsTheUnitsFunction) {
  Run(Resolver("function automatic", "uf") +
      "module top; nettype logic [3:0] unt with uf; endmodule\n");
  EXPECT_EQ(
      SameObject(WithOf(By("top"), "unt"), Named(vpiTaskFunc, Unit(), "uf")),
      "same");
}

TEST_F(NettypesOfARun,
       DISABLED_PackagesResolvedNettypeReachesThePackagesFunction) {
  Run("package pk;\n" + Resolver("function automatic", "f") +
      "  nettype logic [3:0] pnt with f;\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pk = By("pk");
  EXPECT_EQ(SameObject(WithOf(pk, "pnt"), Named(vpiTaskFunc, pk, "f")), "same");
}

TEST_F(NettypesOfARun, DISABLED_UnitsResolvedNettypeReachesTheUnitsFunction) {
  Run(Resolver("function automatic", "uf") +
      "nettype logic [3:0] unt with uf;\n"
      "module top; endmodule\n");
  EXPECT_EQ(SameObject(WithOf(Unit(), "unt"), Named(vpiTaskFunc, Unit(), "uf")),
            "same");
}

TEST_F(NettypesOfARun, DISABLED_AliasOfAResolvedNettypeReachesItsFunction) {
  Run("module top;\n" + Resolver("function automatic", "f") +
      "  nettype logic [3:0] rnt with f;\n"
      "  nettype rnt al;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(SameObject(WithOf(top, "al"), Named(vpiTaskFunc, top, "f")),
            "same");
}

TEST_F(NettypesOfARun, KeywordTypedNettypeAliasesNothing) {
  Run("module top;\n"
      "  nettype logic [3:0] bnt;\n"
      "  nettype real rnt;\n"
      "  nettype bnt al;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(Named(vpiNetTypedef, top, "bnt"), nullptr);
  ASSERT_NE(Named(vpiNetTypedef, top, "rnt"), nullptr);
  EXPECT_EQ(AliasOf(top, "bnt"), nullptr);
  EXPECT_EQ(AliasOf(top, "rnt"), nullptr);
  EXPECT_EQ(SameObject(AliasOf(top, "al"), Named(vpiNetTypedef, top, "bnt")),
            "same");
}

TEST_F(NettypesOfARun,
       DISABLED_AliasNamedThroughAPackageReachesThePackagesNettype) {
  Run("package pk; nettype logic [4:0] pnt; endpackage\n"
      "module m1; nettype bit pnt; nettype pk::pnt al; endmodule\n"
      "module top; m1 a(); endmodule\n");
  EXPECT_EQ(SameObject(AliasOf(By("top.a"), "al"),
                       Named(vpiNetTypedef, By("pk"), "pnt")),
            "same");
}

TEST_F(NettypesOfARun,
       DISABLED_AliasOfAnImportedNettypeReachesThePackagesNettype) {
  Run("package pk; nettype logic [4:0] pnt; endpackage\n"
      "module top; import pk::*; nettype pnt al; endmodule\n");
  EXPECT_EQ(SameObject(AliasOf(By("top"), "al"),
                       Named(vpiNetTypedef, By("pk"), "pnt")),
            "same");
}

TEST_F(NettypesOfARun, DISABLED_AliasOfAUnitNettypeReachesTheUnitsNettype) {
  Run("nettype logic [1:0] unt;\n"
      "module top; nettype unt al; endmodule\n");
  EXPECT_EQ(
      SameObject(AliasOf(By("top"), "al"), Named(vpiNetTypedef, Unit(), "unt")),
      "same");
}

TEST_F(NettypesOfARun, AliasInAPackageReachesThePackagesNettype) {
  Run("package pk; nettype logic [2:0] pnt; nettype pnt pal; endpackage\n"
      "module top; endmodule\n");
  vpiHandle pk = By("pk");
  EXPECT_EQ(SameObject(AliasOf(pk, "pal"), Named(vpiNetTypedef, pk, "pnt")),
            "same");
}

TEST_F(NettypesOfARun, AliasInTheUnitReachesTheUnitsNettype) {
  Run("nettype bit [1:0] unt; nettype unt ual;\n"
      "module top; endmodule\n");
  EXPECT_EQ(
      SameObject(AliasOf(Unit(), "ual"), Named(vpiNetTypedef, Unit(), "unt")),
      "same");
}

TEST_F(NettypesOfARun, AliasOfAnAliasReachesItsDirectTarget) {
  Run("module top; nettype logic t1; nettype t1 t2; nettype t2 t3; "
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(SameObject(AliasOf(top, "t3"), Named(vpiNetTypedef, top, "t2")),
            "same");
  EXPECT_EQ(SameObject(AliasOf(top, "t2"), Named(vpiNetTypedef, top, "t1")),
            "same");
  EXPECT_EQ(AliasOf(top, "t1"), nullptr);
}

TEST_F(NettypesOfARun, PackagesNettypeIsANettypeDecl) {
  Run("package pk; nettype logic [2:0] pnt; nettype pnt pal; endpackage\n"
      "module top; endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("pk"), "pnt")),
            "nettype decl pnt");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("pk"), "pal")),
            "nettype decl pal");
}

TEST_F(NettypesOfARun, UnitsNettypeIsANettypeDecl) {
  Run("nettype bit [1:0] unt; nettype unt ual;\n"
      "module top; endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, Unit(), "unt")),
            "nettype decl unt");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, Unit(), "ual")),
            "nettype decl ual");
}

TEST_F(NettypesOfARun, AnAliasIsANettypeDeclOfItsOwnName) {
  Run("module top; nettype logic [3:0] bnt; nettype bnt alias_nt; endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("top"), "alias_nt")),
            "nettype decl alias_nt");
}

TEST_F(NettypesOfARun, AnInterfacesNettypeIsANettypeDecl) {
  Run("interface ifc; nettype logic [1:0] int_nt; endinterface\n"
      "module top; ifc i0(); endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("top.i0"), "int_nt")),
            "nettype decl int_nt");
}

TEST_F(NettypesOfARun, AProgramsNettypeIsANettypeDecl) {
  Run("program prg; nettype logic [1:0] prg_nt; endprogram\n"
      "module top; prg p0(); endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("top.p0"), "prg_nt")),
            "nettype decl prg_nt");
}

TEST_F(NettypesOfARun, DISABLED_AGenerateBlocksNettypeIsANettypeDecl) {
  Run("module top;\n"
      "  if (1) begin : g nettype logic [1:0] gen_nt; end\n"
      "endmodule\n");
  EXPECT_EQ(KindAndName(Named(vpiNetTypedef, By("top.g"), "gen_nt")),
            "nettype decl gen_nt");
}

TEST_F(NettypesOfARun, APackageNettypeReachesItsTypespec) {
  Run("package pk; nettype bit [4:1] pnt; endpackage\n"
      "module top; endmodule\n");
  vpiHandle of_pnt = TypespecOf(By("pk"), "pnt");
  ASSERT_NE(of_pnt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_pnt), vpiBitTypespec);
  EXPECT_EQ(BoundsOf(of_pnt), (std::vector<int>{4, 1}));
}

TEST_F(NettypesOfARun, AUnitNettypeReachesItsTypespec) {
  Run("nettype logic [2:0] unt;\n"
      "module top; endmodule\n");
  vpiHandle of_unt = TypespecOf(Unit(), "unt");
  ASSERT_NE(of_unt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_unt), vpiLogicTypespec);
  EXPECT_EQ(BoundsOf(of_unt), (std::vector<int>{2, 0}));
}

TEST_F(NettypesOfARun, DISABLED_AliasNamedThroughAPackageReachesItsTypespec) {
  Run("package pk; nettype logic [4:0] pnt; endpackage\n"
      "module m1; nettype bit pnt; nettype pk::pnt al; endmodule\n"
      "module top; m1 a(); endmodule\n");
  EXPECT_EQ(
      SameObject(TypespecOf(By("top.a"), "al"), TypespecOf(By("pk"), "pnt")),
      "same");
}

TEST_F(NettypesOfARun, DISABLED_AliasOfAnImportedNettypeReachesItsTypespec) {
  Run("package pk; nettype logic [4:0] pnt; endpackage\n"
      "module top; import pk::*; nettype pnt al; endmodule\n");
  EXPECT_EQ(
      SameObject(TypespecOf(By("top"), "al"), TypespecOf(By("pk"), "pnt")),
      "same");
}

TEST_F(NettypesOfARun, AnAggregateNettypeReachesItsAggregateTypespec) {
  Run("module top;\n"
      "  typedef struct { real r; bit b; } st_t;\n"
      "  typedef union { real r; bit [63:0] b; } un_t;\n"
      "  typedef real ar_t[5];\n"
      "  nettype st_t snt;\n"
      "  nettype un_t unt;\n"
      "  nettype ar_t ant;\n"
      "  nettype struct packed { logic [1:0] a; logic b; } pnt;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "snt")), vpiStructTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "unt")), vpiUnionTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "ant")), vpiArrayTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "pnt")), vpiStructTypespec);
}

TEST_F(NettypesOfARun, ARealOrTwoStateNettypeReachesItsTypespec) {
  Run("module top;\n"
      "  nettype real rnt;\n"
      "  nettype shortreal srnt;\n"
      "  nettype int int_nt;\n"
      "  nettype bit [2:0] bnt;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "rnt")), vpiRealTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "srnt")), vpiShortRealTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "int_nt")), vpiIntTypespec);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf(top, "bnt")), vpiBitTypespec);
}

TEST_F(NettypesOfARun, ATypeReferenceNettypeReachesTheReferencedTypespec) {
  Run("module top;\n"
      "  logic [6:0] x;\n"
      "  typedef bit [2:0] three_t;\n"
      "  nettype type(x) xnt;\n"
      "  nettype type(three_t) tnt;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle of_xnt = TypespecOf(top, "xnt");
  ASSERT_NE(of_xnt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_xnt), vpiLogicTypespec);
  EXPECT_EQ(BoundsOf(of_xnt), (std::vector<int>{6, 0}));
  vpiHandle of_tnt = TypespecOf(top, "tnt");
  ASSERT_NE(of_tnt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_tnt), vpiBitTypespec);
  EXPECT_EQ(BoundsOf(of_tnt), (std::vector<int>{2, 0}));
}

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
  EXPECT_EQ(KindAndName(pair), "nettype decl pair_t");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, pair)), vpiLogicTypespec);
}

}  // namespace
}  // namespace delta

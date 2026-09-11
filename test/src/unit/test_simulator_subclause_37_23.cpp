#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.23 Nettype declaration: the VPI object model for a user-defined nettype
// (an object of type vpiNetTypedef). The clause's own normative content is its
// two numbered details, exercised here through the production Handle dispatch:
//   detail 1 - vpiWith reaches the nettype's resolution function, and reports
//              NULL when the nettype has no associated resolution function;
//   detail 2 - vpiNetTypedefAlias reaches the aliased nettype when the nettype
//              is an alias of another nettype declaration, reporting a non-null
//              handle to it.
// The diagram's other edges are dependencies satisfied elsewhere: the name
// (vpiName) is the generic string relation, and the underlying typespec edge is
// owned by the typespec subclauses (§37.25), so neither is re-tested here.

// Detail 1: a nettype declared without an associated resolution function
// reports NULL for vpiWith.
TEST(NettypeDeclarationModel, WithIsNullWithoutResolutionFunction) {
  VpiContext ctx;

  VpiObject nettype;
  nettype.type = vpiNetTypedef;  // no resolution function attached

  EXPECT_EQ(ctx.Handle(vpiWith, &nettype), nullptr);
}

// Detail 1: a nettype that does carry a resolution function reaches it through
// vpiWith - the conditional NULL of detail 1 applies only when there is none.
TEST(NettypeDeclarationModel, WithReachesResolutionFunction) {
  VpiContext ctx;

  VpiObject resolver;
  resolver.type = vpiFunction;

  VpiObject nettype;
  nettype.type = vpiNetTypedef;
  nettype.nettype_with = &resolver;

  EXPECT_EQ(ctx.Handle(vpiWith, &nettype), &resolver);
}

// Detail 2: a nettype that is an alias of another nettype declaration reaches
// the aliased nettype through vpiNetTypedefAlias, which is a non-null handle.
TEST(NettypeDeclarationModel, NetTypedefAliasReachesAliasedNettype) {
  VpiContext ctx;

  VpiObject base;
  base.type = vpiNetTypedef;

  VpiObject alias;
  alias.type = vpiNetTypedef;
  alias.nettype_alias = &base;

  VpiHandle aliased = ctx.Handle(vpiNetTypedefAlias, &alias);
  EXPECT_NE(aliased, nullptr);
  EXPECT_EQ(aliased, &base);
}

// Detail 2: a nettype that is not an alias of another nettype has no aliased
// target, so vpiNetTypedefAlias reports NULL.
TEST(NettypeDeclarationModel, NetTypedefAliasIsNullWhenNotAnAlias) {
  VpiContext ctx;

  VpiObject nettype;
  nettype.type = vpiNetTypedef;  // a primary declaration, not an alias

  EXPECT_EQ(ctx.Handle(vpiNetTypedefAlias, &nettype), nullptr);
}

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
int g_nettype_decls = 0;
std::string g_plain_nettype_name;
std::string g_resolved_nettype_name;
bool g_plain_with_is_null = false;
std::string g_resolution_function_name;

int ProbeNettypeDeclsCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiNetTypedef, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle decl = vpi_scan(itr)) {
    ++g_nettype_decls;
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

// §37.23 against a design. The subclause is about an object a run builds for a
// user-defined nettype, and no pass built one: the two details' rules stood
// over objects a test made, while §37.10 detail 1's vpiNetTypedef iteration
// over an instance that declares two nettypes reached neither of them.
TEST(NettypeDeclarationDesign, ADesignsNettypeDeclarationsAreObjects) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_nettype_decls = 0;
  g_plain_nettype_name.clear();
  g_resolved_nettype_name.clear();
  g_plain_with_is_null = false;
  g_resolution_function_name.clear();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
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
  EXPECT_EQ(g_plain_nettype_name, "plainnt");
  EXPECT_EQ(g_resolved_nettype_name, "busnt");

  // Detail 1, both ways round: the declaration written with no resolution
  // function reports NULL for vpiWith, and the one written with `with
  // my_resolve` reaches the function that names.
  EXPECT_TRUE(g_plain_with_is_null);
  EXPECT_EQ(g_resolution_function_name, "my_resolve");
}

}  // namespace
}  // namespace delta

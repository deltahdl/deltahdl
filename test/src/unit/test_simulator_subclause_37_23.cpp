#include <gtest/gtest.h>

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

}  // namespace
}  // namespace delta

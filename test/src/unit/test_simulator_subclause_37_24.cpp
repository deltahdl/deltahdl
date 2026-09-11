#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.24 Generic interconnect: the VPI object model for a vpiInterconnectArray
// and the vpiInterconnectNet objects it ultimately resolves to. The clause's
// own normative details are exercised here:
//   detail 1 - the typespec an interconnect net connects to decides which
//              subobject iteration it supports: a packed/unpacked array
//              typespec supports vpiElement (the net's array elements); a
//              packed/unpacked struct typespec supports vpiMember (the net's
//              struct members);
//   detail 2 - vpiElement on an interconnect array reaches its subelements one
//              dimension level at a time, each itself an interconnect array (a
//              further dimension) or a leaf interconnect net.
// The vpiPacked property is owned by §37.26, the range relations by §37.22, and
// the typespec relation itself by §37.25/§37.16 - the cited dependencies - so
// they are not re-tested here.

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

// Detail 2: vpiElement on an interconnect array returns its subelements - here
// leaf interconnect nets - one level at a time, skipping a child that is not an
// interconnect subobject (the range edge's expr) and preserving order.
TEST(GenericInterconnectModel, ArrayElementIterationReachesLeafNets) {
  VpiContext ctx;

  VpiObject net0;
  net0.type = vpiInterconnectNet;
  VpiObject range_expr;  // not an interconnect subobject: must be skipped
  range_expr.type = vpiOperation;
  VpiObject net1;
  net1.type = vpiInterconnectNet;

  VpiObject array;
  array.type = vpiInterconnectArray;
  array.children = {&net0, &range_expr, &net1};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &array));
  ASSERT_EQ(elems.size(), 2u);
  EXPECT_EQ(elems[0], &net0);
  EXPECT_EQ(elems[1], &net1);
}

// Detail 2: for a multidimensional interconnect array, vpiElement retrieves
// elements that are themselves interconnect arrays - one dimension level at a
// time, leaving deeper levels to a further vpiElement step.
TEST(GenericInterconnectModel, ArrayElementIterationReachesArraysForMultiDim) {
  VpiContext ctx;

  VpiObject sub0;
  sub0.type = vpiInterconnectArray;
  VpiObject sub1;
  sub1.type = vpiInterconnectArray;

  VpiObject array;
  array.type = vpiInterconnectArray;
  array.children = {&sub0, &sub1};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &array));
  ASSERT_EQ(elems.size(), 2u);
  EXPECT_EQ(elems[0], &sub0);
  EXPECT_EQ(elems[1], &sub1);
}

// Detail 1: an interconnect net whose connected typespec is a packed/unpacked
// array supports vpiElement, which reaches the net's per-element interconnect
// nets; the typespec child itself is not an interconnect subobject and is left
// out.
TEST(GenericInterconnectModel, NetElementIterationWhenTypespecIsArray) {
  VpiContext ctx;

  VpiObject typespec;
  typespec.type = vpiArrayTypespec;
  VpiObject elem0;
  elem0.type = vpiInterconnectNet;
  VpiObject elem1;
  elem1.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&typespec, &elem0, &elem1};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &net));
  ASSERT_EQ(elems.size(), 2u);
  EXPECT_EQ(elems[0], &elem0);
  EXPECT_EQ(elems[1], &elem1);
}

// Detail 1: vpiElement does not apply to an interconnect net whose connected
// typespec is a struct - there are no array elements to reach, so the iteration
// yields nothing even though the net carries interconnect subobjects (which a
// vpiMember iteration would reach instead).
TEST(GenericInterconnectModel, NetElementIterationEmptyWhenTypespecIsStruct) {
  VpiContext ctx;

  VpiObject typespec;
  typespec.type = vpiStructTypespec;
  VpiObject member0;
  member0.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&typespec, &member0};

  EXPECT_EQ(ctx.Iterate(vpiElement, &net), nullptr);
}

// Detail 1: an interconnect net whose connected typespec is a packed/unpacked
// struct supports vpiMember, which reaches the net's per-member interconnect
// nets; the typespec child is left out.
TEST(GenericInterconnectModel, NetMemberIterationWhenTypespecIsStruct) {
  VpiContext ctx;

  VpiObject typespec;
  typespec.type = vpiStructTypespec;
  VpiObject member0;
  member0.type = vpiInterconnectNet;
  VpiObject member1;
  member1.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&typespec, &member0, &member1};

  std::vector<VpiHandle> members = Collect(ctx, ctx.Iterate(vpiMember, &net));
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0], &member0);
  EXPECT_EQ(members[1], &member1);
}

// Detail 1: vpiMember does not apply to an interconnect net whose connected
// typespec is an array - those subobjects are array elements (reached by
// vpiElement), not struct members, so the member iteration yields nothing.
TEST(GenericInterconnectModel, NetMemberIterationEmptyWhenTypespecIsArray) {
  VpiContext ctx;

  VpiObject typespec;
  typespec.type = vpiPackedArrayTypespec;
  VpiObject elem0;
  elem0.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&typespec, &elem0};

  EXPECT_EQ(ctx.Iterate(vpiMember, &net), nullptr);
}

// Detail 2 (scope guard): the special interconnect vpiElement handling is keyed
// on an interconnect parent. A vpiElement iteration over an ordinary object
// that merely has interconnect-typed children falls through to the generic
// same-type match and so reaches nothing.
TEST(GenericInterconnectModel, ElementIterationDoesNotApplyToNonInterconnect) {
  VpiContext ctx;

  VpiObject child;
  child.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&child};

  EXPECT_EQ(ctx.Iterate(vpiElement, &net), nullptr);
}

// Detail 1 (edge): whether an interconnect net supports vpiElement or vpiMember
// is decided by the data type of the typespec it connects to. An interconnect
// net that carries no typespec at all therefore supports neither iteration,
// even when it holds interconnect subobjects - both relations reach nothing.
TEST(GenericInterconnectModel, NetSubobjectIterationEmptyWhenNoTypespec) {
  VpiContext ctx;

  VpiObject subobject;
  subobject.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&subobject};  // no typespec child to classify

  EXPECT_EQ(ctx.Iterate(vpiElement, &net), nullptr);
  EXPECT_EQ(ctx.Iterate(vpiMember, &net), nullptr);
}

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
int g_interconnect_nets = 0;
std::string g_interconnect_net_name;
bool g_reached_from_the_port = false;

int ProbeInterconnectCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;

  vpiHandle itr = vpi_iterate(vpiInterconnectNet, mod);
  if (itr != nullptr) {
    while (vpiHandle net = vpi_scan(itr)) {
      ++g_interconnect_nets;
      if (const char* name = vpi_get_str(vpiName, net)) {
        g_interconnect_net_name = name;
      }
    }
  }

  // §37.14 detail 10: the connection inside the instance. For a generic
  // interconnect port that is the interconnect net the port stands for. The
  // port is reached by iteration rather than by name, because the port and the
  // net it stands for are the one name the declaration wrote.
  vpiHandle ports = vpi_iterate(vpiPort, mod);
  if (ports == nullptr) return 0;
  while (vpiHandle port = vpi_scan(ports)) {
    vpiHandle low = vpi_handle(vpiLowConn, port);
    if (low != nullptr && vpi_get(vpiType, low) == vpiInterconnectNet) {
      g_reached_from_the_port = true;
    }
  }
  return 0;
}

// §37.24 against a design. The subclause's model is about interconnect objects
// and no pass built one, so a design declaring a generic interconnect port had
// no interconnect net at all and every rule of the clause stood over objects a
// test had made for itself.
TEST(GenericInterconnectDesign, AnInterconnectPortStandsUpAnInterconnectNet) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_interconnect_nets = 0;
  g_interconnect_net_name.clear();
  g_reached_from_the_port = false;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &ProbeInterconnectCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m(interconnect ic);\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_interconnect_nets, 1);
  EXPECT_EQ(g_interconnect_net_name, "ic");
  EXPECT_TRUE(g_reached_from_the_port);
}

}  // namespace
}  // namespace delta

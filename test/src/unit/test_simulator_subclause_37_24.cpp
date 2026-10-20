#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

PLI_INT32 ProbeInterconnectCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
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
  data.tfname = VpiText("$probe");
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

// D1: a packed array is an array data type as an unpacked one is, and a union
// bears members as a struct does.
TEST(GenericInterconnectModel, PackedArraysAndUnionsSelectTheirRelation) {
  EXPECT_TRUE(VpiIsInterconnectArrayDataTypespec(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsInterconnectArrayDataTypespec(vpiPackedArrayTypespec));
  EXPECT_FALSE(VpiIsInterconnectArrayDataTypespec(vpiStructTypespec));
  EXPECT_TRUE(VpiIsInterconnectStructDataTypespec(vpiStructTypespec));
  EXPECT_TRUE(VpiIsInterconnectStructDataTypespec(vpiUnionTypespec));
  EXPECT_FALSE(VpiIsInterconnectStructDataTypespec(vpiArrayTypespec));
}

// A design run with a PLI application registered, its generic interconnects
// read back once the run is over.
class InterconnectsOfARun : public VpiDesignRun {
 protected:
  // The object a port of the instance `instance` connects inside it.
  static vpiHandle LowConnOf(const char* instance, const char* port) {
    vpiHandle handle = Named(vpiPort, By(instance), port);
    return handle != nullptr ? vpi_handle(vpiLowConn, handle) : nullptr;
  }

  // The integer value of a constant, -1 where there is none.
  static int IntOf(vpiHandle constant) {
    if (constant == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(constant, &value);
    return value.value.integer;
  }

  // The bounds of each range `array` reaches through vpiRange, "left:right".
  static std::vector<std::string> RangesOf(vpiHandle array) {
    std::vector<std::string> ranges;
    for (vpiHandle range : ObjectsOf(vpiRange, array)) {
      ranges.push_back(std::to_string(IntOf(vpi_handle(vpiLeftRange, range))) +
                       ":" +
                       std::to_string(IntOf(vpi_handle(vpiRightRange, range))));
    }
    return ranges;
  }

  // The bounds `array` reaches through vpiLeftRange and vpiRightRange.
  static std::string BoundsOf(vpiHandle array) {
    return std::to_string(IntOf(vpi_handle(vpiLeftRange, array))) + ":" +
           std::to_string(IntOf(vpi_handle(vpiRightRange, array)));
  }

  // The name of the typespec `obj` reaches, "(none)" where it reaches none.
  static std::string TypespecNameOf(vpiHandle obj) {
    vpiHandle typespec = vpi_handle(vpiTypespec, obj);
    if (typespec == nullptr) return "(none)";
    const char* name = vpi_get_str(vpiName, typespec);
    return name != nullptr ? name : "";
  }
};

// §37.24 (figure): a generic interconnect a module's body declares is an
// interconnect net, and one with an unpacked dimension an interconnect array
// whose vpiElement iteration reaches an interconnect net per index (detail 2),
// and whose vpiSize is that number.
TEST_F(InterconnectsOfARun, ABodyInterconnectIsANetOrAnArray) {
  Run("module top; interconnect ic; interconnect ia [0:1]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.ic")), vpiInterconnectNet);
  vpiHandle array = By("top.ia");
  EXPECT_EQ(vpi_get(vpiType, array), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiSize, array), 2);
  EXPECT_EQ(KindsOf(vpiElement, array),
            (std::vector<int>{vpiInterconnectNet, vpiInterconnectNet}));
}

// §37.24 details 1 and 2: an interconnect port with unpacked dimensions stands
// for an interconnect array, whose vpiElement iteration reaches one dimension
// at a time, a descending dimension as an ascending one.
TEST_F(InterconnectsOfARun, AnInterconnectPortArrayReachesOneDimensionAtATime) {
  Run("module m(interconnect ip [1:0][0:2]); endmodule\n"
      "module top; m u(); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.u"), "ip");
  ASSERT_NE(port, nullptr);
  vpiHandle array = vpi_handle(vpiLowConn, port);
  ASSERT_NE(array, nullptr);
  EXPECT_EQ(vpi_get(vpiType, array), vpiInterconnectArray);
  EXPECT_EQ(KindsOf(vpiElement, array),
            (std::vector<int>{vpiInterconnectArray, vpiInterconnectArray}));
  vpiHandle it = vpi_iterate(vpiElement, array);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(KindsOf(vpiElement, vpi_scan(it)),
            std::vector<int>(3, vpiInterconnectNet));
}

// §37.24 detail 2: a body interconnect array of two dimensions reaches an
// interconnect array per index of the first, and each of those an interconnect
// net per index of the second (#7081).
TEST_F(InterconnectsOfARun, ABodyInterconnectArraysLeavesAreInterconnectNets) {
  Run("module top; interconnect n [0:1][2:0]; endmodule\n");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, By("top.n"));
  ASSERT_EQ(kRows.size(), 2u);
  for (vpiHandle row : kRows) {
    EXPECT_EQ(vpi_get(vpiType, row), vpiInterconnectArray);
    EXPECT_EQ(KindsOf(vpiElement, row),
              std::vector<int>(3, vpiInterconnectNet));
  }
  EXPECT_EQ(NamesOf(vpiElement, kRows[1]),
            (std::vector<std::string>{"n[1][0]", "n[1][1]", "n[1][2]"}));
}

// §37.24 (figure): an interconnect array reaches a range per dimension it
// holds through vpiRange, and the bounds of its first through vpiLeftRange and
// vpiRightRange; each of its interconnect arrays holds the dimensions after
// that one, and an interconnect port's array its own (#7078).
TEST_F(InterconnectsOfARun, AnInterconnectArrayReachesItsRangesAndBounds) {
  Run("module m(interconnect ip [2:0]); endmodule\n"
      "module top; interconnect ia [0:1][3:1]; m u(); endmodule\n");
  vpiHandle array = By("top.ia");
  EXPECT_EQ(RangesOf(array), (std::vector<std::string>{"0:1", "3:1"}));
  EXPECT_EQ(BoundsOf(array), "0:1");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, array);
  ASSERT_EQ(kRows.size(), 2u);
  EXPECT_EQ(RangesOf(kRows[0]), (std::vector<std::string>{"3:1"}));
  EXPECT_EQ(BoundsOf(kRows[0]), "3:1");
  vpiHandle port_array = LowConnOf("top.u", "ip");
  ASSERT_NE(port_array, nullptr);
  EXPECT_EQ(RangesOf(port_array), (std::vector<std::string>{"2:0"}));
  EXPECT_EQ(BoundsOf(port_array), "2:0");
}

// §37.24 (figure) with §6.6.8: an interconnect declared with a packed dimension
// is a packed interconnect array, of an interconnect net per index; with an
// unpacked dimension too, it is an interconnect array of those, which is not
// packed. A port so declared stands for one as a body declaration does (#7079).
TEST_F(InterconnectsOfARun, APackedInterconnectIsAPackedInterconnectArray) {
  Run("module m(interconnect [1:0] p); endmodule\n"
      "module top; interconnect [3:0] w; interconnect [1:0] v [0:2];\n"
      "  m u();\n"
      "endmodule\n");
  vpiHandle w = By("top.w");
  EXPECT_EQ(vpi_get(vpiType, w), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiPacked, w), 1);
  EXPECT_EQ(vpi_get(vpiSize, w), 4);
  EXPECT_EQ(BoundsOf(w), "3:0");
  EXPECT_EQ(KindsOf(vpiElement, w), std::vector<int>(4, vpiInterconnectNet));
  vpiHandle v = By("top.v");
  EXPECT_EQ(vpi_get(vpiType, v), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiPacked, v), 0);
  EXPECT_EQ(RangesOf(v), (std::vector<std::string>{"0:2"}));
  const std::vector<vpiHandle> kWords = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kWords.size(), 3u);
  EXPECT_EQ(vpi_get(vpiType, kWords[2]), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiPacked, kWords[2]), 1);
  EXPECT_EQ(NamesOf(vpiElement, kWords[2]),
            (std::vector<std::string>{"v[2][0]", "v[2][1]"}));
  vpiHandle p = LowConnOf("top.u", "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(vpi_get(vpiType, p), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiPacked, p), 1);
  EXPECT_EQ(KindsOf(vpiElement, p), std::vector<int>(2, vpiInterconnectNet));
}

// §37.24 (figure) with §23.3.3.7.1: a body interconnect a port connects is an
// interconnect net still, though the run merged it with the port's wor net
// (#7386).
TEST_F(InterconnectsOfARun, AConnectedBodyInterconnectStaysAnInterconnectNet) {
  Run("module sink(inout wor r); endmodule\n"
      "module top; interconnect c; sink v(c); endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.c")), vpiInterconnectNet);
}

// §37.24 detail 1: an interconnect net's typespec is that of the net it is
// connected to - the instantiation's net for an interconnect port, and the
// port's net inside the instance for a body interconnect - and one connected
// to no net reaches none (#7080).
TEST_F(InterconnectsOfARun, AnInterconnectNetTakesTheTypespecOfItsNet) {
  Run("typedef logic [7:0] byte_t;\n"
      "module leaf(interconnect p); endmodule\n"
      "module sink(input byte_t q); endmodule\n"
      "module top; wire byte_t w; interconnect c;\n"
      "  leaf u(w); sink v(c); leaf x();\n"
      "endmodule\n");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.u", "p")), "byte_t");
  EXPECT_EQ(TypespecNameOf(By("top.c")), "byte_t");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.x", "p")), "(none)");
}

// §37.24 detail 1 with §6.6.8: an interconnect net connected only to another
// interconnect net is connected to no net of a data type, so neither reaches a
// typespec.
TEST_F(InterconnectsOfARun, AnInterconnectJoinedToAnInterconnectHasNoTypespec) {
  Run("module leaf(interconnect p); endmodule\n"
      "module top; interconnect c; leaf u(c); endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.c")), vpiInterconnectNet);
  EXPECT_EQ(TypespecNameOf(By("top.c")), "(none)");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.u", "p")), "(none)");
}

// §37.24 (figure) with §23.4: a nested module's interconnect array is shaped
// as any other, and the net a nested module's assignment writes of its
// enclosing module stands up no object of its own under the instance.
TEST_F(InterconnectsOfARun,
       ANestedModulesInterconnectIsShapedBesideAnOuterNet) {
  Run("module top;\n"
      "  wire w;\n"
      "  module M; assign w = 1'b1; interconnect n [0:1]; endmodule\n"
      "  M m();\n"
      "endmodule\n");
  vpiHandle n = By("top.m.n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiType, n), vpiInterconnectArray);
  EXPECT_EQ(KindsOf(vpiElement, n), std::vector<int>(2, vpiInterconnectNet));
  EXPECT_EQ(By("top.m.w"), nullptr);
}

// §37.24 detail 1: an interconnect net connected to a net of a packed array
// reaches an interconnect net per element of it through vpiElement, in the
// order its range runs, and one connected to a net of a struct an interconnect
// net per member through vpiMember, each taking the typespec of its element or
// member and named under the interconnect's own full name (#7385).
TEST_F(InterconnectsOfARun, AnInterconnectNetHasTheElementsOrMembersOfItsType) {
  Run("typedef struct packed { logic a; logic [1:0] b; } s_t;\n"
      "module leaf(interconnect p, interconnect q, interconnect r);\n"
      "endmodule\n"
      "module sink(input s_t d); endmodule\n"
      "module top; wire s_t [2:0] w; wire s_t s; wire s_t [0:1] z;\n"
      "  interconnect c; leaf u(w, s, z); sink v(c);\n"
      "endmodule\n");
  vpiHandle p = LowConnOf("top.u", "p");
  ASSERT_NE(p, nullptr);
  const std::vector<vpiHandle> kElements = ObjectsOf(vpiElement, p);
  ASSERT_EQ(kElements.size(), 3u);
  EXPECT_STREQ(vpi_get_str(vpiName, kElements[0]), "p[2]");
  EXPECT_EQ(vpi_get(vpiType, kElements[0]), vpiInterconnectNet);
  EXPECT_EQ(TypespecNameOf(kElements[0]), "s_t");
  EXPECT_EQ(NamesOf(vpiMember, kElements[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_TRUE(ObjectsOf(vpiMember, p).empty());
  vpiHandle q = LowConnOf("top.u", "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(NamesOf(vpiMember, q), (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(KindsOf(vpiMember, q), std::vector<int>(2, vpiInterconnectNet));
  EXPECT_TRUE(ObjectsOf(vpiElement, q).empty());
  vpiHandle r = LowConnOf("top.u", "r");
  ASSERT_NE(r, nullptr);
  const std::vector<vpiHandle> kRising = ObjectsOf(vpiElement, r);
  ASSERT_EQ(kRising.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, kRising[0]), "r[0]");
  vpiHandle member = Named(vpiMember, By("top.c"), "b");
  ASSERT_NE(member, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, member), "top.c.b");
}

}  // namespace
}  // namespace delta

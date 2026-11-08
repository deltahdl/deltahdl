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

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

TEST(GenericInterconnectModel, ArrayElementIterationReachesLeafNets) {
  VpiContext ctx;

  VpiObject net0;
  net0.type = vpiInterconnectNet;
  VpiObject range_expr;
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

TEST(GenericInterconnectModel, ElementIterationDoesNotApplyToNonInterconnect) {
  VpiContext ctx;

  VpiObject child;
  child.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&child};

  EXPECT_EQ(ctx.Iterate(vpiElement, &net), nullptr);
}

TEST(GenericInterconnectModel, NetSubobjectIterationEmptyWhenNoTypespec) {
  VpiContext ctx;

  VpiObject subobject;
  subobject.type = vpiInterconnectNet;

  VpiObject net;
  net.type = vpiInterconnectNet;
  net.children = {&subobject};

  EXPECT_EQ(ctx.Iterate(vpiElement, &net), nullptr);
  EXPECT_EQ(ctx.Iterate(vpiMember, &net), nullptr);
}

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

TEST(GenericInterconnectModel, PackedArraysAndUnionsSelectTheirRelation) {
  EXPECT_TRUE(VpiIsInterconnectArrayDataTypespec(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsInterconnectArrayDataTypespec(vpiPackedArrayTypespec));
  EXPECT_FALSE(VpiIsInterconnectArrayDataTypespec(vpiStructTypespec));
  EXPECT_TRUE(VpiIsInterconnectStructDataTypespec(vpiStructTypespec));
  EXPECT_TRUE(VpiIsInterconnectStructDataTypespec(vpiUnionTypespec));
  EXPECT_FALSE(VpiIsInterconnectStructDataTypespec(vpiArrayTypespec));
}

class InterconnectsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle LowConnOf(const char* instance, const char* port) {
    vpiHandle handle = Named(vpiPort, By(instance), port);
    return handle != nullptr ? vpi_handle(vpiLowConn, handle) : nullptr;
  }

  static int IntOf(vpiHandle constant) {
    if (constant == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(constant, &value);
    return value.value.integer;
  }

  static std::vector<std::string> RangesOf(vpiHandle array) {
    std::vector<std::string> ranges;
    for (vpiHandle range : ObjectsOf(vpiRange, array)) {
      ranges.push_back(std::to_string(IntOf(vpi_handle(vpiLeftRange, range))) +
                       ":" +
                       std::to_string(IntOf(vpi_handle(vpiRightRange, range))));
    }
    return ranges;
  }

  static std::string BoundsOf(vpiHandle array) {
    return std::to_string(IntOf(vpi_handle(vpiLeftRange, array))) + ":" +
           std::to_string(IntOf(vpi_handle(vpiRightRange, array)));
  }

  static std::string TypespecNameOf(vpiHandle obj) {
    vpiHandle typespec = vpi_handle(vpiTypespec, obj);
    if (typespec == nullptr) return "(none)";
    const char* name = vpi_get_str(vpiName, typespec);
    return name != nullptr ? name : "";
  }
};

TEST_F(InterconnectsOfARun, ABodyInterconnectIsANetOrAnArray) {
  Run("module top; interconnect ic; interconnect ia [0:1]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.ic")), vpiInterconnectNet);
  vpiHandle array = By("top.ia");
  EXPECT_EQ(vpi_get(vpiType, array), vpiInterconnectArray);
  EXPECT_EQ(vpi_get(vpiSize, array), 2);
  EXPECT_EQ(KindsOf(vpiElement, array),
            (std::vector<int>{vpiInterconnectNet, vpiInterconnectNet}));
}

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

TEST_F(InterconnectsOfARun, AConnectedBodyInterconnectStaysAnInterconnectNet) {
  Run("module sink(inout wor r); endmodule\n"
      "module top; interconnect c; sink v(c); endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.c")), vpiInterconnectNet);
}

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

TEST_F(InterconnectsOfARun, AnInterconnectPortsNetIsTheOneItsNameReaches) {
  Run("module sink(inout tri q); endmodule\n"
      "module mid(interconnect p); sink s(p); endmodule\n"
      "module top; interconnect c; mid m(c); endmodule\n");
  vpiHandle low = LowConnOf("top.m", "p");
  ASSERT_NE(low, nullptr);
  EXPECT_EQ(vpi_get(vpiType, low), vpiInterconnectNet);
  vpiHandle port = Named(vpiPort, By("top.m.s"), "q");
  ASSERT_NE(port, nullptr);
  EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiHighConn, port), low), 1);
}

TEST_F(InterconnectsOfARun, AnInterconnectChainTakesTheTypespecItReaches) {
  Run("typedef logic [7:0] byte_t;\n"
      "module sink(input byte_t q); endmodule\n"
      "module mid(interconnect p); sink s(p); endmodule\n"
      "module top; interconnect c; mid m(c); endmodule\n");
  EXPECT_EQ(TypespecNameOf(By("top.c")), "byte_t");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.m", "p")), "byte_t");
}

TEST_F(InterconnectsOfARun, AnInterconnectChainsDeadEndTakesTheTypespec) {
  Run("typedef logic [7:0] byte_t;\n"
      "module leaf(interconnect r); endmodule\n"
      "module mid(interconnect p); leaf l(p); endmodule\n"
      "module sink(input byte_t q); endmodule\n"
      "module top; interconnect c; mid m(c); sink v(c); endmodule\n");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.m.l", "r")), "byte_t");
  EXPECT_EQ(TypespecNameOf(LowConnOf("top.m", "p")), "byte_t");
  EXPECT_EQ(TypespecNameOf(By("top.c")), "byte_t");
}

}  // namespace
}  // namespace delta

#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiObjectTypeProperty : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(VpiObjectTypeProperty, GetTypeReturnsTheObjectTypeConstant) {
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&net)), vpiNet);

  VpiObject mod;
  mod.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&mod)), vpiModule);
}

TEST_F(VpiObjectTypeProperty, GetStrTypeReturnsTheTypeConstantName) {
  VpiObject net;
  net.type = vpiNet;
  const char* net_name = vpi_get_str(vpiType, VpiHandleOf(&net));
  ASSERT_NE(net_name, nullptr);
  EXPECT_EQ(std::string(net_name), "vpiNet");

  VpiObject mod;
  mod.type = vpiModule;
  const char* mod_name = vpi_get_str(vpiType, VpiHandleOf(&mod));
  ASSERT_NE(mod_name, nullptr);
  EXPECT_EQ(std::string(mod_name), "vpiModule");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeYieldsNoNameForAnUndefinedType) {
  VpiObject odd;
  odd.type = 9999;
  EXPECT_EQ(vpi_get_str(vpiType, VpiHandleOf(&odd)), nullptr);
}

std::string TypeNameOf(int type) {
  VpiObject obj;
  obj.type = type;
  const char* name = vpi_get_str(vpiType, VpiHandleOf(&obj));
  return name == nullptr ? "" : name;
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesTheFirstAnnexKType) {
  EXPECT_EQ(TypeNameOf(vpiAlways), "vpiAlways");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAMemory) {
  EXPECT_EQ(TypeNameOf(vpiMemory), "vpiMemory");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAnIntVar) {
  EXPECT_EQ(TypeNameOf(vpiIntVar), "vpiIntVar");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAGenScope) {
  EXPECT_EQ(TypeNameOf(vpiGenScope), "vpiGenScope");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAClassDefn) {
  EXPECT_EQ(TypeNameOf(vpiClassDefn), "vpiClassDefn");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesTheLastAnnexMType) {
  EXPECT_EQ(TypeNameOf(vpiLetExpr), "vpiLetExpr");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAVarBitByItsAnnexKSpelling) {
  EXPECT_EQ(TypeNameOf(vpiVarBit), "vpiRegBit");
}

TEST_F(VpiObjectTypeProperty, GetReturnsAnAdditionalTypePropertyConstant) {
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiAddOp;

  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&op)), vpiAddOp);
}

TEST_F(VpiObjectTypeProperty, GetReturnsThePrimTypeAdditionalProperty) {
  VpiObject seq;
  seq.type = vpiPrimitive;
  seq.prim_type = vpiSeqPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(&seq)), vpiSeqPrim);

  VpiObject comb;
  comb.type = vpiPrimitive;
  comb.prim_type = vpiCombPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(&comb)), vpiCombPrim);
}

TEST_F(VpiObjectTypeProperty, GetReturnsTheDelayTypeAdditionalProperty) {
  VpiObject mod_path;
  mod_path.type = vpiModPath;
  mod_path.delay_type = vpiModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&mod_path)), vpiModPathDelay);

  VpiObject inter_mod;
  inter_mod.type = vpiInterModPath;
  inter_mod.delay_type = vpiInterModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&inter_mod)),
            vpiInterModPathDelay);
}

TEST_F(VpiObjectTypeProperty, GetStrReturnsAnAdditionalTypePropertyName) {
  VpiObject add;
  add.type = vpiOperation;
  add.op_type = vpiAddOp;
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&add)), vpiAddOp);
  const char* add_name = vpi_get_str(vpiOpType, VpiHandleOf(&add));
  ASSERT_NE(add_name, nullptr);
  EXPECT_EQ(std::string(add_name), "vpiAddOp");

  VpiObject shift;
  shift.type = vpiOperation;
  shift.op_type = vpiLShiftOp;
  const char* shift_name = vpi_get_str(vpiOpType, VpiHandleOf(&shift));
  ASSERT_NE(shift_name, nullptr);
  EXPECT_EQ(std::string(shift_name), "vpiLShiftOp");
}

TEST_F(VpiObjectTypeProperty,
       GetStrAdditionalTypeYieldsNoNameForUnmodelledValue) {
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = 0;

  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&op)), 0);
  EXPECT_EQ(vpi_get_str(vpiOpType, VpiHandleOf(&op)), nullptr);
}

TEST_F(VpiObjectTypeProperty, GetStrNamesTheOperatorsAnnexMAdds) {
  const struct {
    int op_type;
    const char* name;
  } kOperators[] = {{vpiMinusOp, "vpiMinusOp"},
                    {vpiCastOp, "vpiCastOp"},
                    {vpiWildEqOp, "vpiWildEqOp"},
                    {vpiStreamLROp, "vpiStreamLROp"},
                    {vpiInsideOp, "vpiInsideOp"}};
  for (const auto& op : kOperators) {
    VpiObject obj;
    obj.type = vpiOperation;
    obj.op_type = op.op_type;
    const char* name = vpi_get_str(vpiOpType, VpiHandleOf(&obj));
    ASSERT_NE(name, nullptr) << op.name;
    EXPECT_EQ(std::string(name), op.name);
  }
}

TEST_F(VpiObjectTypeProperty, GetStrNamesThePrimitiveDelayAndCheckTypes) {
  VpiObject prim;
  prim.type = vpiPrimitive;
  VpiObject path;
  path.type = vpiModPath;
  VpiObject check;
  check.type = vpiTchk;
  const struct {
    VpiObject* obj;
    int property;
    int* field;
    int value;
    const char* name;
  } kCases[] = {
      {&prim, vpiPrimType, &prim.prim_type, vpiAndPrim, "vpiAndPrim"},
      {&prim, vpiPrimType, &prim.prim_type, vpiCombPrim, "vpiCombPrim"},
      {&path, vpiDelayType, &path.delay_type, vpiModPathDelay,
       "vpiModPathDelay"},
      {&path, vpiDelayType, &path.delay_type, vpiMIPDelay, "vpiMIPDelay"},
      {&check, vpiTchkType, &check.tchk_type, vpiSetup, "vpiSetup"},
      {&check, vpiTchkType, &check.tchk_type, vpiTimeskew, "vpiTimeskew"},
      {&prim, vpiPrimType, &prim.prim_type, 0, nullptr},
      {&path, vpiDelayType, &path.delay_type, 0, nullptr},
      {&check, vpiTchkType, &check.tchk_type, 0, nullptr},
  };
  for (const auto& c : kCases) {
    *c.field = c.value;
    const char* name = vpi_get_str(c.property, VpiHandleOf(c.obj));
    if (c.name == nullptr) {
      EXPECT_EQ(name, nullptr);
      continue;
    }
    ASSERT_NE(name, nullptr) << c.name;
    EXPECT_EQ(std::string(name), c.name);
  }
}

TEST_F(VpiObjectTypeProperty, AnUnresolvedInterconnectNetStaysInterconnect) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject net;
  net.type = vpiInterconnectNet;
  net.parent = &module;
  VpiObject own_port;
  own_port.type = vpiPort;
  own_port.low_conn = &net;
  VpiObject inner;
  inner.type = vpiModule;
  VpiObject inner_port;
  inner_port.type = vpiPort;
  inner_port.high_conn = &net;
  inner.children.push_back(&inner_port);
  module.children = {&own_port, &inner};

  EXPECT_EQ(vpi_get(vpiResolvedNetType, VpiHandleOf(&net)), vpiInterconnect);
  const char* name = vpi_get_str(vpiResolvedNetType, VpiHandleOf(&net));
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "vpiInterconnect");
}

TEST_F(VpiObjectTypeProperty, AnInterconnectNetTakesItsInstancePortsNetType) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject net;
  net.type = vpiInterconnectNet;
  net.parent = &module;
  VpiObject other;
  other.type = vpiNet;
  VpiObject own_port;
  own_port.type = vpiPort;
  own_port.low_conn = &other;
  Net wand;
  wand.type = NetType::kWand;
  VpiObject inner_net;
  inner_net.type = vpiNet;
  inner_net.net = &wand;
  VpiObject other_port;
  other_port.type = vpiPort;
  other_port.high_conn = &other;
  VpiObject inner_port;
  inner_port.type = vpiPort;
  inner_port.high_conn = &net;
  inner_port.low_conn = &inner_net;
  VpiObject inner;
  inner.type = vpiModule;
  inner.children = {&inner_net, &other_port, &inner_port};
  module.children = {&own_port, &inner};

  EXPECT_EQ(vpi_get(vpiResolvedNetType, VpiHandleOf(&net)), vpiWand);
}

TEST_F(VpiObjectTypeProperty, AnInterconnectNetPassesOverNetsOfNoType) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject net;
  net.type = vpiInterconnectNet;
  net.parent = &module;
  VpiObject bare;
  bare.type = vpiNet;
  Net none;
  none.type = NetType::kNone;
  VpiObject typeless;
  typeless.type = vpiNet;
  typeless.net = &none;
  VpiObject inner_ic;
  inner_ic.type = vpiInterconnectNet;
  inner_ic.net = &none;
  Net wand;
  wand.type = NetType::kWand;
  VpiObject leaf_net;
  leaf_net.type = vpiNet;
  leaf_net.net = &wand;
  VpiObject leaf_port;
  leaf_port.type = vpiPort;
  leaf_port.high_conn = &inner_ic;
  leaf_port.low_conn = &leaf_net;
  VpiObject leaf;
  leaf.type = vpiModule;
  leaf.children = {&leaf_port};
  VpiObject back;
  back.type = vpiPort;
  back.high_conn = &net;
  back.low_conn = &inner_ic;
  VpiObject inner;
  inner.type = vpiModule;
  inner.children = {&back, &leaf};
  inner_ic.parent = &inner;
  VpiObject to_bare;
  to_bare.type = vpiPort;
  to_bare.high_conn = &net;
  to_bare.low_conn = &bare;
  VpiObject to_typeless;
  to_typeless.type = vpiPort;
  to_typeless.high_conn = &net;
  to_typeless.low_conn = &typeless;
  VpiObject to_inner;
  to_inner.type = vpiPort;
  to_inner.high_conn = &net;
  to_inner.low_conn = &inner_ic;
  VpiObject holder;
  holder.type = vpiModule;
  holder.children = {&to_bare, &to_typeless, &to_inner};
  module.children = {&holder};

  EXPECT_EQ(vpi_get(vpiResolvedNetType, VpiHandleOf(&net)), vpiWand);
}

TEST_F(VpiObjectTypeProperty, ANetTypeComesFromTheNetAnObjectStandsFor) {
  VpiObject bare;
  bare.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiNetType, VpiHandleOf(&bare)), 0);
  EXPECT_EQ(vpi_get_str(vpiNetType, VpiHandleOf(&bare)), nullptr);

  Net none;
  none.type = NetType::kNone;
  VpiObject typeless;
  typeless.type = vpiNet;
  typeless.net = &none;
  EXPECT_EQ(vpi_get(vpiNetType, VpiHandleOf(&typeless)), vpiNone);
  const char* name = vpi_get_str(vpiNetType, VpiHandleOf(&typeless));
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "vpiNone");

  Net interconnect;
  interconnect.type = NetType::kInterconnect;
  VpiObject generic;
  generic.type = vpiNet;
  generic.net = &interconnect;
  EXPECT_EQ(vpi_get(vpiNetType, VpiHandleOf(&generic)), vpiInterconnect);
}

class ResolvedNetTypesOfARun : public VpiDesignRun {
 protected:
  static std::string Resolved(vpiHandle net) {
    const char* name = vpi_get_str(vpiResolvedNetType, net);
    return std::to_string(vpi_get(vpiResolvedNetType, net)) + " " +
           (name != nullptr ? name : "(none)");
  }
};

TEST_F(ResolvedNetTypesOfARun, AnInterconnectNetTakesTheTypeItIsConnectedTo) {
  Run("module leaf(interconnect p); endmodule\n"
      "module sink(inout wor q); endmodule\n"
      "module top; wand a; wor b; interconnect c;\n"
      "  leaf u1(b); sink u2(c);\n"
      "endmodule\n");
  const std::string kWor = std::to_string(vpiWor) + " vpiWor";
  EXPECT_EQ(Resolved(By("top.a")), std::to_string(vpiWand) + " vpiWand");
  EXPECT_EQ(Resolved(By("top.c")), kWor);
  vpiHandle ports = vpi_iterate(vpiPort, By("top.u1"));
  ASSERT_NE(ports, nullptr);
  vpiHandle port = vpi_scan(ports);
  ASSERT_NE(port, nullptr);
  EXPECT_EQ(Resolved(vpi_handle(vpiLowConn, port)), kWor);
}

TEST_F(ResolvedNetTypesOfARun, AnInterconnectNetTakesItsMergedNetsType) {
  Run("module dut1(inout wire w); endmodule\n"
      "module dut2(inout wand w); endmodule\n"
      "module top; interconnect c; dut1 a(c); dut2 b(c); endmodule\n");
  EXPECT_EQ(Resolved(By("top.c")), std::to_string(vpiWand) + " vpiWand");
}

TEST_F(ResolvedNetTypesOfARun, AnInterconnectChainTakesItsMergedNetsType) {
  Run("module dut1(inout wire w); endmodule\n"
      "module dut2(inout wand w); endmodule\n"
      "module mid(interconnect p); dut1 a(p); dut2 b(p); endmodule\n"
      "module top; interconnect c; mid m(c); endmodule\n");
  const std::string kWand = std::to_string(vpiWand) + " vpiWand";
  EXPECT_EQ(Resolved(By("top.c")), kWand);
  vpiHandle port = Named(vpiPort, By("top.m"), "p");
  ASSERT_NE(port, nullptr);
  EXPECT_EQ(Resolved(vpi_handle(vpiLowConn, port)), kWand);
}

}  // namespace
}  // namespace delta

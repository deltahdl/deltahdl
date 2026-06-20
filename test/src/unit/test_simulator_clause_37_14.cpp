#include <gtest/gtest.h>

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.14 Ports: the VPI port object model. These tests observe the production
// helpers and dispatch cases in vpi.cpp that apply the clause's numbered
// "Details". The connection relations (vpiHighConn/vpiLowConn) are shared with
// §37.15 Reference objects, and detail 5 ties an interface port's lowConn to a
// ref obj, so those rules are exercised against ref obj handles here too.

// A test fixture that installs the context the public C entry points dispatch
// through, so vpi_get/vpi_get_str/vpi_handle/vpi_get_delays observe the same
// rules a PLI application would.
class PortContext : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1: a port's vpiPortType is one of vpiPort, vpiInterfacePort, or
// vpiModportPort, and which one is decided by the formal, not the actual.
TEST(PortModel, PortTypeValuesAndFormalDerivation) {
  EXPECT_TRUE(VpiIsValidPortType(vpiPort));
  EXPECT_TRUE(VpiIsValidPortType(vpiInterfacePort));
  EXPECT_TRUE(VpiIsValidPortType(vpiModportPort));
  EXPECT_FALSE(VpiIsValidPortType(vpiRefObj));

  // The formal decides the type: a modport formal wins over an interface
  // formal, an interface formal yields an interface port, and anything else is
  // ordinary.
  EXPECT_EQ(VpiPortTypeFromFormal(/*interface=*/false, /*modport=*/false),
            vpiPort);
  EXPECT_EQ(VpiPortTypeFromFormal(/*interface=*/true, /*modport=*/false),
            vpiInterfacePort);
  EXPECT_EQ(VpiPortTypeFromFormal(/*interface=*/true, /*modport=*/true),
            vpiModportPort);
}

TEST_F(PortContext, PortTypeReportedThroughVpiGet) {
  VpiObject port;
  port.type = vpiPort;
  port.port_type = vpiModportPort;
  EXPECT_EQ(vpi_get(vpiPortType, &port), vpiModportPort);
}

// D2: the delay routines are not applicable to an interface port.
TEST(PortModel, DelaysNotApplicableToInterfacePort) {
  EXPECT_FALSE(VpiPortDelaysApplicable(vpiInterfacePort));
  EXPECT_TRUE(VpiPortDelaysApplicable(vpiPort));
  EXPECT_TRUE(VpiPortDelaysApplicable(vpiModportPort));
}

TEST_F(PortContext, GetDelaysOnInterfacePortIsAnError) {
  VpiObject iface_port;
  iface_port.type = vpiPort;
  iface_port.port_type = vpiInterfacePort;

  VpiDelay delay = {};
  delay.no_of_delays = 1;
  vpi_get_delays(&iface_port, &delay);
  // The interface-port guard fires first; its message identifies the ground for
  // the error, distinguishing it from the generic no-of-delays legality check.
  EXPECT_NE(ctx_.LastError().level, 0);
  ASSERT_NE(ctx_.LastError().message, nullptr);
  EXPECT_NE(std::string(ctx_.LastError().message).find("interface port"),
            std::string::npos);
}

// D3, D4, D10: vpiHighConn reaches the higher connection and vpiLowConn the
// lower one; an unconnected instance gives a NULL highConn and a null port
// gives a NULL lowConn.
TEST_F(PortContext, HighConnAndLowConnReachDesignatedConnections) {
  VpiObject high, low;
  VpiObject port;
  port.type = vpiPort;
  port.high_conn = &high;
  port.low_conn = &low;
  EXPECT_EQ(VpiHandleC(vpiHighConn, &port), &high);
  EXPECT_EQ(VpiHandleC(vpiLowConn, &port), &low);

  // D10: an instance with no connection to the port -> NULL highConn.
  VpiObject unconnected;
  unconnected.type = vpiPort;
  unconnected.low_conn = &low;
  EXPECT_EQ(VpiHandleC(vpiHighConn, &unconnected), nullptr);

  // D10: a null port -> NULL lowConn, even if a stored pointer were present.
  VpiObject null_port;
  null_port.type = vpiPort;
  null_port.null_port = true;
  null_port.low_conn = &low;
  EXPECT_EQ(VpiHandleC(vpiLowConn, &null_port), nullptr);
  EXPECT_EQ(VpiLowConn(&null_port), nullptr);
}

// D5: the lowConn of a vpiInterfacePort shall always be a ref obj (§37.15).
TEST(PortModel, InterfacePortLowConnIsRefObj) {
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;

  VpiObject iface_port;
  iface_port.type = vpiPort;
  iface_port.port_type = vpiInterfacePort;
  iface_port.low_conn = &ref_obj;
  EXPECT_TRUE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  // An interface port whose lowConn is some other kind violates the rule.
  VpiObject net;
  net.type = vpiNet;
  iface_port.low_conn = &net;
  EXPECT_FALSE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  // An interface port with no lowConn at all violates the rule.
  iface_port.low_conn = nullptr;
  EXPECT_FALSE(VpiPortLowConnSatisfiesInterfaceRule(&iface_port));

  // The rule does not constrain a non-interface port.
  VpiObject ordinary;
  ordinary.type = vpiPort;
  ordinary.port_type = vpiPort;
  ordinary.low_conn = &net;
  EXPECT_TRUE(VpiPortLowConnSatisfiesInterfaceRule(&ordinary));
}

// D6: vpiScalar/vpiVector report whether the port is 1 bit or more than 1 bit,
// based on the port's own width and nothing about what is connected.
TEST_F(PortContext, ScalarAndVectorFollowPortWidth) {
  EXPECT_TRUE(VpiPortScalar(1));
  EXPECT_FALSE(VpiPortScalar(8));
  EXPECT_FALSE(VpiPortVector(1));
  EXPECT_TRUE(VpiPortVector(8));

  VpiObject scalar_port;
  scalar_port.type = vpiPort;
  scalar_port.size = 1;
  EXPECT_EQ(vpi_get(vpiScalar, &scalar_port), 1);
  EXPECT_EQ(vpi_get(vpiVector, &scalar_port), 0);

  VpiObject vector_port;
  vector_port.type = vpiPort;
  vector_port.size = 16;
  EXPECT_EQ(vpi_get(vpiScalar, &vector_port), 0);
  EXPECT_EQ(vpi_get(vpiVector, &vector_port), 1);
}

// D7: vpiPortIndex and vpiName apply to a whole port but not to a port bit.
TEST_F(PortContext, PortIndexAndNameDoNotApplyToPortBit) {
  EXPECT_TRUE(VpiPortIndexAndNameApply(vpiPort));
  EXPECT_FALSE(VpiPortIndexAndNameApply(vpiPortBit));

  VpiObject port_bit;
  port_bit.type = vpiPortBit;
  port_bit.index = 3;
  port_bit.name = "b";
  EXPECT_EQ(vpi_get(vpiPortIndex, &port_bit), vpiUndefined);
  EXPECT_EQ(vpi_get_str(vpiName, &port_bit), nullptr);
}

// D8: an explicitly named port returns its explicit name; failing that, an
// inferred name if one exists; otherwise NULL.
TEST_F(PortContext, ExplicitNameResolution) {
  EXPECT_STREQ(VpiPortName(/*explicit=*/true, "exp", "inf"), "exp");
  EXPECT_STREQ(VpiPortName(/*explicit=*/false, "exp", "inf"), "inf");
  EXPECT_EQ(VpiPortName(/*explicit=*/false, "", ""), nullptr);
  // No explicit name written, but an inferred name exists.
  EXPECT_STREQ(VpiPortName(/*explicit=*/false, "", "inf"), "inf");

  VpiObject named_port;
  named_port.type = vpiPort;
  named_port.name = "p";
  named_port.explicit_name = true;
  EXPECT_EQ(vpi_get(vpiExplicitName, &named_port), 1);
  EXPECT_STREQ(vpi_get_str(vpiName, &named_port), "p");
}

// D8 (remaining arms, through the vpi_get_str dispatch path): a port that was
// not explicitly named but still has a name returns that name, and a port with
// no name at all returns NULL.
TEST_F(PortContext, PortNameThroughVpiGetStrForInferredAndUnnamed) {
  // Not explicitly named, but a name exists -> that name is returned.
  VpiObject inferred_port;
  inferred_port.type = vpiPort;
  inferred_port.name = "q";
  inferred_port.explicit_name = false;
  EXPECT_EQ(vpi_get(vpiExplicitName, &inferred_port), 0);
  EXPECT_STREQ(vpi_get_str(vpiName, &inferred_port), "q");

  // No name at all -> NULL.
  VpiObject unnamed_port;
  unnamed_port.type = vpiPort;  // name left empty
  EXPECT_EQ(vpi_get_str(vpiName, &unnamed_port), nullptr);
}

// D9: vpiPortIndex gives the port order; the first port has index zero. The
// production CreatePort routine assigns indices in declaration order.
TEST_F(PortContext, PortIndexGivesDeclarationOrder) {
  VpiObject parent;
  parent.type = vpiModule;
  VpiHandle first = ctx_.CreatePort("a", vpiInput, &parent);
  VpiHandle second = ctx_.CreatePort("b", vpiOutput, &parent);
  VpiHandle third = ctx_.CreatePort("c", vpiInput, &parent);
  EXPECT_EQ(vpi_get(vpiPortIndex, first), 0);
  EXPECT_EQ(vpi_get(vpiPortIndex, second), 1);
  EXPECT_EQ(vpi_get(vpiPortIndex, third), 2);
}

// D11: vpiSize for a null port is 0; any other port reports its bit width.
TEST_F(PortContext, NullPortSizeIsZero) {
  EXPECT_EQ(VpiPortSize(/*is_null_port=*/true, 8), 0);
  EXPECT_EQ(VpiPortSize(/*is_null_port=*/false, 8), 8);

  VpiObject null_port;
  null_port.type = vpiPort;
  null_port.null_port = true;
  null_port.size = 8;  // ignored for a null port
  EXPECT_EQ(vpi_get(vpiSize, &null_port), 0);

  VpiObject sized_port;
  sized_port.type = vpiPort;
  sized_port.size = 8;
  EXPECT_EQ(vpi_get(vpiSize, &sized_port), 8);
}

}  // namespace
}  // namespace delta

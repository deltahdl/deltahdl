#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.83 Attribute: the object model diagram draws an attribute object reached
// from a long list of design objects (instances, ports, nets, variables,
// statements, processes, class definitions, and so on) through the vpiParent
// edge, and gives the attribute object four scalar property accesses:
//   -> name              str: vpiName
//   -> On definition     bool: vpiDefAttribute
//   -> value             vpi_get_value()
//   -> definition location  str: vpiDefFile, int: vpiDefLineNo
// There is no BNF and no 'shall' sentence; the clause owns the attribute's
// vpiParent navigation and its three scalar properties beyond the name. The
// attribute's value is reached through vpi_get_value() (§38.34, a dependency),
// and its vpiName is the generic name read shared by every object. These tests
// observe the production code apply each owned edge and property through the
// public vpi_handle/vpi_get/vpi_get_str dispatch paths.

// The fixture installs a context so the public entry points run their real
// dispatch over the test objects.
class Attribute : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Diagram edge (vpiParent): an attribute reaches the design object it is attached
// to. The owning object is one of the many kinds the figure lists; here a net
// carries the attribute, and VpiHandleC(vpiParent, ...) reaches that net rather
// than some other null result.
TEST_F(Attribute, ParentReachesTheOwningObject) {
  VpiObject owning_net;
  owning_net.type = vpiNet;

  VpiObject attr;
  attr.type = vpiAttribute;
  attr.parent = &owning_net;

  EXPECT_EQ(VpiHandleC(vpiParent, &attr), &owning_net);
}

// Figure property (-> name): an attribute reports its name through the generic
// vpi_get_str(vpiName) read. Observed through the public dispatch path.
TEST_F(Attribute, NameReportsTheAttributeName) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.name = "keep";

  EXPECT_STREQ(vpi_get_str(vpiName, &attr), "keep");
}

// Figure property (-> On definition): an attribute reports through
// vpi_get(vpiDefAttribute) whether it was specified on a definition rather than
// on an instance, as 1 when on a definition and 0 otherwise. Driving both states
// exercises the production code reading the stored Boolean.
TEST_F(Attribute, OnDefinitionFlagReportedThroughVpiGet) {
  VpiObject on_definition;
  on_definition.type = vpiAttribute;
  on_definition.def_attribute = true;
  EXPECT_EQ(vpi_get(vpiDefAttribute, &on_definition), 1);

  VpiObject on_instance;
  on_instance.type = vpiAttribute;
  on_instance.def_attribute = false;
  EXPECT_EQ(vpi_get(vpiDefAttribute, &on_instance), 0);
}

// Figure property guard: vpiDefAttribute is drawn only on the attribute object,
// so querying it on any other object kind is not a valid request and the
// production guard returns vpiUndefined rather than handing back a stored field.
TEST_F(Attribute, OnDefinitionFlagIsUndefinedForNonAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiDefAttribute, &not_an_attribute), vpiUndefined);
}

// Figure property (-> definition location, file): an attribute reports the source
// file of its definition through vpi_get_str(vpiDefFile). An attribute with no
// recorded definition file yields null rather than an empty string - the
// empty-name branch distinct from the wrong-kind guard.
TEST_F(Attribute, DefinitionFileReportedThroughVpiGetStr) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_file = "rtl/top.sv";
  EXPECT_STREQ(vpi_get_str(vpiDefFile, &attr), "rtl/top.sv");

  VpiObject no_file;
  no_file.type = vpiAttribute;
  EXPECT_EQ(vpi_get_str(vpiDefFile, &no_file), nullptr);
}

// Figure property (-> definition location, line): an attribute reports the source
// line of its definition through vpi_get(vpiDefLineNo).
TEST_F(Attribute, DefinitionLineReportedThroughVpiGet) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_line_no = 42;
  EXPECT_EQ(vpi_get(vpiDefLineNo, &attr), 42);
}

// Figure property guard: the definition-location properties are drawn only on the
// attribute object, so querying them on any other object kind is not a valid
// request - vpiDefFile yields null and vpiDefLineNo yields vpiUndefined through
// the production guards rather than handing back stored fields.
TEST_F(Attribute, DefinitionLocationPropertiesGuardedToAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiModule;
  EXPECT_EQ(vpi_get_str(vpiDefFile, &not_an_attribute), nullptr);
  EXPECT_EQ(vpi_get(vpiDefLineNo, &not_an_attribute), vpiUndefined);
}

}  // namespace
}  // namespace delta

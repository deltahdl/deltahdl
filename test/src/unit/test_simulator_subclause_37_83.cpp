#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.83 Attribute: the object model diagram draws a dotted enclosure with no
// name holding a long list of design objects - instances, ports, nets,
// variables, statements, processes, class definitions and the rest - and two
// arrows between that enclosure and the `attribute` object. They differ in
// their heads, which §37.4.3 makes the difference between the two routines: the
// one into `attribute` is a double arrow with no tag, so it is
// vpi_iterate(vpiAttribute, obj) over the attributes an object carries, and the
// one back is a single arrow tagged vpiParent, so it is
// vpi_handle(vpiParent, attr) to the one object an attribute is attached to.
// The attribute object carries four property accesses:
//   -> name              str: vpiName
//   -> On definition     bool: vpiDefAttribute
//   -> value             vpi_get_value()
//   -> definition location  str: vpiDefFile, int: vpiDefLineNo
// There is no BNF and no 'shall' sentence. The value is read through
// vpi_get_value() (§38.34, a dependency) and the name through the generic read
// every object shares; the rest the clause owns. These tests observe the
// production code apply both arrows and every property through the public
// vpi_handle/vpi_iterate/vpi_get/vpi_get_str/vpi_get_value dispatch paths.

// The fixture installs a context so the public entry points run their real
// dispatch over the test objects.
class Attribute : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// The single arrow back (vpiParent): an attribute reaches the design object it
// is attached to. The owning object is one of the many kinds the figure lists;
// here a net carries the attribute, and vpi_handle(vpiParent, ...) reaches that
// net rather than some other null result.
TEST_F(Attribute, ParentReachesTheOwningObject) {
  VpiObject owning_net;
  owning_net.type = vpiNet;

  VpiObject attr;
  attr.type = vpiAttribute;
  attr.parent = &owning_net;

  EXPECT_EQ(vpi_handle(vpiParent, &attr), &owning_net);
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
// on an instance, as 1 when on a definition and 0 otherwise. Driving both
// states exercises the production code reading the stored Boolean.
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
// production guard returns vpiUndefined rather than handing back a stored
// field.
TEST_F(Attribute, OnDefinitionFlagIsUndefinedForNonAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiDefAttribute, &not_an_attribute), vpiUndefined);
}

// Figure property (-> definition location, file): an attribute reports the
// source file of its definition through vpi_get_str(vpiDefFile). An attribute
// with no recorded definition file yields null rather than an empty string -
// the empty-name branch distinct from the wrong-kind guard.
TEST_F(Attribute, DefinitionFileReportedThroughVpiGetStr) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_file = "rtl/top.sv";
  EXPECT_STREQ(vpi_get_str(vpiDefFile, &attr), "rtl/top.sv");

  VpiObject no_file;
  no_file.type = vpiAttribute;
  EXPECT_EQ(vpi_get_str(vpiDefFile, &no_file), nullptr);
}

// Figure property (-> definition location, line): an attribute reports the
// source line of its definition through vpi_get(vpiDefLineNo).
TEST_F(Attribute, DefinitionLineReportedThroughVpiGet) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_line_no = 42;
  EXPECT_EQ(vpi_get(vpiDefLineNo, &attr), 42);
}

// Figure property guard: the definition-location properties are drawn only on
// the attribute object, so querying them on any other object kind is not a
// valid request - vpiDefFile yields null and vpiDefLineNo yields vpiUndefined
// through the production guards rather than handing back stored fields.
TEST_F(Attribute, DefinitionLocationPropertiesGuardedToAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiModule;
  EXPECT_EQ(vpi_get_str(vpiDefFile, &not_an_attribute), nullptr);
  EXPECT_EQ(vpi_get(vpiDefLineNo, &not_an_attribute), vpiUndefined);
}

// The untagged double arrow into `attribute`: an object reaches the attributes
// it carries through vpi_iterate(vpiAttribute, obj), in the order they were
// written, and children of other kinds are not among them. Each attribute
// reached is the one whose vpiParent is that object, which is the same pair of
// arrows read from both ends.
TEST_F(Attribute, AnObjectIteratesTheAttributesItCarries) {
  VpiObject owning_module;
  owning_module.type = vpiModule;

  VpiObject keep;
  keep.type = vpiAttribute;
  keep.name = "keep";
  keep.parent = &owning_module;

  VpiObject a_net;  // a child of another kind, which the iteration steps over
  a_net.type = vpiNet;

  VpiObject dont_touch;
  dont_touch.type = vpiAttribute;
  dont_touch.name = "dont_touch";
  dont_touch.parent = &owning_module;

  owning_module.children = {&keep, &a_net, &dont_touch};

  vpiHandle it = vpi_iterate(vpiAttribute, &owning_module);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &keep);
  EXPECT_EQ(vpi_scan(it), &dont_touch);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(vpi_handle(vpiParent, &keep), &owning_module);
  EXPECT_EQ(vpi_handle(vpiParent, &dont_touch), &owning_module);
}

// The double arrow's empty outcome: an object carrying no attribute iterates
// none, so the children it does carry are not handed back in their place.
TEST_F(Attribute, AnObjectWithNoAttributeIteratesNone) {
  VpiObject a_net;
  a_net.type = vpiNet;

  VpiObject owning_module;
  owning_module.type = vpiModule;
  owning_module.children = {&a_net};

  EXPECT_EQ(vpi_iterate(vpiAttribute, &owning_module), nullptr);
}

// Figure property (-> value): an attribute reports the value it was written
// with through vpi_get_value(), which is what the figure draws on it rather
// than a vpi_get integer property. An attribute given no value reports none.
TEST_F(Attribute, ValueReportedThroughVpiGetValue) {
  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;
  storage.aval = 7;

  VpiObject attr;
  attr.type = vpiAttribute;
  attr.name = "priority";
  attr.var = &var;

  VpiValue value{};
  value.format = vpiIntVal;
  vpi_get_value(&attr, &value);
  EXPECT_EQ(value.value.integer, 7);

  // An attribute written with no value has none to read, so the request leaves
  // the caller's structure as it found it rather than inventing one.
  VpiObject no_value;
  no_value.type = vpiAttribute;

  VpiValue untouched{};
  untouched.format = vpiIntVal;
  untouched.value.integer = 99;
  vpi_get_value(&no_value, &untouched);
  EXPECT_EQ(untouched.value.integer, 99);
}

}  // namespace
}  // namespace delta

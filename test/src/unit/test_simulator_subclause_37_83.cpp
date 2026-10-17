#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&attr))),
            &owning_net);
}

// Figure property (-> name): an attribute reports its name through the generic
// vpi_get_str(vpiName) read. Observed through the public dispatch path.
TEST_F(Attribute, NameReportsTheAttributeName) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.name = "keep";

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&attr)), "keep");
}

// Figure property (-> On definition): an attribute reports through
// vpi_get(vpiDefAttribute) whether it was specified on a definition rather than
// on an instance, as 1 when on a definition and 0 otherwise. Driving both
// states exercises the production code reading the stored Boolean.
TEST_F(Attribute, OnDefinitionFlagReportedThroughVpiGet) {
  VpiObject on_definition;
  on_definition.type = vpiAttribute;
  on_definition.def_attribute = true;
  EXPECT_EQ(vpi_get(vpiDefAttribute, VpiHandleOf(&on_definition)), 1);

  VpiObject on_instance;
  on_instance.type = vpiAttribute;
  on_instance.def_attribute = false;
  EXPECT_EQ(vpi_get(vpiDefAttribute, VpiHandleOf(&on_instance)), 0);
}

// Figure property guard: vpiDefAttribute is drawn only on the attribute object,
// so querying it on any other object kind is not a valid request and the
// production guard returns vpiUndefined rather than handing back a stored
// field.
TEST_F(Attribute, OnDefinitionFlagIsUndefinedForNonAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiDefAttribute, VpiHandleOf(&not_an_attribute)),
            vpiUndefined);
}

// Figure property (-> definition location, file): an attribute reports the
// source file of its definition through vpi_get_str(vpiDefFile). An attribute
// with no recorded definition file yields null rather than an empty string -
// the empty-name branch distinct from the wrong-kind guard.
TEST_F(Attribute, DefinitionFileReportedThroughVpiGetStr) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_file = "rtl/top.sv";
  EXPECT_STREQ(vpi_get_str(vpiDefFile, VpiHandleOf(&attr)), "rtl/top.sv");

  VpiObject no_file;
  no_file.type = vpiAttribute;
  EXPECT_EQ(vpi_get_str(vpiDefFile, VpiHandleOf(&no_file)), nullptr);
}

// Figure property (-> definition location, line): an attribute reports the
// source line of its definition through vpi_get(vpiDefLineNo).
TEST_F(Attribute, DefinitionLineReportedThroughVpiGet) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_line_no = 42;
  EXPECT_EQ(vpi_get(vpiDefLineNo, VpiHandleOf(&attr)), 42);
}

// Figure property guard: the definition-location properties are drawn on the
// attribute object and, by §37.10, on an instance, so querying them on a net
// is not a valid request - vpiDefFile yields null and vpiDefLineNo yields
// vpiUndefined through the production guards rather than handing back stored
// fields.
TEST_F(Attribute, DefinitionLocationPropertiesGuardedToAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get_str(vpiDefFile, VpiHandleOf(&not_an_attribute)), nullptr);
  EXPECT_EQ(vpi_get(vpiDefLineNo, VpiHandleOf(&not_an_attribute)),
            vpiUndefined);
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

  vpiHandle it = vpi_iterate(vpiAttribute, VpiHandleOf(&owning_module));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &keep);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &dont_touch);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&keep))),
            &owning_module);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&dont_touch))),
            &owning_module);
}

// The double arrow's empty outcome: an object carrying no attribute iterates
// none, so the children it does carry are not handed back in their place.
TEST_F(Attribute, AnObjectWithNoAttributeIteratesNone) {
  VpiObject a_net;
  a_net.type = vpiNet;

  VpiObject owning_module;
  owning_module.type = vpiModule;
  owning_module.children = {&a_net};

  EXPECT_EQ(vpi_iterate(vpiAttribute, VpiHandleOf(&owning_module)), nullptr);
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

  s_vpi_value value{};
  value.format = vpiIntVal;
  vpi_get_value(VpiHandleOf(&attr), &value);
  EXPECT_EQ(value.value.integer, 7);

  // An attribute written with no value has none to read, so the request leaves
  // the caller's structure as it found it rather than inventing one.
  VpiObject no_value;
  no_value.type = vpiAttribute;

  s_vpi_value untouched{};
  untouched.format = vpiIntVal;
  untouched.value.integer = 99;
  vpi_get_value(VpiHandleOf(&no_value), &untouched);
  EXPECT_EQ(untouched.value.integer, 99);
}

// The attributes of a run: those a design is written with, built from the
// elaborated design rather than by hand.
class AttributesOfARun : public VpiDesignRun {
 protected:
  // The value `attr` reports in `format`, as a string; empty for none.
  static std::string ValueOf(vpiHandle attr, int format) {
    s_vpi_value value = {};
    value.format = format;
    vpi_get_value(attr, &value);
    if (format == vpiIntVal) return std::to_string(value.value.integer);
    return value.value.str == nullptr ? "" : value.value.str;
  }
};

// A net and a variable carry the attributes they are declared with, in the
// order written, each reaching the net or variable through vpiParent and
// written on it rather than on a definition. One written with no value is a
// bit of 1 (§5.12); one written with a sized literal has that literal's width;
// one written with a string is that string.
TEST_F(AttributesOfARun, ANetAndAVariableCarryTheirAttributes) {
  Run("module top;\n"
      "  (* keep, weight = 8'd5 *) wire w;\n"
      "  (* tag = \"fast\" *) logic v;\n"
      "  wire plain;\n"
      "endmodule\n");
  vpiHandle w = By("top.w");
  vpiHandle it = vpi_iterate(vpiAttribute, w);
  ASSERT_NE(it, nullptr);
  vpiHandle keep = vpi_scan(it);
  vpiHandle weight = vpi_scan(it);
  EXPECT_EQ(vpi_scan(it), nullptr);
  ASSERT_NE(keep, nullptr);
  ASSERT_NE(weight, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, keep), "keep");
  EXPECT_EQ(vpi_get(vpiDefAttribute, keep), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, keep)), VpiObjectOf(w));
  EXPECT_EQ(ValueOf(keep, vpiBinStrVal), "1");
  EXPECT_STREQ(vpi_get_str(vpiName, weight), "weight");
  EXPECT_EQ(ValueOf(weight, vpiBinStrVal), "00000101");
  vpiHandle tag = Named(vpiAttribute, By("top.v"), "tag");
  ASSERT_NE(tag, nullptr);
  EXPECT_EQ(ValueOf(tag, vpiStringVal), "fast");
  EXPECT_EQ(vpi_iterate(vpiAttribute, By("top.plain")), nullptr);
}

// An attribute written with a parameter's name holds the parameter's value,
// as an integer where its expression fixes no width.
TEST_F(AttributesOfARun, AnAttributeOfAParametersValueIsAnInteger) {
  Run("module top #(parameter P = 7);\n"
      "  (* depth = P *) logic v;\n"
      "endmodule\n");
  vpiHandle depth = Named(vpiAttribute, By("top.v"), "depth");
  ASSERT_NE(depth, nullptr);
  EXPECT_EQ(ValueOf(depth, vpiIntVal), "7");
  EXPECT_EQ(ValueOf(depth, vpiBinStrVal).size(), 32u);
}

// An instance carries the attributes its instantiation is written with, and,
// as attributes on its definition, those its module's declaration is written
// with; a top module carries its declaration's. Each reports where it was
// written, in the file the module is.
TEST_F(AttributesOfARun, AnInstanceCarriesItsOwnAndItsDefinitionsAttributes) {
  Run("(* area = 3 *) module sub; endmodule\n"
      "(* root *) module top;\n"
      "  (* place = \"left\" *) sub u();\n"
      "endmodule\n");
  vpiHandle u = By("top.u");
  EXPECT_EQ(NamesOf(vpiAttribute, u),
            (std::vector<std::string>{"area", "place"}));
  vpiHandle area = Named(vpiAttribute, u, "area");
  vpiHandle place = Named(vpiAttribute, u, "place");
  ASSERT_NE(area, nullptr);
  ASSERT_NE(place, nullptr);
  EXPECT_EQ(vpi_get(vpiDefAttribute, area), 1);
  EXPECT_EQ(ValueOf(area, vpiIntVal), "3");
  EXPECT_EQ(vpi_get(vpiDefAttribute, place), 0);
  EXPECT_EQ(vpi_get(vpiDefLineNo, area), 1);
  EXPECT_EQ(vpi_get(vpiDefLineNo, place), 3);
  EXPECT_STREQ(vpi_get_str(vpiDefFile, place), vpi_get_str(vpiDefFile, u));
  vpiHandle root = Named(vpiAttribute, By("top"), "root");
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(vpi_get(vpiDefAttribute, root), 1);
}

// A procedure carries the attributes it is written with.
TEST_F(AttributesOfARun, AProcessCarriesItsAttributes) {
  Run("module top;\n"
      "  (* stage = 4 *) initial begin end\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle process = vpi_scan(it);
  ASSERT_NE(process, nullptr);
  vpiHandle stage = Named(vpiAttribute, process, "stage");
  ASSERT_NE(stage, nullptr);
  EXPECT_EQ(ValueOf(stage, vpiIntVal), "4");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, stage)), VpiObjectOf(process));
}

// An attribute is written on its holder, not declared in it: a name it shares
// with what the holder declares reaches the declaration, and an index selects
// no attribute, here where the vector it is written on has no bit 0.
TEST_F(AttributesOfARun, NoNameOrIndexReachesAnAttribute) {
  Run("(* w = 2 *) module top;\n"
      "  wire w;\n"
      "  (* keep *) wire [2:1] bus;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.w")), vpiNet);
  EXPECT_EQ(vpi_handle_by_index(By("top.bus"), 0), nullptr);
}

}  // namespace
}  // namespace delta

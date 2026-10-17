#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
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

// A task and a function carry the attributes they are written with.
TEST_F(AttributesOfARun, ATaskAndAFunctionCarryTheirAttributes) {
  Run("module top;\n"
      "  (* inline *) function int f(); return 0; endfunction\n"
      "  (* slow = 2 *) task t(); endtask\n"
      "endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  vpiHandle t = Named(vpiTaskFunc, By("top"), "t");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, f), std::vector<std::string>{"inline"});
  vpiHandle slow = Named(vpiAttribute, t, "slow");
  ASSERT_NE(slow, nullptr);
  EXPECT_EQ(ValueOf(slow, vpiIntVal), "2");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, slow)), VpiObjectOf(t));
}

// A gate and a UDP instance carry the attributes their instantiations are
// written with.
TEST_F(AttributesOfARun, AGateAndAUdpCarryTheirAttributes) {
  Run("primitive u_and(output y, input a, b);\n"
      "  table 1 1 : 1; 0 ? : 0; ? 0 : 0; endtable\n"
      "endprimitive\n"
      "module top; wire y, z, a, b;\n"
      "  (* keep *) and g1 (y, a, b);\n"
      "  (* place = \"west\" *) u_and u1 (z, a, b);\n"
      "endmodule\n");
  vpiHandle g1 = Named(vpiPrimitive, By("top"), "g1");
  vpiHandle u1 = Named(vpiPrimitive, By("top"), "u1");
  ASSERT_NE(g1, nullptr);
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, g1), std::vector<std::string>{"keep"});
  vpiHandle place = Named(vpiAttribute, u1, "place");
  ASSERT_NE(place, nullptr);
  EXPECT_EQ(ValueOf(place, vpiStringVal), "west");
}

// A statement carries the attributes it is written with, here a case
// statement, the statement an initial procedure runs, and an assignment the
// case statement holds.
TEST_F(AttributesOfARun, AStatementCarriesItsAttributes) {
  Run("module top; logic [1:0] s; logic y;\n"
      "  initial (* parallel_case *) case (s)\n"
      "    0: (* note *) y = 1;\n"
      "    default: y = 0;\n"
      "  endcase\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle case_stmt = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, case_stmt),
            std::vector<std::string>{"parallel_case"});
  vpiHandle items = vpi_iterate(vpiCaseItem, case_stmt);
  ASSERT_NE(items, nullptr);
  vpiHandle first = vpi_handle(vpiStmt, vpi_scan(items));
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, first), std::vector<std::string>{"note"});
}

// A concurrent assertion, a property declaration and a clocking block carry
// the attributes they are written with.
TEST_F(AttributesOfARun, AnAssertionAPropertyAndAClockingBlockCarryTheirs) {
  Run("module top; logic clk, x;\n"
      "  (* tag = 1 *) property p; @(posedge clk) x; endproperty\n"
      "  (* tag = 2 *) a1: assert property (@(posedge clk) x);\n"
      "  (* tag = 3 *) clocking cb @(posedge clk); endclocking\n"
      "endmodule\n");
  const auto kTagOf = [](vpiHandle obj) {
    vpiHandle tag = Named(vpiAttribute, obj, "tag");
    return tag == nullptr ? std::string() : ValueOf(tag, vpiIntVal);
  };
  EXPECT_EQ(kTagOf(Named(vpiPropertyDecl, By("top"), "p")), "1");
  EXPECT_EQ(kTagOf(Named(vpiAssertion, By("top"), "a1")), "2");
  EXPECT_EQ(kTagOf(Named(vpiClockingBlock, By("top"), "cb")), "3");
}

// A port carries the attributes written before its declaration, an ANSI
// port's in the module header and a non-ANSI port's before the body
// declaration that gives it its direction.
TEST_F(AttributesOfARun, APortCarriesItsAttributes) {
  Run("module ansi((* keep *) input logic a, (* tag = 4 *) output logic b);\n"
      "endmodule\n"
      "module plain(c);\n"
      "  (* note *) input c;\n"
      "endmodule\n"
      "module top; logic a, b, c;\n"
      "  ansi u1(.a(a), .b(b));\n"
      "  plain u2(.c(c));\n"
      "endmodule\n");
  vpiHandle a = Named(vpiPort, By("top.u1"), "a");
  vpiHandle b = Named(vpiPort, By("top.u1"), "b");
  vpiHandle c = Named(vpiPort, By("top.u2"), "c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, a), std::vector<std::string>{"keep"});
  vpiHandle tag = Named(vpiAttribute, b, "tag");
  ASSERT_NE(tag, nullptr);
  EXPECT_EQ(ValueOf(tag, vpiIntVal), "4");
  EXPECT_EQ(NamesOf(vpiAttribute, c), std::vector<std::string>{"note"});
}

// A class carries the attributes written before its declaration, whether
// the compilation unit, a package or a module declares it, and a constraint
// those written before it in the class.
TEST_F(AttributesOfARun, AClassAndAConstraintCarryTheirAttributes) {
  Run("(* tag = 1 *) class Unit; endclass\n"
      "package p; (* tag = 2 *) class Pkg; endclass endpackage\n"
      "module top;\n"
      "  (* tag = 3 *) class Inner;\n"
      "    rand int x;\n"
      "    (* soft_c *) constraint c { x > 0; }\n"
      "  endclass\n"
      "endmodule\n");
  const auto kTagOf = [](vpiHandle obj) {
    vpiHandle tag = Named(vpiAttribute, obj, "tag");
    return tag == nullptr ? std::string() : ValueOf(tag, vpiIntVal);
  };
  EXPECT_EQ(kTagOf(Named(vpiClassDefn, nullptr, "Unit")), "1");
  EXPECT_EQ(kTagOf(Named(vpiClassDefn, By("p"), "Pkg")), "2");
  vpiHandle inner = Named(vpiClassDefn, By("top"), "Inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(kTagOf(inner), "3");
  vpiHandle c = Named(vpiConstraint, inner, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, c), std::vector<std::string>{"soft_c"});
}

// An operation carries the attributes written after its operator, in a
// continuous assignment and in a procedural statement alike, and for a
// binary, a unary and a conditional operator.
TEST_F(AttributesOfARun, AnOperationCarriesItsOperatorsAttributes) {
  Run("module top; wire [7:0] a, b, y, u, t; logic [7:0] z; wire c;\n"
      "  assign y = a + (* mode = \"cla\" *) b;\n"
      "  assign u = ~ (* inv *) a;\n"
      "  assign t = c ? (* pick *) a : b;\n"
      "  initial z = a & (* tag *) b;\n"
      "endmodule\n");
  std::vector<std::string> names;
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle assign = vpi_scan(it)) {
    for (const std::string& name :
         NamesOf(vpiAttribute, vpi_handle(vpiRhs, assign))) {
      names.push_back(name);
    }
  }
  std::ranges::sort(names);
  EXPECT_EQ(names, (std::vector<std::string>{"inv", "mode", "pick"}));
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle assignment = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(assignment, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, vpi_handle(vpiRhs, assignment)),
            std::vector<std::string>{"tag"});
}

}  // namespace
}  // namespace delta

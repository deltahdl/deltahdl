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

class Attribute : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Attribute, ParentReachesTheOwningObject) {
  VpiObject owning_net;
  owning_net.type = vpiNet;

  VpiObject attr;
  attr.type = vpiAttribute;
  attr.parent = &owning_net;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&attr))),
            &owning_net);
}

TEST_F(Attribute, NameReportsTheAttributeName) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.name = "keep";

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&attr)), "keep");
}

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

TEST_F(Attribute, OnDefinitionFlagIsUndefinedForNonAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiDefAttribute, VpiHandleOf(&not_an_attribute)),
            vpiUndefined);
}

TEST_F(Attribute, DefinitionFileReportedThroughVpiGetStr) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_file = "rtl/top.sv";
  EXPECT_STREQ(vpi_get_str(vpiDefFile, VpiHandleOf(&attr)), "rtl/top.sv");

  VpiObject no_file;
  no_file.type = vpiAttribute;
  EXPECT_EQ(vpi_get_str(vpiDefFile, VpiHandleOf(&no_file)), nullptr);
}

TEST_F(Attribute, DefinitionLineReportedThroughVpiGet) {
  VpiObject attr;
  attr.type = vpiAttribute;
  attr.def_line_no = 42;
  EXPECT_EQ(vpi_get(vpiDefLineNo, VpiHandleOf(&attr)), 42);
}

TEST_F(Attribute, DefinitionLocationPropertiesGuardedToAttribute) {
  VpiObject not_an_attribute;
  not_an_attribute.type = vpiNet;
  EXPECT_EQ(vpi_get_str(vpiDefFile, VpiHandleOf(&not_an_attribute)), nullptr);
  EXPECT_EQ(vpi_get(vpiDefLineNo, VpiHandleOf(&not_an_attribute)),
            vpiUndefined);
}

TEST_F(Attribute, AnObjectIteratesTheAttributesItCarries) {
  VpiObject owning_module;
  owning_module.type = vpiModule;

  VpiObject keep;
  keep.type = vpiAttribute;
  keep.name = "keep";
  keep.parent = &owning_module;

  VpiObject a_net;
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

TEST_F(Attribute, AnObjectWithNoAttributeIteratesNone) {
  VpiObject a_net;
  a_net.type = vpiNet;

  VpiObject owning_module;
  owning_module.type = vpiModule;
  owning_module.children = {&a_net};

  EXPECT_EQ(vpi_iterate(vpiAttribute, VpiHandleOf(&owning_module)), nullptr);
}

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

  VpiObject no_value;
  no_value.type = vpiAttribute;

  s_vpi_value untouched{};
  untouched.format = vpiIntVal;
  untouched.value.integer = 99;
  vpi_get_value(VpiHandleOf(&no_value), &untouched);
  EXPECT_EQ(untouched.value.integer, 99);
}

class AttributesOfARun : public VpiDesignRun {
 protected:
  static std::string ValueOf(vpiHandle attr, int format) {
    s_vpi_value value = {};
    value.format = format;
    vpi_get_value(attr, &value);
    if (format == vpiIntVal) return std::to_string(value.value.integer);
    return value.value.str == nullptr ? "" : value.value.str;
  }
};

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

TEST_F(AttributesOfARun, ASpecParamCarriesItsAttributes) {
  Run("module top;\n"
      "  (* note, depth = 3 *) specparam d = 1;\n"
      "  specparam e = 2;\n"
      "endmodule\n");
  vpiHandle d = Named(vpiSpecParam, By("top"), "d");
  ASSERT_NE(d, nullptr);
  vpiHandle note = Named(vpiAttribute, d, "note");
  ASSERT_NE(note, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, note)), VpiObjectOf(d));
  vpiHandle depth = Named(vpiAttribute, d, "depth");
  ASSERT_NE(depth, nullptr);
  EXPECT_EQ(ValueOf(depth, vpiIntVal), "3");
  EXPECT_EQ(vpi_iterate(vpiAttribute, Named(vpiSpecParam, By("top"), "e")),
            nullptr);
}

TEST_F(AttributesOfARun, AnAttributeOfAParametersValueIsAnInteger) {
  Run("module top #(parameter P = 7);\n"
      "  (* depth = P *) logic v;\n"
      "endmodule\n");
  vpiHandle depth = Named(vpiAttribute, By("top.v"), "depth");
  ASSERT_NE(depth, nullptr);
  EXPECT_EQ(ValueOf(depth, vpiIntVal), "7");
  EXPECT_EQ(ValueOf(depth, vpiBinStrVal).size(), 32u);
}

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

TEST_F(AttributesOfARun, NoNameOrIndexReachesAnAttribute) {
  Run("(* w = 2, only *) module top;\n"
      "  wire w;\n"
      "  (* keep *) wire [2:1] bus;\n"
      "endmodule\n");
  ASSERT_NE(Named(vpiAttribute, By("top"), "only"), nullptr);
  EXPECT_EQ(vpi_get(vpiType, By("top.w")), vpiNet);
  EXPECT_EQ(By("top.only"), nullptr);
  EXPECT_EQ(vpi_handle_by_index(By("top.bus"), 0), nullptr);
}

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

TEST_F(AttributesOfARun, ASequenceDeclarationCarriesItsAttributes) {
  Run("module top; logic x, y;\n"
      "  (* tag = 4 *) sequence s; x ##1 y; endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  vpiHandle tag = Named(vpiAttribute, decl, "tag");
  ASSERT_NE(tag, nullptr);
  EXPECT_EQ(ValueOf(tag, vpiIntVal), "4");
}

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

TEST_F(AttributesOfARun, AnOperationOutsideAnAssignmentCarriesItsAttributes) {
  Run("interface ifc; logic a, b;\n"
      "  modport mp(input .p(a & (* t4 *) b));\n"
      "endinterface\n"
      "module sub(input logic [7:0] i); endmodule\n"
      "module top; wire y, a, b, c, clk, en; logic [7:0] x, z;\n"
      "  and g (y, a & (* t1 *) b, c);\n"
      "  sub u(.i(x | (* t2 *) z));\n"
      "  clocking cb @(posedge (clk & (* t3 *) en)); endclocking\n"
      "  ifc i0();\n"
      "  class Base; function new(int n); endfunction endclass\n"
      "  class Derived extends Base(2 + (* t5 *) 3);\n"
      "    rand int v;\n"
      "    constraint k { v > (* t6 *) 1; }\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle terms =
      vpi_iterate(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
  ASSERT_NE(terms, nullptr);
  vpi_scan(terms);
  EXPECT_EQ(NamesOf(vpiAttribute, vpi_handle(vpiExpr, vpi_scan(terms))),
            std::vector<std::string>{"t1"});
  vpiHandle i = Named(vpiPort, By("top.u"), "i");
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, vpi_handle(vpiHighConn, i)),
            std::vector<std::string>{"t2"});
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  const std::vector<vpiHandle> kEdgeOperands =
      OperandsOf(vpi_handle(vpiCondition, vpi_handle(vpiClockingEvent, cb)));
  ASSERT_EQ(kEdgeOperands.size(), 1u);
  EXPECT_EQ(NamesOf(vpiAttribute, kEdgeOperands[0]),
            std::vector<std::string>{"t3"});
  vpiHandle mp = Named(vpiModport, By("top.i0"), "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(
      NamesOf(vpiAttribute, vpi_handle(vpiExpr, Named(vpiIODecl, mp, "p"))),
      std::vector<std::string>{"t4"});
  vpiHandle derived = Named(vpiClassDefn, By("top"), "Derived");
  ASSERT_NE(derived, nullptr);
  vpiHandle args = vpi_iterate(vpiArgument, vpi_handle(vpiExtends, derived));
  ASSERT_NE(args, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, vpi_scan(args)),
            std::vector<std::string>{"t5"});
  vpiHandle items =
      vpi_iterate(vpiConstraintItem, Named(vpiConstraint, derived, "k"));
  ASSERT_NE(items, nullptr);
  EXPECT_EQ(NamesOf(vpiAttribute, vpi_scan(items)),
            std::vector<std::string>{"t6"});
}

TEST_F(AttributesOfARun, APropertysOperationCarriesItsOperatorsAttributes) {
  Run("package p; logic x, y;\n"
      "  property q; x ^ (* in_pkg *) y; endproperty\n"
      "endpackage\n"
      "module top; logic a, b;\n"
      "  property r; a || (* in_mod *) b; endproperty\n"
      "endmodule\n");
  const auto kBodyOf = [](vpiHandle scope, const char* name) {
    vpiHandle decl = Named(vpiPropertyDecl, scope, name);
    return decl == nullptr
               ? nullptr
               : vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  };
  EXPECT_EQ(NamesOf(vpiAttribute, kBodyOf(By("p"), "q")),
            std::vector<std::string>{"in_pkg"});
  EXPECT_EQ(NamesOf(vpiAttribute, kBodyOf(By("top"), "r")),
            std::vector<std::string>{"in_mod"});
}

}  // namespace
}  // namespace delta

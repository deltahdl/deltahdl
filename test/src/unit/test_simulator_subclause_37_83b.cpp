#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kUdpDesign =
    "(* d_udp *) primitive u_or(output y, input a, b);\n"
    "  table 1 ? : 1; ? 1 : 1; 0 0 : 0; endtable\n"
    "endprimitive\n"
    "module top; wire y, a, b;\n"
    "  (* a_udp *) u_or g0 (y, a, b);\n"
    "endmodule\n";

class AttributesOfEachKind : public VpiDesignRun {
 protected:
  static void ExpectCarried(vpiHandle holder, const char* name, int line) {
    ASSERT_NE(holder, nullptr) << name;
    vpiHandle attr = Named(vpiAttribute, holder, name);
    ASSERT_NE(attr, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, attr), vpiAttribute) << name;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiParent, attr), holder), 1)
        << name;
    EXPECT_EQ(vpi_get(vpiDefLineNo, attr), line) << name;
    const char* file = vpi_get_str(vpiDefFile, attr);
    ASSERT_NE(file, nullptr) << name;
    EXPECT_STREQ(file, "<test>") << name;
  }

  static void ExpectOnDefinition(vpiHandle holder, const char* name,
                                 int on_definition) {
    ASSERT_NE(holder, nullptr) << name;
    vpiHandle attr = Named(vpiAttribute, holder, name);
    ASSERT_NE(attr, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiDefAttribute, attr), on_definition) << name;
  }

  static vpiHandle Carrying(int type, vpiHandle scope, const char* name) {
    for (vpiHandle obj : ObjectsOf(type, scope)) {
      if (Named(vpiAttribute, obj, name) != nullptr) return obj;
    }
    return nullptr;
  }

  static vpiHandle FirstOf(int type, vpiHandle ref) {
    if (ref == nullptr) return nullptr;
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

TEST_F(AttributesOfEachKind, EachInstanceCarriesItsOwnAndItsDefinitions) {
  Run("(* d_if = 1 *) interface ifc; endinterface\n"
      "(* d_pg = 2 *) program pg; endprogram\n"
      "(* d_sub *) module sub; endmodule\n"
      "(* d_top *) module top;\n"
      "  (* a_if *) ifc i0();\n"
      "  (* a_pg *) pg p0();\n"
      "  (* a_sub *) sub u();\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiAttribute, By("top.i0")),
            (std::vector<std::string>{"a_if", "d_if"}));
  EXPECT_EQ(NamesOf(vpiAttribute, By("top.p0")),
            (std::vector<std::string>{"a_pg", "d_pg"}));
  ExpectCarried(By("top.i0"), "d_if", 1);
  ExpectCarried(By("top.i0"), "a_if", 5);
  ExpectCarried(By("top.p0"), "d_pg", 2);
  ExpectCarried(By("top.p0"), "a_pg", 6);
  ExpectCarried(By("top.u"), "d_sub", 3);
  ExpectCarried(By("top.u"), "a_sub", 7);
  ExpectCarried(By("top"), "d_top", 4);
}

TEST_F(AttributesOfEachKind, AnInterfaceOrProgramDeclarationsIsOnDefinition) {
  Run("(* d_if *) interface ifc; endinterface\n"
      "(* d_pg *) program pg; endprogram\n"
      "module top;\n"
      "  (* a_if *) ifc i0();\n"
      "  (* a_pg *) pg p0();\n"
      "endmodule\n");
  ExpectOnDefinition(By("top.i0"), "d_if", 1);
  ExpectOnDefinition(By("top.i0"), "a_if", 0);
  ExpectOnDefinition(By("top.p0"), "d_pg", 1);
  ExpectOnDefinition(By("top.p0"), "a_pg", 0);
}

TEST_F(AttributesOfEachKind, DISABLED_APackageCarriesItsOwnAttribute) {
  Run("(* d_pk = 3 *) package pk; endpackage\n"
      "module top; endmodule\n");
  ExpectCarried(By("pk"), "d_pk", 1);
}

TEST_F(AttributesOfEachKind, AUdpInstantiationsOwnAttributeIsCarried) {
  Run(kUdpDesign);
  vpiHandle g0 = Named(vpiPrimitive, By("top"), "g0");
  ExpectCarried(g0, "a_udp", 5);
  ExpectOnDefinition(g0, "a_udp", 0);
}

TEST_F(AttributesOfEachKind, DISABLED_AUdpInstanceCarriesItsDeclarations) {
  Run(kUdpDesign);
  vpiHandle g0 = Named(vpiPrimitive, By("top"), "g0");
  EXPECT_EQ(NamesOf(vpiAttribute, g0),
            (std::vector<std::string>{"a_udp", "d_udp"}));
  ExpectCarried(g0, "d_udp", 1);
  ExpectOnDefinition(g0, "d_udp", 1);
}

TEST_F(AttributesOfEachKind, AnOperationOutsideAnAssignmentReachesItsOwner) {
  Run("module sub(input logic [7:0] i); endmodule\n"
      "module top; wire y, a, b, c; logic [7:0] x, z;\n"
      "  and g (y, a & (* t1 *) b, c);\n"
      "  sub u(.i(x | (* t2 *) z));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kTerms =
      ObjectsOf(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
  ASSERT_EQ(kTerms.size(), 3U);
  ExpectCarried(vpi_handle(vpiExpr, kTerms[1]), "t1", 3);
  vpiHandle i = Named(vpiPort, By("top.u"), "i");
  ASSERT_NE(i, nullptr);
  ExpectCarried(vpi_handle(vpiHighConn, i), "t2", 4);
}

TEST_F(AttributesOfEachKind, EachDeclarationCarriesTheAttributeAboveIt) {
  Run("interface ifc;\n"
      "  (* a_it *)\n"
      "  function int it(); return 0; endfunction\n"
      "endinterface\n"
      "class C; endclass\n"
      "module top;\n"
      "  ifc i0();\n"
      "  (* a_an *)\n"
      "  wire an [1:0];\n"
      "  (* a_av *)\n"
      "  logic av [1:0];\n"
      "  (* a_sv *)\n"
      "  struct packed { logic x; } sv;\n"
      "  (* a_cv *)\n"
      "  C cv;\n"
      "  (* a_ev *)\n"
      "  event ev;\n"
      "  (* a_fn *)\n"
      "  function int fn(); return 0; endfunction\n"
      "  (* a_v *)\n"
      "  logic v;\n"
      "endmodule\n");
  ExpectCarried(Named(vpiTaskFunc, By("top.i0"), "it"), "a_it", 2);
  ExpectCarried(By("top.an"), "a_an", 8);
  ExpectCarried(By("top.av"), "a_av", 10);
  ExpectCarried(By("top.sv"), "a_sv", 12);
  ExpectCarried(By("top.cv"), "a_cv", 14);
  ExpectCarried(By("top.ev"), "a_ev", 16);
  ExpectCarried(Named(vpiTaskFunc, By("top"), "fn"), "a_fn", 18);
  ExpectCarried(By("top.v"), "a_v", 20);
}

TEST_F(AttributesOfEachKind,
       DISABLED_APackageTaskAndAClassMethodCarryTheAttributeAboveThem) {
  Run("package pk;\n"
      "  (* a_pt *)\n"
      "  task pt; endtask\n"
      "endpackage\n"
      "class C;\n"
      "  (* a_cm *)\n"
      "  function void cm(); endfunction\n"
      "endclass\n"
      "module top; endmodule\n");
  ExpectCarried(Named(vpiTaskFunc, By("pk"), "pt"), "a_pt", 2);
  ExpectCarried(Named(vpiMethods, Named(vpiClassDefn, nullptr, "C"), "cm"),
                "a_cm", 6);
}

TEST_F(AttributesOfEachKind,
       EachProcessAssertionAndBodyStatementCarriesItsOwn) {
  Run("module top; logic clk, x, y1, y2, y3, y4;\n"
      "  (* a_al *) always @(x) y1 = x;\n"
      "  (* a_ac *) always_comb y2 = x;\n"
      "  (* a_af *) always_ff @(posedge clk) y3 <= x;\n"
      "  (* a_lt *) always_latch if (clk) y4 <= x;\n"
      "  (* a_fi *) final begin end\n"
      "  task tk; (* a_ts *) y1 = 0; endtask\n"
      "  (* a_as *) assume property (@(posedge clk) x);\n"
      "  (* a_co *) cover property (@(posedge clk) x);\n"
      "  (* a_rs *) restrict property (@(posedge clk) x);\n"
      "  always @(posedge clk) (* a_ip *) assert property (x);\n"
      "  (* a_ap *) assert property (@(posedge clk) x);\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ExpectCarried(Carrying(vpiProcess, top, "a_al"), "a_al", 2);
  ExpectCarried(Carrying(vpiProcess, top, "a_ac"), "a_ac", 3);
  ExpectCarried(Carrying(vpiProcess, top, "a_af"), "a_af", 4);
  ExpectCarried(Carrying(vpiProcess, top, "a_lt"), "a_lt", 5);
  ExpectCarried(Carrying(vpiProcess, top, "a_fi"), "a_fi", 6);
  ExpectCarried(vpi_handle(vpiStmt, Named(vpiTaskFunc, top, "tk")), "a_ts", 7);
  ExpectCarried(Carrying(vpiAssertion, top, "a_as"), "a_as", 8);
  ExpectCarried(Carrying(vpiAssertion, top, "a_co"), "a_co", 9);
  ExpectCarried(Carrying(vpiAssertion, top, "a_rs"), "a_rs", 10);
  ExpectCarried(Carrying(vpiAssertion, top, "a_ip"), "a_ip", 11);
  ExpectCarried(Carrying(vpiAssertion, top, "a_ap"), "a_ap", 12);
}

TEST_F(AttributesOfEachKind, EachKindTheDiagramListsReachesItsAttributesOwner) {
  Run("module sub((* a_po *) input logic i); endmodule\n"
      "module top; logic clk, x, y, s; wire w, a, b;\n"
      "  (* a_g *) and g (w, a, b);\n"
      "  sub u(.i(x));\n"
      "  initial (* a_st *) y = x & (* a_op *) s;\n"
      "  (* a_pr *) property p; @(posedge clk) x; endproperty\n"
      "  (* a_se *) sequence q; x ##1 y; endsequence\n"
      "  (* a_ck *) clocking cb @(posedge clk); endclocking\n"
      "  (* a_cl *) class K; rand int v; (* a_cn *) constraint c { v > 0; }\n"
      "  endclass\n"
      "  property r; x || (* a_pe *) y; endproperty\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ExpectCarried(Named(vpiPort, By("top.u"), "i"), "a_po", 1);
  ExpectCarried(Named(vpiPrimitive, top, "g"), "a_g", 3);
  vpiHandle stmt = vpi_handle(vpiStmt, FirstOf(vpiProcess, top));
  ExpectCarried(stmt, "a_st", 5);
  ExpectCarried(stmt == nullptr ? nullptr : vpi_handle(vpiRhs, stmt), "a_op",
                5);
  ExpectCarried(Named(vpiPropertyDecl, top, "p"), "a_pr", 6);
  ExpectCarried(Named(vpiSequenceDecl, top, "q"), "a_se", 7);
  ExpectCarried(Named(vpiClockingBlock, top, "cb"), "a_ck", 8);
  vpiHandle k = Named(vpiClassDefn, top, "K");
  ExpectCarried(k, "a_cl", 9);
  ExpectCarried(k == nullptr ? nullptr : Named(vpiConstraint, k, "c"), "a_cn",
                9);
  vpiHandle r = Named(vpiPropertyDecl, top, "r");
  vpiHandle spec = r == nullptr ? nullptr : vpi_handle(vpiPropertySpec, r);
  ExpectCarried(spec == nullptr ? nullptr : vpi_handle(vpiPropertyExpr, spec),
                "a_pe", 11);
}

TEST_F(AttributesOfEachKind, KindsTheSyntaxGivesNoAttributeIterateNone) {
  Run("primitive u_or(output y, input a, b);\n"
      "  table 1 ? : 1; ? 1 : 1; 0 0 : 0; endtable\n"
      "endprimitive\n"
      "module sub #(parameter W = 1); endmodule\n"
      "module top(input a, d, clk, output y); wire z;\n"
      "  (* a_s *) sub #(.W(2)) s();\n"
      "  and g (z, a, d);\n"
      "  u_or g1 (y, a, d);\n"
      "  specify (a => y) = 1; $setup(d, posedge clk, 1); endspecify\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::vector<vpiHandle> kTerms =
      ObjectsOf(vpiPrimTerm, Named(vpiPrimitive, top, "g"));
  ASSERT_EQ(kTerms.size(), 3U);
  for (vpiHandle term : kTerms) {
    EXPECT_EQ(vpi_iterate(vpiAttribute, term), nullptr);
  }
  vpiHandle mod_path = FirstOf(vpiModPath, top);
  ASSERT_NE(mod_path, nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, mod_path), nullptr);
  vpiHandle path_term = FirstOf(vpiModPathIn, mod_path);
  ASSERT_NE(path_term, nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, path_term), nullptr);
  vpiHandle tchk = FirstOf(vpiTchk, top);
  ASSERT_NE(tchk, nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, tchk), nullptr);
  vpiHandle entry = FirstOf(
      vpiTableEntry, vpi_handle(vpiUdpDefn, Named(vpiPrimitive, top, "g1")));
  ASSERT_NE(entry, nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, entry), nullptr);
  vpiHandle assign = FirstOf(vpiParamAssign, By("top.s"));
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, assign), nullptr);
}

TEST_F(AttributesOfEachKind, TwoAttributeInstancesOnOneObjectAreBothCarried) {
  Run("module top;\n"
      "  (* a1 *) (* a2 = 2 *) wire w;\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiAttribute, By("top.w")),
            (std::vector<std::string>{"a1", "a2"}));
  ExpectCarried(By("top.w"), "a1", 2);
  ExpectCarried(By("top.w"), "a2", 2);
}

TEST_F(AttributesOfEachKind, AVectorAttributesValueComesBackAsAVector) {
  Run("module top;\n"
      "  (* v = 8'd5 *) wire w;\n"
      "endmodule\n");
  vpiHandle v = Named(vpiAttribute, By("top.w"), "v");
  ASSERT_NE(v, nullptr);
  s_vpi_value value = {};
  value.format = vpiObjTypeVal;
  vpi_get_value(v, &value);
  EXPECT_EQ(value.format, vpiVectorVal);
  ASSERT_NE(value.value.vector, nullptr);
  EXPECT_EQ(value.value.vector[0].aval & 0xFFu, 5u);
  EXPECT_EQ(value.value.vector[0].bval & 0xFFu, 0u);
}

TEST_F(AttributesOfEachKind, DISABLED_ARealAttributesValueComesBackAsAReal) {
  Run("module top;\n"
      "  (* r = 2.5 *) wire w;\n"
      "endmodule\n");
  vpiHandle r = Named(vpiAttribute, By("top.w"), "r");
  ASSERT_NE(r, nullptr);
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(r, &value);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
  value = {};
  value.format = vpiObjTypeVal;
  vpi_get_value(r, &value);
  EXPECT_EQ(value.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
}

}  // namespace
}  // namespace delta

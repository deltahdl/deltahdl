#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(IoDeclModel, ExprTargetTypeClassification) {
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiInterfaceTfDecl));
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiVirtualInterfaceVar));
  EXPECT_TRUE(VpiIsIoDeclExprType(kVpiNet));
  EXPECT_TRUE(VpiIsIoDeclExprType(kVpiReg));

  EXPECT_FALSE(VpiIsIoDeclExprType(vpiModule));
  EXPECT_FALSE(VpiIsIoDeclExprType(vpiExpr));
}

TEST(IoDeclModel, ExprTargetKindFollowsPassingMode) {
  EXPECT_EQ(VpiIoDeclExprType(true, false, false, kVpiNet), vpiRefObj);
  EXPECT_EQ(VpiIoDeclExprType(false, true, false, kVpiNet), vpiRefObj);
  EXPECT_EQ(VpiIoDeclExprType(true, true, true, kVpiNet),
            vpiVirtualInterfaceVar);
  EXPECT_EQ(VpiIoDeclExprType(false, false, false, kVpiNet), kVpiNet);
}

TEST(IoDeclPublic, HandleExprReturnsConnectionChild) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject io_decl;
  io_decl.type = vpiIODecl;
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  io_decl.children.push_back(&typespec);
  io_decl.children.push_back(&ref_obj);

  VpiHandle expr = ctx.Handle(vpiExpr, &io_decl);
  ASSERT_EQ(expr, &ref_obj);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiRefObj);

  VpiObject bare;
  bare.type = vpiIODecl;
  bare.children.push_back(&typespec);
  EXPECT_EQ(ctx.Handle(vpiExpr, &bare), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(IoDeclModel, ByReferenceReportsVpiRefDirection) {
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, true, false, false), vpiRef);
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, false, false, false), vpiInput);
  EXPECT_EQ(VpiIoDeclDirection(vpiOutput, false, false, false), vpiOutput);
  EXPECT_EQ(VpiIoDeclDirection(vpiInout, false, false, false), vpiInout);
}

TEST(IoDeclModel, InterfaceModportAndVirtualInterfaceHaveNoDirection) {
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, true, true, false), vpiNoDirection);
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, false, false, true), vpiNoDirection);
}

TEST(IoDeclModel, RangesMatchCorrespondingTypespec) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[0].size = 8;
  dims[1].kind = VpiDimensionKind::kAssoc;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;
  dims[1].size = 0;

  std::vector<VpiRangeDesc> io_ranges = VpiIoDeclRanges(dims);
  std::vector<VpiRangeDesc> ts_ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(io_ranges.size(), ts_ranges.size());
  for (size_t i = 0; i < io_ranges.size(); ++i) {
    EXPECT_EQ(io_ranges[i].empty, ts_ranges[i].empty);
    EXPECT_EQ(io_ranges[i].left_expr, ts_ranges[i].left_expr);
    EXPECT_EQ(io_ranges[i].right_expr, ts_ranges[i].right_expr);
    EXPECT_EQ(io_ranges[i].size, ts_ranges[i].size);
  }
  EXPECT_EQ(io_ranges[0].left_expr, &l0);
  EXPECT_TRUE(io_ranges[1].empty);
}

TEST(IoDeclModel, LeftRightRangeMatchTypespec) {
  VpiObject l0, r0;
  std::vector<VpiArrayDimension> packed(1);
  packed[0].kind = VpiDimensionKind::kPacked;
  packed[0].left_expr = &l0;
  packed[0].right_expr = &r0;
  packed[0].size = 4;
  EXPECT_EQ(VpiIoDeclLeftRange(packed), VpiTypespecLeftRange(packed));
  EXPECT_EQ(VpiIoDeclRightRange(packed), VpiTypespecRightRange(packed));
  EXPECT_EQ(VpiIoDeclLeftRange(packed), &l0);
  EXPECT_EQ(VpiIoDeclRightRange(packed), &r0);

  std::vector<VpiArrayDimension> dynamic(1);
  dynamic[0].kind = VpiDimensionKind::kDynamic;
  EXPECT_EQ(VpiIoDeclLeftRange(dynamic), nullptr);
  EXPECT_EQ(VpiIoDeclRightRange(dynamic), VpiTypespecRightRange(dynamic));
}

TEST(IoDeclModel, ExprTraversalAppliesOnlyToIoDecl) {
  EXPECT_EQ(VpiIoDeclExpr(nullptr), nullptr);

  VpiObject not_io_decl;
  not_io_decl.type = vpiModule;
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  not_io_decl.children.push_back(&ref_obj);
  EXPECT_EQ(VpiIoDeclExpr(&not_io_decl), nullptr);
}

TEST(IoDeclModel, ScalarIoDeclHasNoRanges) {
  std::vector<VpiArrayDimension> none;
  EXPECT_TRUE(VpiIoDeclRanges(none).empty());
  EXPECT_EQ(VpiIoDeclRanges(none).size(), VpiTypespecRanges(none).size());
  EXPECT_EQ(VpiIoDeclLeftRange(none), nullptr);
  EXPECT_EQ(VpiIoDeclRightRange(none), nullptr);
  EXPECT_EQ(VpiIoDeclLeftRange(none), VpiTypespecLeftRange(none));
  EXPECT_EQ(VpiIoDeclRightRange(none), VpiTypespecRightRange(none));
}

class ModportIoDeclsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle InInstance(const char* name) {
    std::string full = std::string("top.i0.") + name;
    return vpi_handle_by_name(full.data(), nullptr);
  }

  static vpiHandle IoDecl(const char* modport, const char* port) {
    vpiHandle iface = vpi_handle_by_name(VpiText("top.i0"), nullptr);
    return Named(vpiIODecl, Named(vpiModport, iface, modport), port);
  }

  static std::string Design(const std::string& items) {
    return "interface ifc; " + items +
           " endinterface\nmodule top; ifc i0(); endmodule\n";
  }
};

TEST_F(ModportIoDeclsOfARun, ASimplePortReachesTheVariableItNames) {
  Run(Design("logic a, b; modport mp(input a, output b);"));
  vpiHandle b = InInstance("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, IoDecl("mp", "b"))),
            VpiObjectOf(b));
}

TEST_F(ModportIoDeclsOfARun, ASimplePortReachesTheNetItNames) {
  Run(Design("wire w; modport mp(input w);"));
  vpiHandle w = InInstance("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, IoDecl("mp", "w"))),
            VpiObjectOf(w));
}

TEST_F(ModportIoDeclsOfARun, ARefPortReachesARefObj) {
  Run(Design("logic a; modport mr(ref a);"));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiExpr, IoDecl("mr", "a"))),
            vpiRefObj);
}

TEST_F(ModportIoDeclsOfARun, ARefPortsRefObjIsBoundToTheVariable) {
  Run(Design("logic a; modport mr(ref a);"));
  vpiHandle a = InInstance("a");
  ASSERT_NE(a, nullptr);
  vpiHandle ref_obj = vpi_handle(vpiExpr, IoDecl("mr", "a"));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiActual, ref_obj)), VpiObjectOf(a));
}

TEST_F(ModportIoDeclsOfARun, AnExpressionPortReachesItsExpression) {
  Run(Design("logic [7:0] r; modport mp(output .lo(r[3:0]));"));
  vpiHandle lo = vpi_handle(vpiExpr, IoDecl("mp", "lo"));
  EXPECT_EQ(vpi_get(vpiType, lo), vpiPartSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, lo)),
            VpiObjectOf(InInstance("r")));
}

TEST_F(ModportIoDeclsOfARun, AnEmptyExpressionPortReachesNone) {
  Run(Design("logic [7:0] r; modport mp(output .lo());"));
  vpiHandle lo = IoDecl("mp", "lo");
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, lo), nullptr);
}

class IoDeclsOfARun : public ModportIoDeclsOfARun {
 protected:
  static vpiHandle ArgOf(const char* tf, const char* arg) {
    return Named(vpiIODecl, Named(vpiTaskFunc, By("top"), tf), arg);
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(IoDeclsOfARun, AnArgumentsIoDeclReportsTheVariableItDeclares) {
  Run("module top;\n"
      "  task automatic t(input logic signed [7:0] a, input logic b,\n"
      "                   input int c[2], ref int r);\n"
      "  endtask\n"
      "endmodule\n");
  vpiHandle a = ArgOf("t", "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, a), 8);
  EXPECT_EQ(vpi_get(vpiSigned, a), 1);
  EXPECT_EQ(vpi_get(vpiScalar, a), 0);
  EXPECT_EQ(vpi_get(vpiVector, a), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, a)), 7);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, a)), 0);
  EXPECT_EQ(ObjectsOf(vpiRange, a).size(), 1U);
  vpiHandle a_var = vpi_handle(vpiExpr, a);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, a)),
            VpiObjectOf(vpi_handle(vpiTypespec, a_var)));
  vpiHandle b = ArgOf("t", "b");
  EXPECT_EQ(vpi_get(vpiSize, b), 1);
  EXPECT_EQ(vpi_get(vpiScalar, b), 1);
  EXPECT_EQ(vpi_get(vpiSigned, b), 0);
  EXPECT_NE(ArgOf("t", "c"), nullptr);
  vpiHandle r = ArgOf("t", "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, r), vpiRef);
  vpiHandle ref_obj = vpi_handle(vpiExpr, r);
  EXPECT_EQ(vpi_get(vpiType, ref_obj), vpiRefObj);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiActual, ref_obj)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiSize, r), 32);
}

TEST_F(IoDeclsOfARun, AVirtualInterfaceIoDeclHasNoDirection) {
  Run("interface inner; endinterface\n"
      "module top; inner n();\n"
      "  task t(virtual inner w); endtask\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiDirection, ArgOf("t", "w")), vpiNoDirection);
}

TEST_F(IoDeclsOfARun, AUdpDefnReachesAnIoDeclPerPort) {
  Run("primitive my_and(o, a, b);\n"
      "  output o;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 ? : 0;\n"
      "    ? 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire o; my_and u1(o, 1'b1, 1'b0); endmodule\n");
  vpiHandle udp = ObjectsOf(vpiPrimitive, By("top")).front();
  vpiHandle defn = vpi_handle(vpiUdpDefn, udp);
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, defn),
            (std::vector<std::string>{"a", "b", "o"}));
  vpiHandle o = Named(vpiIODecl, defn, "o");
  EXPECT_EQ(vpi_get(vpiDirection, o), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, defn, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiSize, o), 1);
  EXPECT_EQ(vpi_get(vpiScalar, o), 1);
  EXPECT_EQ(vpi_handle(vpiExpr, o), nullptr);
}

TEST_F(IoDeclsOfARun, AModportsSubroutineIoDeclReachesAnInterfaceTfDecl) {
  Run("interface ifc; logic a;\n"
      "  extern task put();\n"
      "  task get(); endtask\n"
      "  modport mp(input a, import get, export put);\n"
      "endinterface\n"
      "module tgt(ifc.mp b); task b.put(); endtask endmodule\n"
      "module top; ifc i0(); tgt t(i0.mp); endmodule\n");
  vpiHandle put = vpi_handle(vpiExpr, IoDecl("mp", "put"));
  ASSERT_NE(put, nullptr);
  EXPECT_EQ(vpi_get(vpiType, put), vpiInterfaceTfDecl);
  EXPECT_EQ(VpiObjectOf(put),
            VpiObjectOf(Named(vpiInterfaceTfDecl, By("top.i0"), "put")));
  vpiHandle get = vpi_handle(vpiExpr, IoDecl("mp", "get"));
  ASSERT_NE(get, nullptr);
  EXPECT_EQ(vpi_get(vpiType, get), vpiInterfaceTfDecl);
  EXPECT_EQ(vpi_get(vpiAccessType, get), vpiExternAcc);
  EXPECT_STREQ(vpi_get_str(vpiFullName, vpi_handle(vpiTask, get)),
               "top.i0.get");
}

}  // namespace
}  // namespace delta

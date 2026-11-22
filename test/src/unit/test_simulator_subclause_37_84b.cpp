#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct FrameUse {
  int calls = 0;
  int iterator_type = 0;
  int use_is_frame = 0;
};

FrameUse g_frame_use;

PLI_INT32 LookAtFrameUseCalltf(PLI_BYTE8*) {
  ++g_frame_use.calls;
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  vpiHandle iter =
      frame == nullptr ? nullptr : vpi_iterate(vpiAutomatics, frame);
  if (iter == nullptr) return 0;
  g_frame_use.iterator_type = vpi_get(vpiIteratorType, iter);
  g_frame_use.use_is_frame =
      vpi_compare_objects(vpi_handle(vpiUse, iter), frame);
  return 0;
}

class IteratorReference : public VpiDesignRun {
 protected:
  static void ExpectUseIsTheReference(int type, vpiHandle ref) {
    ASSERT_NE(ref, nullptr) << type;
    vpiHandle iter = vpi_iterate(type, ref);
    ASSERT_NE(iter, nullptr) << type;
    EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator) << type;
    EXPECT_EQ(vpi_get(vpiIteratorType, iter), type) << type;
    EXPECT_EQ(vpi_compare_objects(vpi_handle(vpiUse, iter), ref), 1) << type;
  }

  static void ExpectUseIsNull(int type) {
    vpiHandle iter = vpi_iterate(type, nullptr);
    ASSERT_NE(iter, nullptr) << type;
    EXPECT_EQ(vpi_get(vpiIteratorType, iter), type) << type;
    EXPECT_EQ(vpi_handle(vpiUse, iter), nullptr) << type;
  }

  static vpiHandle Watched(vpiHandle obj) {
    if (obj == nullptr) return nullptr;
    s_cb_data cb = {};
    cb.reason = cbValueChange;
    cb.obj = obj;
    return vpi_register_cb(&cb) == nullptr ? nullptr : obj;
  }

  static vpiHandle FirstOf(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

TEST_F(IteratorReference, EachDesignWideWalkAnswersUseWithNull) {
  Run("module top; initial #5 $noop; endmodule\n");
  ExpectUseIsNull(vpiModule);
  ExpectUseIsNull(vpiUserSystf);
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  ExpectUseIsNull(vpiCallback);
}

TEST_F(IteratorReference, TheTimeQueueWalkAnswersUseWithNull) {
  vpi_.SetTimeQueueSlots({{10, false, false}, {20, false, false}});
  ExpectUseIsNull(vpiTimeQueue);
  vpiHandle slot = FirstOf(vpiTimeQueue, nullptr);
  ExpectUseIsTheReference(vpiCallback, Watched(slot));
}

TEST_F(IteratorReference, InstanceKindsAnswerUseWithTheirReference) {
  Run("module sub; wire w; endmodule\n"
      "interface ifc; logic l; endinterface\n"
      "program pg; int k; endprogram\n"
      "module top;\n"
      "  sub u(); sub ua[1:0](); ifc i0(); pg p0();\n"
      "endmodule\n");
  ExpectUseIsTheReference(vpiModule, By("top"));
  ExpectUseIsTheReference(vpiNet, By("top.u"));
  ExpectUseIsTheReference(vpiVariables, By("top.i0"));
  ExpectUseIsTheReference(vpiVariables, By("top.p0"));
  ExpectUseIsTheReference(vpiModule, Named(vpiModuleArray, By("top"), "ua"));
}

TEST_F(IteratorReference, DeclarationKindsAnswerUseWithTheirReference) {
  Run("module top;\n"
      "  wire [3:0] w; assign w = 4'd3;\n"
      "  wire na[2];\n"
      "  logic [3:0] v;\n"
      "  logic va[2];\n"
      "  event ea[2];\n"
      "endmodule\n");
  ExpectUseIsTheReference(vpiRange, By("top.w"));
  ExpectUseIsTheReference(vpiDriver, By("top.w"));
  ExpectUseIsTheReference(vpiNet, By("top.na"));
  ExpectUseIsTheReference(vpiRange, By("top.v"));
  ExpectUseIsTheReference(vpiReg, By("top.va"));
  ExpectUseIsTheReference(vpiNamedEvent, By("top.ea"));
}

TEST_F(IteratorReference, StructuralKindsAnswerUseWithTheirReference) {
  Run("primitive u_or(output y, input a, b);\n"
      "  table 1 ? : 1; ? 1 : 1; 0 0 : 0; endtable\n"
      "endprimitive\n"
      "module top(input a, d, clk, output y);\n"
      "  wire g, h;\n"
      "  and g0 (g, a, d);\n"
      "  u_or g1 (h, a, d);\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "    $setup(d, posedge clk, 2);\n"
      "  endspecify\n"
      "  assign y = a;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle gate = FirstOf(vpiPrimitive, top);
  ExpectUseIsTheReference(vpiPrimTerm, gate);
  ExpectUseIsTheReference(vpiCallback, Watched(FirstOf(vpiPrimTerm, gate)));
  vpiHandle udp = nullptr;
  for (vpiHandle prim : ObjectsOf(vpiPrimitive, top)) {
    if (vpi_get(vpiType, prim) == vpiUdp) udp = prim;
  }
  ASSERT_NE(udp, nullptr);
  ExpectUseIsTheReference(vpiTableEntry, vpi_handle(vpiUdpDefn, udp));
  vpiHandle path = FirstOf(vpiModPath, top);
  ExpectUseIsTheReference(vpiModPathIn, path);
  ExpectUseIsTheReference(vpiTchkTerm, FirstOf(vpiTchk, top));
}

TEST_F(IteratorReference, DelayTermsAnswerUseWithTheirReference) {
  Run("module m(input a, output y);\n"
      "  wire z; buf g(y, a); assign z = y;\n"
      "  specify (a => y) = 3; endspecify\n"
      "endmodule\n"
      "module top; wire p, q; m u(p, q); endmodule\n");
  vpiHandle in_term = nullptr;
  for (vpiHandle load : ObjectsOf(vpiLoad, By("top.u.y"))) {
    if (vpi_get(vpiType, load) == vpiDelayTerm) in_term = load;
  }
  ASSERT_NE(in_term, nullptr);
  vpiHandle device = vpi_handle(vpiDelayDevice, in_term);
  ASSERT_NE(device, nullptr);
  ExpectUseIsTheReference(vpiDriver, vpi_handle(vpiInTerm, device));
  ExpectUseIsTheReference(vpiLoad, vpi_handle(vpiOutTerm, device));
}

TEST_F(IteratorReference, AnInterModPathAnswersUseWithItself) {
  VpiObject out_port;
  out_port.type = vpiPort;
  VpiObject in_port;
  in_port.type = vpiPort;
  VpiObject path;
  path.type = vpiInterModPath;
  path.children = {&out_port, &in_port};
  ExpectUseIsTheReference(vpiPort, VpiHandleOf(&path));
}

TEST_F(IteratorReference, ProceduralKindsAnswerUseWithTheirReference) {
  Run("module top;\n"
      "  logic [3:0] a, b; int r;\n"
      "  function int f(int x, int y); return x + y; endfunction\n"
      "  (* p_attr *) initial begin\n"
      "    r = f(1, 2);\n"
      "    case (a) 4'd1, 4'd2: r = 0; default: r = 1; endcase\n"
      "    r = a + b;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle process = FirstOf(vpiProcess, By("top"));
  ASSERT_NE(process, nullptr);
  vpiHandle block = vpi_handle(vpiStmt, process);
  ExpectUseIsTheReference(vpiAttribute, process);
  ExpectUseIsTheReference(vpiStmt, block);
  vpiHandle call = nullptr;
  vpiHandle case_stmt = nullptr;
  vpiHandle sum = nullptr;
  for (vpiHandle stmt : ObjectsOf(vpiStmt, block)) {
    if (vpi_get(vpiType, stmt) == vpiCase) case_stmt = stmt;
    if (vpi_get(vpiType, stmt) != vpiAssignment) continue;
    vpiHandle rhs = vpi_handle(vpiRhs, stmt);
    if (vpi_get(vpiType, rhs) == vpiFuncCall) call = rhs;
    if (vpi_get(vpiType, rhs) == vpiOperation) sum = rhs;
  }
  ExpectUseIsTheReference(vpiArgument, call);
  ExpectUseIsTheReference(vpiOperand, sum);
  ExpectUseIsTheReference(vpiCaseItem, case_stmt);
  ExpectUseIsTheReference(vpiExpr, FirstOf(vpiCaseItem, case_stmt));
  ExpectUseIsTheReference(vpiUse, FirstOf(vpiOperand, sum));
}

TEST_F(IteratorReference, AFrameAnswersUseWithItself) {
  g_frame_use = {};
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$frame_use");
  data.calltf = &LookAtFrameUseCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top;\n"
      "  task automatic t(input int x); int y; y = x; $frame_use; endtask\n"
      "  initial t(3);\n"
      "endmodule\n");
  EXPECT_EQ(g_frame_use.calls, 1);
  EXPECT_EQ(g_frame_use.iterator_type, vpiAutomatics);
  EXPECT_EQ(g_frame_use.use_is_frame, 1);
}

TEST_F(IteratorReference, DISABLED_AnIoDeclIsTheReferenceItsIteratorAnswers) {
  Run("module top(input [3:0] a); endmodule\n");
  vpiHandle io = FirstOf(vpiIODecl, By("top"));
  ExpectUseIsTheReference(vpiRange, io);
}

}  // namespace
}  // namespace delta

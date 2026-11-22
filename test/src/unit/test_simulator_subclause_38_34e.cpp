#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "helpers_vpi_put_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct ObjectPutResults {
  std::vector<int> read_at_once;
  std::vector<PLI_INT32> errors;
  std::vector<std::string> released;
  std::vector<vpiHandle> returned;
};

ObjectPutResults results;

std::string BitsOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiBinStrVal;
  vpi_get_value(obj, &value);
  return value.value.str == nullptr ? "" : value.value.str;
}

vpiHandle Handle(const char* name) {
  return vpi_handle_by_name(VpiText(name), nullptr);
}

void PutScalar(vpiHandle obj, PLI_INT32 scalar, int flags = vpiNoDelay,
               uint32_t delay = 0) {
  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = scalar;
  s_vpi_time time = {vpiSimTime, 0, delay, 0.0};
  vpi_put_value(obj, &val, &time, flags);
}

void RecordErrorOfPut(vpiHandle obj, s_vpi_value val, int flags) {
  vpi_put_value(obj, &val, nullptr, flags);
  const PLI_INT32 kError = vpi_chk_error(nullptr);
  results.errors.push_back(kError);
}

class ObjectPutsOfARun : public VpiPutRun {
 protected:
  void SetUp() override {
    VpiPutRun::SetUp();
    results = {};
  }

  static std::string BitsAt(const char* name) { return BitsOf(By(name)); }

  static std::vector<PLI_INT32> Errors(size_t count) {
    return std::vector<PLI_INT32>(count, vpiError);
  }
};

constexpr const char* kLatch =
    "primitive latch_udp(q, d, en);\n"
    "  output reg q; input d, en;\n"
    "  initial q = 0;\n"
    "  table\n"
    "    0 1 : ? : 0;\n"
    "    1 1 : ? : 1;\n"
    "    ? 0 : ? : -;\n"
    "  endtable\n"
    "endprimitive\n";

TEST_F(ObjectPutsOfARun, ASequentialUdpWithADelayTakesANoDelayPutAtOnce) {
  Putter() = [] {
    vpiHandle udp = vpi_handle_by_name(VpiText("top.u1"), nullptr);
    PutScalar(udp, vpi1);
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(udp, &value);
    results.read_at_once.push_back(value.value.integer);
    results.read_at_once.push_back(IntOf("top.q"));
  };
  Run(std::string(kLatch) +
      "module top; wire q; logic d = 0, en = 0;\n"
      "  latch_udp #5 u1(q, d, en);\n"
      "  initial #10 $put;\n"
      "endmodule\n");
  EXPECT_EQ(results.read_at_once, (std::vector<int>{1, 1}));
}

TEST_F(ObjectPutsOfARun, AScaledDelayOnANetIsInItsModulesUnit) {
  Putter() = [] {
    s_vpi_value val = {};
    val.format = vpiScalarVal;
    val.value.scalar = vpi1;
    s_vpi_time time = {vpiScaledRealTime, 0, 0, 2.0};
    vpi_put_value(Handle("top.c.w"), &val, &time, vpiInertialDelay);
  };
  Run("module child; timeunit 10ns; timeprecision 1ns; wire w; endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns; time at = 0;\n"
      "  child c();\n"
      "  always @(c.w) at = $time;\n"
      "  initial #5 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.at"), 25);
}

void PutOneAfterAScaledDelayOfTwo(std::initializer_list<const char*> names) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 1;
  s_vpi_time time = {vpiScaledRealTime, 0, 0, 2.0};
  for (const char* name : names) {
    vpi_put_value(Handle(name), &val, &time, vpiInertialDelay);
  }
}

TEST_F(ObjectPutsOfARun, AScaledDelayIsInTheUnitOfAnInterfaceOrProgram) {
  Putter() = [] { PutOneAfterAScaledDelayOfTwo({"top.i.v", "top.pg.v"}); };
  Run("interface ifc; timeunit 10ns; timeprecision 1ns; int v; endinterface\n"
      "program prg; timeunit 10ns; timeprecision 1ns; int v; endprogram\n"
      "module top; timeunit 1ns; timeprecision 1ns; time ai = 0, ag = 0;\n"
      "  ifc i(); prg pg();\n"
      "  always @(i.v) ai = $time;\n"
      "  always @(pg.v) ag = $time;\n"
      "  initial #5 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.ai"), 25);
  EXPECT_EQ(IntOf("top.ag"), 25);
}

TEST_F(ObjectPutsOfARun,
       DISABLED_AScaledDelayIsInTheUnitOfAPackageOrTheCompilationUnit) {
  Putter() = [] { PutOneAfterAScaledDelayOfTwo({"p::v", "$unit::u"}); };
  Run("timeunit 10ns; timeprecision 1ns;\n"
      "int u;\n"
      "package p; timeunit 10ns; timeprecision 1ns; int v; endpackage\n"
      "module top; timeunit 1ns; timeprecision 1ns; time ap = 0, au = 0;\n"
      "  always @(p::v) ap = $time;\n"
      "  always @(u) au = $time;\n"
      "  initial #5 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.ap"), 25);
  EXPECT_EQ(IntOf("top.au"), 25);
}

TEST_F(ObjectPutsOfARun, AStrengthPutToAScalarSetsItsLogicValue) {
  Run("module top; logic s = 0; initial $noop; endmodule\n");
  s_vpi_strengthval strength = {vpi1, vpiStrongDrive, vpiStrongDrive};
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  val.value.strength = &strength;
  vpi_put_value(By("top.s"), &val, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf("top.s"), 1);
}

TEST_F(ObjectPutsOfARun, AStringPutToAShortrealOrRealtimeIsRefused) {
  Run("module top; shortreal s = 1.5; realtime t = 2.5; initial $noop;\n"
      "endmodule\n");
  s_vpi_value text = {};
  text.format = vpiStringVal;
  text.value.str = VpiText("3");
  RecordErrorOfPut(By("top.s"), text, vpiNoDelay);
  RecordErrorOfPut(By("top.t"), text, vpiNoDelay);
  EXPECT_EQ(results.errors, Errors(2));
  s_vpi_value real = {};
  real.format = vpiRealVal;
  vpi_get_value(By("top.s"), &real);
  EXPECT_DOUBLE_EQ(real.value.real, 1.5);
  vpi_get_value(By("top.t"), &real);
  EXPECT_DOUBLE_EQ(real.value.real, 2.5);
}

TEST_F(ObjectPutsOfARun,
       DISABLED_AStrengthPutToAVectorNetOrOneBitRangeIsRefused) {
  Run("module top; wire [7:0] w; logic [0:0] v = 0; initial $noop;\n"
      "endmodule\n");
  s_vpi_strengthval strength = {vpi1, vpiStrongDrive, vpiStrongDrive};
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  val.value.strength = &strength;
  RecordErrorOfPut(By("top.w"), val, vpiNoDelay);
  RecordErrorOfPut(By("top.v"), val, vpiNoDelay);
  EXPECT_EQ(results.errors, Errors(2));
  EXPECT_EQ(BitsAt("top.v"), "0");
}

TEST_F(ObjectPutsOfARun, APutToANetBitOverridesOnlyThatBitUntilADriverChanges) {
  Putter() = [] {
    PutScalar(Handle("top.w[2]"), vpi1);
    PutScalar(Handle("top.w[1]"), vpi1, vpiInertialDelay, 1);
    PutScalar(Handle("top.w[0]"), vpi1, vpiTransportDelay, 1);
    PutScalar(Handle("top.p[1]"), vpi1, vpiPureTransportDelay, 1);
  };
  Run("module top; logic [3:0] d = 0; wire [3:0] w = d, p = d;\n"
      "  logic [3:0] w_at3, p_at3;\n"
      "  initial begin #1 $put; #2 w_at3 = w; p_at3 = p; #1 d = 4'b1000; end\n"
      "endmodule\n");
  EXPECT_EQ(BitsAt("top.w_at3"), "0111");
  EXPECT_EQ(BitsAt("top.p_at3"), "0010");
  EXPECT_EQ(BitsAt("top.w"), "1000");
  EXPECT_EQ(BitsAt("top.p"), "1000");
}

TEST_F(ObjectPutsOfARun, ADelayedPutToANetOverridesItUntilADriverChanges) {
  Putter() = [] {
    PutInt("top.a", 5, vpiInertialDelay, 1);
    PutInt("top.b", 6, vpiTransportDelay, 1);
    PutInt("top.c", 7, vpiPureTransportDelay, 1);
  };
  Run("module top; logic [7:0] d = 1; wire [7:0] a = d, b = d, c = d;\n"
      "  logic [7:0] a3, b3, c3;\n"
      "  initial begin #1 $put; #2 a3 = a; b3 = b; c3 = c; #1 d = 2; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.a3"), 5);
  EXPECT_EQ(IntOf("top.b3"), 6);
  EXPECT_EQ(IntOf("top.c3"), 7);
  EXPECT_EQ(IntOf("top.a"), 2);
  EXPECT_EQ(IntOf("top.b"), 2);
  EXPECT_EQ(IntOf("top.c"), 2);
}

TEST_F(ObjectPutsOfARun, ANetOverrideHoldsAcrossStepsWithoutADriverChange) {
  Putter() = [] { PutInt("top.w", 9, vpiNoDelay); };
  Run("module top; logic [7:0] d = 3, e = 0; wire [7:0] w = d;\n"
      "  logic [7:0] w_at4;\n"
      "  initial begin #1 $put; #1 e = 1; #1 e = 2; #1 w_at4 = w; #1 d = 4; "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.w_at4"), 9);
  EXPECT_EQ(IntOf("top.w"), 4);
}

TEST_F(ObjectPutsOfARun, DISABLED_AForceOnANetBitOrPartHoldsOnlyThoseBits) {
  Putter() = [] {
    PutScalar(Handle("top.w[6]"), vpi1, vpiForceFlag);
    s_vpi_value part = {};
    part.format = vpiBinStrVal;
    part.value.str = VpiText("11");
    vpi_put_value(Handle("top.w[5:4]"), &part, nullptr, vpiForceFlag);
  };
  Run("module top; logic [7:0] d = 0; wire [7:0] w = d;\n"
      "  initial begin #1 $put; #1 d = 8'h01; end\n"
      "endmodule\n");
  EXPECT_EQ(BitsAt("top.w"), "00110011");
}

TEST_F(ObjectPutsOfARun, DISABLED_AForceOnAVariableSelectIsRefused) {
  Putter() = [] {
    s_vpi_value zero = {};
    zero.format = vpiIntVal;
    RecordErrorOfPut(Handle("top.v[4]"), zero, vpiForceFlag);
    RecordErrorOfPut(Handle("top.v[3:2]"), zero, vpiForceFlag);
    results.read_at_once.push_back(IntOf("top.v"));
  };
  Run("module top; logic [7:0] v = 8'h0F;\n"
      "  initial begin #1 $put; #1 v = 8'hF0; end\n"
      "endmodule\n");
  EXPECT_EQ(results.errors, Errors(2));
  EXPECT_EQ(results.read_at_once, (std::vector<int>{0x0F}));
  EXPECT_EQ(IntOf("top.v"), 0xF0);
}

TEST_F(ObjectPutsOfARun, AForceOnAnUnpackedArrayOrStructureIsRefused) {
  Run("module top; int a [2]; struct { int x; int y [2]; } s;\n"
      "  union { int x; } u; initial $noop;\n"
      "endmodule\n");
  s_vpi_value one = {};
  one.format = vpiIntVal;
  one.value.integer = 1;
  RecordErrorOfPut(By("top.a"), one, vpiForceFlag);
  RecordErrorOfPut(By("top.s"), one, vpiForceFlag);
  RecordErrorOfPut(By("top.u"), one, vpiForceFlag);
  RecordErrorOfPut(Handle("top.s.y"), one, vpiForceFlag);
  EXPECT_EQ(results.errors, Errors(4));
  RecordErrorOfPut(Handle("top.s.x"), one, vpiForceFlag);
  EXPECT_EQ(results.errors.back(), 0);
  EXPECT_EQ(IntOf("top.s.x"), 1);
}

TEST_F(ObjectPutsOfARun, AForceOrReleaseWithADelayActsAtOnce) {
  Putter() = [] {
    results.read_at_once.push_back(IntOf("top.w"));
    results.returned.push_back(PutInt("top.w", 6, vpiForceFlag, 3));
    results.read_at_once.push_back(IntOf("top.w"));
    s_vpi_time time = {vpiSimTime, 0, 3, 0.0};
    s_vpi_value out = {};
    out.format = vpiIntVal;
    vpi_put_value(Handle("top.w"), &out, &time, vpiReleaseFlag);
    results.read_at_once.push_back(out.value.integer);
    results.read_at_once.push_back(IntOf("top.w"));
  };
  Run("module top; logic [7:0] d = 2; wire [7:0] w = d;\n"
      "  logic [7:0] w_at5;\n"
      "  initial begin #1 $put; #4 w_at5 = w; end\n"
      "endmodule\n");
  EXPECT_EQ(results.read_at_once, (std::vector<int>{2, 6, 2, 2}));
  EXPECT_EQ(results.returned, (std::vector<vpiHandle>{nullptr}));
  EXPECT_EQ(IntOf("top.w_at5"), 2);
}

TEST_F(ObjectPutsOfARun, AMemoryWordTakesTheValuePut) {
  Putter() = [] {
    s_vpi_value val = {};
    val.format = vpiIntVal;
    val.value.integer = 7;
    vpi_put_value(vpi_handle_by_index(Handle("top.m"), 2), &val, nullptr,
                  vpiNoDelay);
  };
  Run("module top; int m [4]; int x;\n"
      "  initial begin #1 $put; #1 x = m[2]; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.x"), 7);
}

TEST_F(ObjectPutsOfARun, ABitOfABuiltInNetTakesThePut) {
  Run("module top; wire [3:0] w; initial $noop; endmodule\n");
  s_vpi_value one = {};
  one.format = vpiScalarVal;
  one.value.scalar = vpi1;
  RecordErrorOfPut(Handle("top.w[0]"), one, vpiNoDelay);
  EXPECT_EQ(results.errors, (std::vector<PLI_INT32>{0}));
  EXPECT_EQ(BitsAt("top.w"), "zzz1");
}

TEST_F(ObjectPutsOfARun, AGateASwitchOrACombinationalUdpRefusesAPut) {
  Run("primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; wire a, b, c, d; logic i = 0;\n"
      "  and g(a, i, i); tran s(b, c); inv u(d, i);\n"
      "endmodule\n");
  s_vpi_value one = {};
  one.format = vpiScalarVal;
  one.value.scalar = vpi1;
  for (const char* name : {"g", "s", "u"}) {
    vpiHandle prim = Named(vpiPrimitive, By("top"), name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_put_value(prim, &one, nullptr, vpiNoDelay), nullptr);
    const PLI_INT32 kError = vpi_chk_error(nullptr);
    results.errors.push_back(kError);
  }
  EXPECT_EQ(results.errors, Errors(3));
}

TEST_F(ObjectPutsOfARun,
       DISABLED_AReleasedAssignedVariableTakesItsAssignmentAtOnce) {
  Putter() = [] {
    static int calls = 0;
    if (calls++ % 2 == 0) {
      PutInt("top.v", 9, vpiForceFlag);
      return;
    }
    s_vpi_time time = {vpiSimTime, 0, 3, 0.0};
    s_vpi_value out = {};
    out.format = vpiIntVal;
    vpi_put_value(Handle("top.v"), &out, &time, vpiReleaseFlag);
    results.read_at_once.push_back(out.value.integer);
    results.read_at_once.push_back(IntOf("top.v"));
  };
  Run("module top; logic [7:0] d = 3, v; assign v = d;\n"
      "  initial begin #1 $put; #1 $put; end\n"
      "endmodule\n");
  EXPECT_EQ(results.read_at_once, (std::vector<int>{3, 3}));
}

TEST_F(ObjectPutsOfARun, AReleaseReportsTheValueInTheFormatAsked) {
  Putter() = [] {
    for (const PLI_INT32 kFormat :
         {vpiBinStrVal, vpiVectorVal, vpiTimeVal, vpiStrengthVal}) {
      const char* name = kFormat == vpiStrengthVal ? "top.s" : "top.w";
      PutInt(name, 0, vpiForceFlag);
      s_vpi_value out = {};
      out.format = kFormat;
      vpi_put_value(Handle(name), &out, nullptr, vpiReleaseFlag);
      if (kFormat == vpiBinStrVal) {
        results.released.emplace_back(out.value.str);
      } else if (kFormat == vpiVectorVal) {
        results.released.push_back(std::to_string(out.value.vector->aval) +
                                   "/" +
                                   std::to_string(out.value.vector->bval));
      } else if (kFormat == vpiTimeVal) {
        results.released.push_back(std::to_string(out.value.time->low));
      } else {
        results.released.push_back(std::to_string(out.value.strength->logic));
      }
    }
  };
  Run("module top; logic [7:0] d = 5; logic e = 1; wire [7:0] w = d;\n"
      "  wire s = e;\n"
      "  initial #1 $put;\n"
      "endmodule\n");
  EXPECT_EQ(results.released, (std::vector<std::string>{"00000101", "5/0", "5",
                                                        std::to_string(vpi1)}));
}

}  // namespace
}  // namespace delta

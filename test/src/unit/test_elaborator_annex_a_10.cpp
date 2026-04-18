#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BnfClarificationElaboration, RefPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(ref int x);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, InoutPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(inout wire a);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TimeunitDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TimeprecisionDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TimeunitAndPrecisionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, ParameterInClassIsLocalparam) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(BnfClarificationElaboration, AutomaticInInitialBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, StructPackedWithDimOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [7:0] b;\n"
             "  } my_t;\n"
             "  my_t data;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TypeRefWithWireOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire x;\n"
             "  wire type(x) y;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TypeRefWithVarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  var type(x) y;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, ReplicationWithConstantOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] x;\n"
             "  assign x = {4{2'b01}};\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, EmptyUnpackedArrayConcatOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {};\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, DollarInQueueSelectOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q[$] = 5;\n"
             "endmodule\n"));
}

// Item 8: final_specifier illegal on pure virtual method

TEST(BnfClarificationElaboration, FinalOnPureVirtualError) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class c;\n"
      "  pure virtual function void do_it() final;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Item 7: parameter in class treated as localparam (cannot override)

TEST(BnfClarificationElaboration, ParameterInClassNoOverride) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = A + 1;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// Item 16: charge strength only with trireg

TEST(BnfClarificationElaboration, ChargeStrengthWithTriregOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  trireg (small) x;\n"
             "endmodule\n"));
}

}  // namespace

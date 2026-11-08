#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

bool ElaboratesWithBlockLocalIn(const std::string& stmt) {
  return ElabOk("module m;\n  int r;\n  initial\n    " + stmt +
                "\nendmodule\n");
}

TEST(NetsAndVariables, BlockLocalReadInAnAssertionPassStmtIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn("assert (r) begin int a; r = a; end"));
}

TEST(NetsAndVariables, BlockLocalReadInAnAssertionFailStmtIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("assert (r) else begin int a; r = a; end"));
}

TEST(NetsAndVariables, BlockLocalReadInARandcaseItemIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "randcase 1: begin int a; r = a; end endcase"));
}

TEST(NetsAndVariables, BlockLocalReadInARandsequenceCodeBlockIsAccepted) {
  EXPECT_TRUE(
      ElaboratesWithBlockLocalIn("begin\n"
                                 "      randsequence(main)\n"
                                 "        main : { begin int a; r = a; end };\n"
                                 "      endsequence\n"
                                 "    end"));
}

TEST(NetsAndVariables, BlockLocalReadInARandsequenceWeightCodeBlockIsAccepted) {
  EXPECT_TRUE(ElaboratesWithBlockLocalIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin int a; r = a; end };\n"
      "        alt : { r = 1; };\n"
      "      endsequence\n"
      "    end"));
}

TEST(NetsAndVariables,
     MemberQualifiedProceduralTargetIsAWriteToItsBaseVariable) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic f; } s_t;\n"
      "  s_t v;\n"
      "  logic a, b;\n"
      "  assign v = a;\n"
      "  initial v.f = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
}

TEST(NetsAndVariables, PackageScopedAssignmentIsNotAWriteToThePrefixName) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  wire p;\n"
             "  logic a;\n"
             "  assign p = a;\n"
             "  initial p::x = 1;\n"
             "endmodule\n",
             f));
}

TEST(NetsAndVariables, UntypedOutputPortIsANetAProcedureCannotWrite) {
  ElabFixture f;
  Elaborate(
      "module top(input clk, input a, output b, output c);\n"
      "  clocking ck1 @(posedge clk);\n"
      "    default input #10ns output #5ns;\n"
      "    input a;\n"
      "    output b;\n"
      "    output #3ns c;\n"
      "  endclocking\n"
      "  always_ff @(posedge clk) begin\n"
      "    b <= a;\n"
      "    c <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'b' cannot be the target of a procedural assignment", 9, "10.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'c' cannot be the target of a procedural assignment", 10, "10.4"));
}

TEST(NetsAndVariables, TypedOutputPortIsAVariableAProcedureMayWrite) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module top(input clk, input a, output logic b);\n"
             "  always_ff @(posedge clk) b <= a;\n"
             "endmodule\n",
             f));
}

TEST(NetsAndVariables, NetSelectTakesSeveralContinuousAssignments) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  wire [3:0] a;\n"
             "  wor r[2];\n"
             "  assign a[0] = 1'b1;\n"
             "  assign a[0] = 1'b0;\n"
             "  assign r[0] = 1'b0;\n"
             "  assign r[0] = 1'b1;\n"
             "endmodule\n",
             f));
}

TEST(NetsAndVariables, SubroutineWriteMeetsContinuousAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y, z;\n"
      "  task automatic t(); y = a; endtask\n"
      "  function automatic void g(output logic z); z = a; endfunction\n"
      "  always_comb t();\n"
      "  assign y = a;\n"
      "  assign z = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'y' has both continuous and procedural "
                            "assignments",
                            6, "6.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "variable 'z' has both continuous and procedural "
                             "assignments",
                             7, "6.5"));
}

TEST(NetsAndVariables, AGenerateBlocksVariableIsNotTheModulesOfThatName) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic w;\n"
      "  assign w = 1'b0;\n"
      "  if (1) begin : a\n"
      "    logic w;\n"
      "    assign w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables, EveryIterationAssigningTheModulesVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic w;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    assign w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'w'", 4,
                            "6.5"));
}

TEST(NetsAndVariables, AnIterationsVariableTakesNoMixtureOfAssignments) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    logic w;\n"
      "    assign w = 1'b0;\n"
      "    initial w = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'w' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "multiple continuous assignments to 'w'", 4,
                             "6.5"));
}

constexpr const char* kAbcExampleHead =
    "module m(input logic clk, input logic sel);\n"
    "  struct {\n"
    "    bit [7:0] A;\n"
    "    bit [7:0] B;\n"
    "    byte C;\n"
    "  } abc;\n"
    "  assign abc.C = sel ? 8'hBE : 8'hEF;\n"
    "  not (abc.A[0], abc.B[0]),\n"
    "      (abc.A[1], abc.B[1]),\n"
    "      (abc.A[2], abc.B[2]),\n"
    "      (abc.A[3], abc.B[3]);\n"
    "  always @(posedge clk) abc.B <= abc.B + 1;\n";

TEST(NetsAndVariables, SectionsStructExampleIsAccepted) {
  EXPECT_TRUE(ElabOk(std::string(kAbcExampleHead) + "endmodule\n"));
}

TEST(NetsAndVariables, SectionsStructExampleAdditionsAreReported) {
  ElabFixture second;
  ElabOk(std::string(kAbcExampleHead) +
             "  assign abc.C = sel ? 8'hDE : 8'hED;\n"
             "endmodule\n",
         second);
  EXPECT_TRUE(ReportedError(
      second.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'abc.C'", 13,
      "6.5"));
  ElabFixture mixed;
  ElabOk(std::string(kAbcExampleHead) +
             "  always @(posedge clk) abc.A[7:3] <= !abc.B[7:3];\n"
             "endmodule\n",
         mixed);
  EXPECT_TRUE(ReportedError(mixed.diag.Diagnostics(),
                            "element 'abc.A[3]' has both a continuous "
                            "assignment and a procedural assignment",
                            8, "10.3.2"));
  EXPECT_FALSE(ReportedError(mixed.diag.Diagnostics(),
                             "element 'abc.A[2]' has both a continuous "
                             "assignment and a procedural assignment",
                             8, "10.3.2"));
}

constexpr const char* kInverterUdp =
    "primitive inv(output o, input i);\n"
    "  table\n"
    "    0 : 1;\n"
    "    1 : 0;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(NetsAndVariables, UdpOutputIsAContinuousWriterOfAVariable) {
  ElabFixture whole;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a, w;\n"
             "  inv u(w, a);\n"
             "  initial w = 1'b0;\n"
             "endmodule\n",
         whole);
  EXPECT_TRUE(ReportedError(whole.diag.Diagnostics(),
                            "variable 'w' has both continuous and procedural "
                            "assignments",
                            9, "6.5"));
  ElabFixture twice;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a, w;\n"
             "  inv u1(w, a);\n"
             "  inv u2(w, a);\n"
             "endmodule\n",
         twice);
  EXPECT_TRUE(ReportedError(twice.diag.Diagnostics(),
                            "variable 'w' is driven by more than one "
                            "continuous assignment or primitive output",
                            10, "10.3.2"));
  ElabFixture bit;
  ElabOk(std::string(kInverterUdp) +
             "module m;\n"
             "  logic a;\n"
             "  logic [1:0] v;\n"
             "  inv u(v[0], a);\n"
             "  initial v[0] = 1'b0;\n"
             "endmodule\n",
         bit);
  EXPECT_TRUE(ReportedError(bit.diag.Diagnostics(),
                            "element 'v[0]' has both a continuous assignment "
                            "and a procedural assignment",
                            10, "10.3.2"));
  EXPECT_TRUE(ElabOk(std::string(kInverterUdp) + "module m;\n"
                                                 "  logic a;\n"
                                                 "  logic [1:0] v;\n"
                                                 "  inv u(v[0], a);\n"
                                                 "  initial v[1] = 1'b0;\n"
                                                 "endmodule\n"));
}

TEST(NetsAndVariables, ProceduralAssignIsAProceduralWriter) {
  ElabFixture module_level;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  initial assign v = a;\n"
      "  assign v = b;\n"
      "endmodule\n",
      module_level);
  EXPECT_TRUE(ReportedError(module_level.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            4, "6.5"));
  ElabFixture generated;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  assign v = b;\n"
      "  if (1) begin : g\n"
      "    initial assign v = a;\n"
      "  end\n"
      "endmodule\n",
      generated);
  EXPECT_TRUE(ReportedError(generated.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            5, "6.5"));
  ElabFixture in_task;
  ElabOk(
      "module m;\n"
      "  logic a, b, v;\n"
      "  task t;\n"
      "    assign v = a;\n"
      "  endtask\n"
      "  assign v = b;\n"
      "endmodule\n",
      in_task);
  EXPECT_TRUE(ReportedError(in_task.diag.Diagnostics(),
                            "variable 'v' has both continuous and procedural "
                            "assignments",
                            6, "6.5"));
  ElabFixture member;
  ElabOk(
      "module m;\n"
      "  struct packed { logic p; logic q; } s;\n"
      "  assign s.p = 1'b0;\n"
      "  initial assign s = 2'b00;\n"
      "endmodule\n",
      member);
  EXPECT_TRUE(ReportedError(member.diag.Diagnostics(),
                            "element 's.p' has both a continuous assignment "
                            "and a procedural assignment",
                            3, "10.3.2"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, v;\n"
             "  initial assign v = a;\n"
             "endmodule\n"));
}

TEST(NetsAndVariables, ForceIsNoWriterUnderTheRule) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, v;\n"
             "  assign v = b;\n"
             "  initial force v = a;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic b;\n"
             "  logic [1:0] v;\n"
             "  assign v[0] = b;\n"
             "  initial force v = 2'b00;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, v;\n"
             "  initial begin\n"
             "    v = 1'b0;\n"
             "    assign v = a;\n"
             "    force v = a;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace

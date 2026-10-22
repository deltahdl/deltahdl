#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §10.4: the left-hand side of a procedural assignment shall be a variable.
// Positive anchor — a variable LHS is accepted, confirming the net-target check
// does not reject legitimate variable targets.
TEST(ProceduralAssignmentElaboration, VariableLhsIsAccepted) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    v = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §10.4 requires that the left-hand side of a procedural assignment be a
// variable, and admits four forms for it: a singular variable (§6.4), an
// aggregate variable (Clause 7), a bit-select, part-select or slice of a packed
// array, and a slice of an unpacked array. A net is none of the four, so the
// report cites §10.4. §6.5 says that a net cannot be procedurally assigned, but
// says it as what follows for a net from the requirement §10.4 places on the
// assignment, so it is not the citation however the check is written -- this
// one reads the module's net names, which is a mechanism and not the rule.
TEST(ProceduralAssignmentElaboration, ProceduralAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, NonblockingAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, SelectOfNetBaseIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  initial begin\n"
      "    w[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

TEST(ProceduralAssignmentElaboration, ConcatenationContainingNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    {v, w} = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            5, "10.4"));
}

// §10.4 with §23.2.2.1 (printed pages 731 and 732): a non-ANSI port declared
// with no net or variable type, which the body never declares again, is a net,
// so a procedural assignment to it is reported as one to a declared net is.
TEST(ProceduralAssignmentElaboration, AssignToUndeclaredNonAnsiPortIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t(q);\n"
      "  output q;\n"
      "  initial begin\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
}

// §23.2.2.1: the body declaring that port again as a variable makes it one, and
// a variable takes the procedural assignment.
TEST(ProceduralAssignmentElaboration, AssignToNonAnsiPortDeclaredAVariable) {
  SimFixture f;
  ElaborateSrc(
      "module t(q);\n"
      "  output q;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §10.4 holds wherever the procedural assignment stands: in a task, in a
// function and in a process of a generate block.
TEST(ProceduralAssignmentElaboration, NetTargetInSubroutineOrGenerateIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  if (1) begin : g initial w = 1; end\n"
      "  task tk; w = 0; endtask\n"
      "  function void fn(); w = 0; endfunction\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "cannot be the target of a procedural assignment",
                              line, "10.4"));
  }
}

// §23.9: a block's own variable, a subroutine's formal and a loop's variable
// are what an assignment within their scope names, even where a module net
// has the same name.
TEST(ProceduralAssignmentElaboration, LocalNameShadowingNetIsAccepted) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w, k;\n"
      "  initial begin logic w; w = 1; end\n"
      "  task tk(output logic w); w = 0; endtask\n"
      "  initial for (int k = 0; k < 2; k++) k = k;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "cannot be the target of a procedural assignment"),
            nullptr);
}

// Syntax 10-2 (printed page 252): only the expression form of a blocking
// assignment takes an intra-assignment delay or event control, and the forms
// that assign a dynamic array's or a class's new take none.
TEST(ProceduralAssignmentElaboration, TimingControlOnAssignmentOfNewIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class C; endclass\n"
      "  int d[]; C c; logic clk; int x;\n"
      "  initial d = #1 new[4];\n"
      "  initial c = @(posedge clk) new;\n"
      "  initial x = #1 3;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an assignment of 'new' takes no "
                              "intra-assignment delay or event control",
                              line, "10.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "an assignment of 'new' takes no "
                             "intra-assignment delay or event control",
                             6, "10.4"));
}

// §6.19 makes the names an enumeration declares named constants, and Syntax
// 10-2 writes the target of a blocking or nonblocking assignment as a
// variable_lvalue, which a constant is not. An assignment to one is reported,
// whole or as an element of a concatenation, and the variable `q` is not.
TEST(ProceduralAssignmentElaboration,
     AssignmentOfAnEnumerationConstantIsError) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    A = B;\n"
      "    B <= A;\n"
      "    {q, A} = 2;\n"
      "    q = A;\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<const char*, uint32_t> kReports[] = {
      {"A", 5}, {"B", 6}, {"A", 7}};
  for (const auto& [name, line] : kReports) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("assignment of constant '{}', which is not a variable",
                    name),
        line, "10.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "of constant", 8, "10.4"));
}

}  // namespace

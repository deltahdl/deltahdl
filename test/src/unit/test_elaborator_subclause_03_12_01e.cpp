#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A source and the line of the report it should draw.
struct Written {
  const char* src;
  uint32_t line;
};

constexpr const char* kUnitNetInit =
    "a net declaration with an implicit continuous assignment cannot stand in "
    "the compilation-unit scope";

// Whether elaborating `src` draws `message` at `line` under `subclause`.
::testing::AssertionResult ElabReports(const std::string& src,
                                       const char* message, uint32_t line,
                                       const char* subclause) {
  ElabFixture f;
  ElabOk(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, subclause);
}

// §3.12.1 (printed page 56) gives the compilation-unit scope the items a
// package may hold, and §26.2 (printed 807) keeps a net declaration with an
// implicit continuous assignment out of a package, which holds no process. So
// the unit holds none either, whatever the net type, the delay or the drive
// strength written with the assignment.
TEST(UnitNetDeclarationAssignment, EachNetTypeWithAnAssignment) {
  const char* const kDecls[] = {
      "wire w = 1'b1;",    "tri w = 1'b1;",
      "wand w = 1'b1;",    "wor w = 1'b1;",
      "triand w = 1'b1;",  "trior w = 1'b1;",
      "tri0 w = 1'b1;",    "tri1 w = 1'b1;",
      "supply0 w = 1'b0;", "supply1 w = 1'b1;",
      "trireg w = 1'b1;",  "uwire w = 1'b1;",
      "wire #5 w = 1'b1;", "wire (strong0, weak1) w = 1'b1;",
  };
  for (const char* decl : kDecls) {
    EXPECT_TRUE(ElabReports(std::string(decl) + "\nmodule m; endmodule\n",
                            kUnitNetInit, 1, "3.12.1"))
        << decl;
  }
}

// A net of a user-defined nettype (§6.6.7) is a net, so its initializer is
// the same implicit continuous assignment.
TEST(UnitNetDeclarationAssignment, NettypeNetWithAnAssignment) {
  EXPECT_TRUE(
      ElabReports("nettype logic [3:0] n4;\n"
                  "n4 w = 4'd5;\n"
                  "module m; endmodule\n",
                  kUnitNetInit, 2, "3.12.1"));
}

// Of two nets declared together, the one written with an assignment is
// reported, and the other is not.
TEST(UnitNetDeclarationAssignment, OnlyTheAssignedNetOfTwo) {
  ElabFixture f;
  ElabOk(
      "wire a,\n"
      "     b = 1'b1;\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnitNetInit, 2, "3.12.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kUnitNetInit, 1, "3.12.1"));
}

// The nearest allowed forms: the unit's net without an assignment, the unit's
// variable with a declaration assignment, which §26.2 lets a package hold, and
// the net declaration assignment in a module, an interface, a program and a
// generate block, which hold continuous assignments.
TEST(UnitNetDeclarationAssignment, TheNearestAllowedForms) {
  EXPECT_TRUE(
      ElabOk("wire w;\n"
             "logic v = 1'b1;\n"
             "interface i;\n"
             "  wire wi = 1'b1;\n"
             "endinterface\n"
             "program p;\n"
             "  wire wp = 1'b1;\n"
             "endprogram\n"
             "module m;\n"
             "  wire wm = 1'b1;\n"
             "  if (1) begin : g\n"
             "    wire wg = 1'b1;\n"
             "  end\n"
             "  i ui();\n"
             "  p up();\n"
             "endmodule\n"));
}

// §3.12.1 (printed page 56): a name a module does not declare reaches the
// net the compilation unit declares before it, so the reference names a net,
// which §6.5 lets more than one continuous assignment or primitive output
// drive, whatever its net type, written in a module, an interface, a program
// or a generate block.
TEST(UnitNetReference, SeveralDriversOfTheUnitsNet) {
  const char* const kNetTypes[] = {"wire",  "tri",  "wand", "wor",   "triand",
                                   "trior", "tri0", "tri1", "trireg"};
  for (const char* type : kNetTypes) {
    EXPECT_TRUE(ElabOk(std::string(type) + " w;\n"
                                           "module m;\n"
                                           "  logic a, b;\n"
                                           "  assign w = a;\n"
                                           "  assign w = b;\n"
                                           "endmodule\n"))
        << type;
  }
  EXPECT_TRUE(
      ElabOk("wand w;\n"
             "interface i;\n"
             "  logic a, b;\n"
             "  assign w = a;\n"
             "  assign w = b;\n"
             "endinterface\n"
             "program p;\n"
             "  logic a, b;\n"
             "  assign w = a;\n"
             "  assign w = b;\n"
             "endprogram\n"
             "module m;\n"
             "  logic a, b, c, d;\n"
             "  if (1) begin : g\n"
             "    assign w = a;\n"
             "    assign w = b;\n"
             "  end\n"
             "  buf g1 (w, c);\n"
             "  buf g2 (w, d);\n"
             "  i ui();\n"
             "  p up();\n"
             "endmodule\n"));
}

// The nearest forms the rule reports: the unit's variable, which a module's
// two continuous assignments, or two primitive outputs, drive.
TEST(UnitNetReference, SeveralDriversOfTheUnitsVariable) {
  EXPECT_TRUE(
      ElabReports("logic v;\n"
                  "module m;\n"
                  "  logic a, b;\n"
                  "  assign v = a;\n"
                  "  assign v = b;\n"
                  "endmodule\n",
                  "multiple continuous assignments to 'v'", 5, "6.5"));
  EXPECT_TRUE(ElabReports(
      "logic v;\n"
      "module m;\n"
      "  logic a, b;\n"
      "  buf g1 (v, a);\n"
      "  buf g2 (v, b);\n"
      "endmodule\n",
      "variable 'v' is driven by more than one continuous assignment or "
      "primitive output",
      5, "10.3.2"));
}

// §6.6.2: the unit's uwire takes one driver, so a module's second continuous
// assignment to it is reported as the uwire's; one assignment is accepted.
TEST(UnitNetReference, TheUnitsUwire) {
  EXPECT_TRUE(
      ElabReports("uwire w;\n"
                  "module m;\n"
                  "  logic a, b;\n"
                  "  assign w = a;\n"
                  "  assign w = b;\n"
                  "endmodule\n",
                  "uwire 'w' cannot have multiple drivers", 5, "6.6.2"));
  EXPECT_TRUE(
      ElabOk("uwire w;\n"
             "module m;\n"
             "  logic a;\n"
             "  assign w = a;\n"
             "endmodule\n"));
}

// §10.4: a procedural assignment writes a variable, and the unit's net is
// none, wherever the assignment stands: each kind of procedure of a module, a
// task and a function, a nonblocking assignment, an interface's and a
// program's initial procedure, and a module's generate block.
TEST(UnitNetReference, ProceduralAssignmentToTheUnitsNet) {
  const char* const kMessage = "net 'w' cannot be the target of a procedural";
  const Written kCases[] = {
      {"wire w;\n"
       "module m;\n"
       "  initial w = 1'b1;\n"
       "endmodule\n",
       3},
      {"wire w;\n"
       "module m;\n"
       "  initial w <= 1'b1;\n"
       "endmodule\n",
       3},
      {"wire w;\n"
       "module m;\n"
       "  logic a;\n"
       "  always @(a) w = a;\n"
       "endmodule\n",
       4},
      {"wire w;\n"
       "module m;\n"
       "  logic a;\n"
       "  always_comb w = a;\n"
       "endmodule\n",
       4},
      {"wire w;\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  always_ff @(posedge clk) w <= a;\n"
       "endmodule\n",
       4},
      {"wire w;\n"
       "module m;\n"
       "  final w = 1'b1;\n"
       "endmodule\n",
       3},
      {"wire w;\n"
       "module m;\n"
       "  task t();\n"
       "    w = 1'b1;\n"
       "  endtask\n"
       "endmodule\n",
       4},
      {"wire w;\n"
       "module m;\n"
       "  function void f();\n"
       "    w = 1'b1;\n"
       "  endfunction\n"
       "endmodule\n",
       4},
      {"wire w;\n"
       "interface i;\n"
       "  initial w = 1'b1;\n"
       "endinterface\n"
       "module m;\n"
       "  i ui();\n"
       "endmodule\n",
       3},
      {"wire w;\n"
       "program p;\n"
       "  initial w = 1'b1;\n"
       "endprogram\n"
       "module m;\n"
       "  p up();\n"
       "endmodule\n",
       3},
      {"wire w;\n"
       "module m;\n"
       "  if (1) begin : g\n"
       "    initial w = 1'b1;\n"
       "  end\n"
       "endmodule\n",
       4},
  };
  for (const Written& c : kCases) {
    EXPECT_TRUE(ElabReports(c.src, kMessage, c.line, "10.4")) << c.src;
  }
}

// The nearest allowed forms: the unit's variable written procedurally in each
// of those places, and a module's own variable or output port of the net's
// name, which the module's procedure writes rather than the unit's net.
TEST(UnitNetReference, ProceduralAssignmentToTheUnitsVariable) {
  EXPECT_TRUE(
      ElabOk("logic v;\n"
             "interface i;\n"
             "  initial v = 1'b1;\n"
             "endinterface\n"
             "program p;\n"
             "  initial v = 1'b1;\n"
             "endprogram\n"
             "module m;\n"
             "  logic a;\n"
             "  initial v = 1'b1;\n"
             "  always @(a) v <= a;\n"
             "  task t();\n"
             "    v = 1'b1;\n"
             "  endtask\n"
             "  if (1) begin : g\n"
             "    initial v = 1'b0;\n"
             "  end\n"
             "  i ui();\n"
             "  p up();\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("wire w;\n"
             "module m;\n"
             "  logic w;\n"
             "  initial w = 1'b1;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("wire w;\n"
             "module m(output logic w);\n"
             "  initial w = 1'b1;\n"
             "endmodule\n"));
}

// §10.6.1: a procedural continuous assignment and a deassign take a variable,
// and the unit's net is none; the unit's variable is accepted.
TEST(UnitNetReference, AssignAndDeassignOfTheUnitsNet) {
  const char* const kMessage =
      "net 'w' cannot be the target of a procedural assign or deassign";
  EXPECT_TRUE(
      ElabReports("wire w;\n"
                  "module m;\n"
                  "  initial assign w = 1'b1;\n"
                  "endmodule\n",
                  kMessage, 3, "10.6.1"));
  EXPECT_TRUE(
      ElabReports("wire w;\n"
                  "module m;\n"
                  "  initial deassign w;\n"
                  "endmodule\n",
                  kMessage, 3, "10.6.1"));
  EXPECT_TRUE(
      ElabOk("logic v;\n"
             "module m;\n"
             "  initial begin\n"
             "    assign v = 1'b1;\n"
             "    deassign v;\n"
             "  end\n"
             "endmodule\n"));
}

// §11.4.14.3: a streaming concatenation written as a continuous assignment's
// target unpacks into variables, and the unit's net is none; the unit's
// variable is accepted.
TEST(UnitNetReference, StreamingTargetNamingTheUnitsNet) {
  EXPECT_TRUE(
      ElabReports("wire [7:0] w;\n"
                  "module m;\n"
                  "  logic [7:0] a;\n"
                  "  assign {>>{w}} = a;\n"
                  "endmodule\n",
                  "unpacks into variables, and 'w' is a net", 4, "11.4.14.3"));
  EXPECT_TRUE(
      ElabOk("logic [7:0] v;\n"
             "module m;\n"
             "  logic [7:0] a;\n"
             "  assign {>>{v}} = a;\n"
             "endmodule\n"));
}

// §10.6.2: a force may name a constant bit-select of a vector net, and of the
// unit's net as of the module's own; a select of a variable, the unit's
// variable among them, and a select of a net by a variable index are reported.
TEST(UnitNetReference, ForceOfASelectOfTheUnitsNet) {
  EXPECT_TRUE(
      ElabOk("wire [3:0] w;\n"
             "module m;\n"
             "  initial force w[0] = 1'b1;\n"
             "endmodule\n"));
  EXPECT_TRUE(ElabReports(
      "logic [3:0] v;\n"
      "module m;\n"
      "  initial force v[0] = 1'b1;\n"
      "endmodule\n",
      "bit-select or part-select of a variable is not a legal force LHS", 3,
      "10.6.2"));
  EXPECT_TRUE(ElabReports(
      "wire [3:0] w;\n"
      "module m;\n"
      "  int i;\n"
      "  initial force w[i] = 1'b1;\n"
      "endmodule\n",
      "bit-select or part-select of a net in a force LHS must be constant", 4,
      "10.6.2"));
}

}  // namespace

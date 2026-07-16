#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// IEEE 1800-2023 §9.4.2.2 "Implicit event_expression list".
//
// The implicit event control @* / @(*) is shorthand for an event_expression
// built from every net and variable READ by the process body. The subclause's
// "shall" sentence enumerates the read positions that must be included: the
// right-hand side of assignments, arguments of subroutine calls, case and
// conditional selector expressions, index variables on the left-hand side of
// an assignment, and case-item expressions. It also excludes identifiers that
// appear only as the lvalue of an assignment (i.e. that are written but never
// read).
//
// These tests exercise that rule where it ultimately takes effect: at run time.
// A process built from real `always @*` source is elaborated (the elaborator's
// InferSensitivity computes the list) and lowered, then driven by a testbench
// that changes one signal at a later time step. If that signal is in the
// implied list the process re-executes and the observed output changes; if the
// signal is excluded the process stays asleep and the output is unchanged. Each
// test therefore observes production code applying the rule end to end, rather
// than restating the classification in the test itself.

using namespace delta;

namespace {

uint64_t RunAndReadVar(SimFixture& f, const std::string& src,
                       const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  if (!design) return ~0ull;
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable(var_name);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : ~0ull;
}

// "shall ... include ... the right-hand side of assignments": changing an RHS
// operand after the initial settle must re-trigger the block. If `a` were not
// in the implied list, y would keep its t=0 value 0x03 instead of 0x12.
TEST(ImplicitSensitivitySim, WakesOnRhsOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = a + b;\n"
                             "  initial begin\n"
                             "    a = 8'h01; b = 8'h02;\n"
                             "    #5 a = 8'h10;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x12u);
}

// Each RHS operand is independently in the implied list: changing the other
// operand `b` (with `a` held constant) must likewise re-trigger the block.
TEST(ImplicitSensitivitySim, WakesOnSecondRhsOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = a + b;\n"
                             "  initial begin\n"
                             "    a = 8'h20; b = 8'h01;\n"
                             "    #5 b = 8'h05;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x25u);
}

// "shall ... include ... subroutine calls": an argument passed to a called
// function is read, so a change to it re-triggers the block.
TEST(ImplicitSensitivitySim, WakesOnSubroutineArgChange) {
  SimFixture f;
  uint64_t y =
      RunAndReadVar(f,
                    "module t;\n"
                    "  function logic [7:0] dbl(input logic [7:0] v);\n"
                    "    return v << 1;\n"
                    "  endfunction\n"
                    "  logic [7:0] a, y;\n"
                    "  always @* y = dbl(a);\n"
                    "  initial begin\n"
                    "    a = 8'h03;\n"
                    "    #5 a = 8'h05;\n"
                    "    #5 $finish;\n"
                    "  end\n"
                    "endmodule\n",
                    "y");
  EXPECT_EQ(y, 0x0Au);
}

// "shall ... include ... case ... expressions": the case selector is read even
// though it never appears on the RHS of an assignment.
TEST(ImplicitSensitivitySim, WakesOnCaseSelectorChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [1:0] sel;\n"
                             "  logic [7:0] y;\n"
                             "  always @*\n"
                             "    case (sel)\n"
                             "      2'b00: y = 8'h10;\n"
                             "      2'b01: y = 8'h20;\n"
                             "      default: y = 8'hFF;\n"
                             "    endcase\n"
                             "  initial begin\n"
                             "    sel = 2'b00;\n"
                             "    #5 sel = 2'b01;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x20u);
}

// "shall ... include ... case item expressions": a variable appearing only in
// a case-item label (the reverse-case idiom `case (1'b1) sig[k]:`) is read, so
// a change to it re-triggers. Here `state` is never on an RHS and is not the
// case selector (which is the constant 1'b1); it drives the block solely
// through the item labels. If it were left out of the implied list, y would
// keep its first value 0x11 instead of updating to 0x33.
TEST(ImplicitSensitivitySim, WakesOnCaseItemExprChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [3:0] state;\n"
                             "  logic [7:0] y;\n"
                             "  always @*\n"
                             "    case (1'b1)\n"
                             "      state[0]: y = 8'h11;\n"
                             "      state[1]: y = 8'h22;\n"
                             "      state[2]: y = 8'h33;\n"
                             "      default:  y = 8'hFF;\n"
                             "    endcase\n"
                             "  initial begin\n"
                             "    state = 4'b0001;\n"
                             "    #5 state = 4'b0100;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0x33u);
}

// "shall ... include ... conditional expressions": the `?:` selector is read.
// sel appears only in the condition, never as an assignment RHS operand.
TEST(ImplicitSensitivitySim, WakesOnConditionalSelectorChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic sel;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @* y = sel ? a : b;\n"
                             "  initial begin\n"
                             "    a = 8'hAA; b = 8'hBB; sel = 1'b0;\n"
                             "    #5 sel = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xAAu);
}

// "shall ... include ... an index variable on the left-hand side of
// assignments": idx is read (to pick the target bit) even though it appears on
// the LHS. A change to idx re-triggers, setting a second bit; y[0] set by the
// first pass survives because only the selected bit is written.
TEST(ImplicitSensitivitySim, WakesOnLhsIndexChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [1:0] idx;\n"
                             "  logic v;\n"
                             "  logic [3:0] y;\n"
                             "  always @* y[idx] = v;\n"
                             "  initial begin\n"
                             "    y = 4'b0000; v = 1'b1; idx = 2'd0;\n"
                             "    #5 idx = 2'd2;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0b0101u);
}

// "adding all nets and variables that are read": nets are admitted alongside
// variables. The wire w is driven by a continuous assignment (§10.3); when its
// value changes the @* block re-triggers. Built from real source and run end to
// end — the net's value is produced by the assign, not hand-set. If nets were
// excluded from the implied list, y would keep its t=0 value 0.
TEST(ImplicitSensitivitySim, WakesOnNetOperandChange) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic a;\n"
                             "  wire w;\n"
                             "  logic y;\n"
                             "  assign w = a;\n"
                             "  always @* y = w;\n"
                             "  initial begin\n"
                             "    a = 1'b0;\n"
                             "    #5 a = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 1u);
}

// §9.4.2.2 applies @* to a procedural timing-control statement, not only to a
// module `always @*`. The standalone `@*` here (LRM Example 4's inner form)
// builds its implicit list from the statement it controls -- {c} for `x = c` --
// and suspends until c changes. c holds its declared value 0 until #5, so the
// initial process parks on the @* and only assigns x once c toggles: x observed
// == 1 proves the procedural @* waited on the implied signal rather than
// falling straight through.
TEST(ImplicitSensitivitySim, ProceduralStarWaitsOnImpliedRead) {
  SimFixture f;
  uint64_t x = RunAndReadVar(f,
                             "module t;\n"
                             "  logic c = 1'b0;\n"
                             "  logic x = 1'b0;\n"
                             "  initial begin\n"
                             "    @* x = c;\n"
                             "  end\n"
                             "  initial begin\n"
                             "    #5 c = 1'b1;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "x");
  EXPECT_EQ(x, 1u);
}

// Exclusion: an identifier that appears only as the lvalue of an assignment
// (written, never read) is NOT in the implied list. Here y is pure-LHS, so an
// external write to y must not wake the block. If y were (wrongly) in the list,
// the block would re-run y = a and overwrite 0xFF back to 0x05.
TEST(ImplicitSensitivitySim, DoesNotWakeOnPureLhsWrite) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, y;\n"
                             "  always @* y = a;\n"
                             "  initial begin\n"
                             "    a = 8'h05;\n"
                             "    #5 y = 8'hFF;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xFFu);
}

// The parenthesized form @(*) yields the identical implied list at run time:
// changing the read operand a re-triggers the block just as with @*.
TEST(ImplicitSensitivitySim, ParenFormWakesLikeStar) {
  SimFixture f;
  uint64_t y = RunAndReadVar(f,
                             "module t;\n"
                             "  logic [7:0] a, b, y;\n"
                             "  always @(*) y = a | b;\n"
                             "  initial begin\n"
                             "    a = 8'h00; b = 8'h0F;\n"
                             "    #5 a = 8'hF0;\n"
                             "    #5 $finish;\n"
                             "  end\n"
                             "endmodule\n",
                             "y");
  EXPECT_EQ(y, 0xFFu);
}

}  // namespace

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/net_data_type.h"
#include "elaborator/simple_bit_vector.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(DollarConstantElaboration, DollarBodyParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DollarConstantElaboration, DollarPortListParameterSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter int P = $);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.7: $ may be assigned to a value parameter of a simple bit vector type
// (§6.11.1). This drives that dependency's real syntax — an explicitly declared
// packed logic vector — through parse+elaborate and observes the parameter
// being flagged unbounded.
TEST(DollarConstantElaboration, DollarSimpleBitVectorTypeParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter logic [7:0] P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.7: a parameter assigned $ may be used anywhere a literal $ is allowed.
// This mirrors the clause's own example — the unbounded parameter supplies the
// upper bound of a sequence cycle-delay range — and confirms the parameter is
// flagged unbounded and is accepted in that context without error.
TEST(DollarConstantElaboration, DollarParameterUsableAsUnboundedRangeBound) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter r1 = 1;\n"
      "  parameter r2 = $;\n"
      "  logic clk, a, b, c;\n"
      "  property inq1;\n"
      "    @(posedge clk) a ##[r1:r2] b |=> c;\n"
      "  endproperty\n"
      "  assert property (inq1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_r2 = false;
  for (auto& p : mod->params) {
    if (p.name == "r2") {
      found_r2 = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_r2);
}

TEST(DollarConstantElaboration, BoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

// §6.20.7: assigning a $ parameter to another parameter is legal, and the
// assigned-to parameter is itself unbounded.
TEST(DollarConstantElaboration, DollarParameterAssignedToAnotherIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

// The same propagation applies when the chain appears in a parameter port list,
// where a later parameter can depend on an earlier one.
TEST(DollarConstantElaboration, DollarPortListParameterChainIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter Q = $, parameter P = Q);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

// A parameter assigned a bounded parameter is not unbounded.
TEST(DollarConstantElaboration, ParameterAssignedBoundedParameterNotUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter Q = 7;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_unbounded);
    }
  }
}

// §6.20.7: unboundedness propagates transitively along a chain of parameters,
// since each link is marked unbounded as it is elaborated.
TEST(DollarConstantElaboration, DollarParameterChainThreeDeepAllUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = $;\n"
      "  parameter B = A;\n"
      "  parameter C = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int seen = 0;
  for (auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") {
      ++seen;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_EQ(seen, 3);
}

// §6.20.7: the referenced unbounded constant may itself be a localparam (a
// §11.2.1 constant form) rather than a parameter; assigning it to a later
// parameter propagates unboundedness just as a parameter reference does.
TEST(DollarConstantElaboration,
     DollarLocalparamReferencedByParameterIsUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_p = false;
  for (auto& p : mod->params) {
    if (p.name == "Q") {
      EXPECT_TRUE(p.is_unbounded);
    }
    if (p.name == "P") {
      found_p = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found_p);
}

// §6.20.7: $ may be assigned to a value parameter; a localparam is a value
// parameter, so it too becomes unbounded when assigned $.
TEST(DollarConstantElaboration, DollarLocalparamSetsUnboundedFlag) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "P") {
      found = true;
      EXPECT_TRUE(p.is_unbounded);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.7: $ must be self-contained; combining it with an operator in a
// parameter value is illegal.
TEST(DollarConstantElaboration, NonSelfContainedDollarParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = $ + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            2, "6.20.7"));
}

// The same restriction holds for a parameter declared in a port list.
TEST(DollarConstantElaboration, NonSelfContainedDollarPortParameterIsError) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter int P = $ + 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$' may only be assigned to parameter 'P' as a "
                            "complete, self-contained expression",
                            1, "6.20.7"));
}

TEST(DollarConstantElaboration, DollarParameterNotResolved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_FALSE(p.is_resolved);
    }
  }
}

// §23.9 lists generate blocks among the elements that open a new scope, and
// rules that an identifier referenced directly, with no hierarchical path, is
// declared in its own scope or in a module, interface, program, checker, task,
// function, named block or generate block above it in the same branch of the
// name tree. Block 'a' is not higher in the module's own branch, so the P that
// block 'a' assigned $ is not what the module-level Q names, and the §6.20.7
// propagation this file's DollarParameterAssignedToAnotherIsUnbounded asserts
// does not reach it.
//
// The test fails when Q comes out unbounded. Elaborator::RefersToUnboundedParam
// in src/elaborator/elaborator_items_scope.cpp matches RtlirParamDecl::name,
// which Elaborator::ElaborateParamDecl writes bare whatever scope declared the
// parameter, so block 'a''s P answers for a reference anywhere in the module
// unless RtlirParamDecl::gen_block_prefix is consulted beside it.
TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockDoesNotMakeAModuleLevelParameterUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "    end\n"
      "  endgenerate\n"
      "  localparam Q = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q" || !p.gen_block_prefix.empty()) continue;
    found_q = true;
    EXPECT_FALSE(p.is_unbounded)
        << "block 'a' localparam P should not reach a module-level Q";
  }
  EXPECT_TRUE(found_q);
}

// The direction the scope test must not lose. §23.9 rules that an identifier
// declared in the scope itself is what a direct reference names, so block 'a''s
// own P is what block 'a''s Q names, and §6.20.7's propagation carries the
// unbounded flag across it exactly as this file's
// DollarParameterAssignedToAnotherIsUnbounded has it do at module level.
//
// The test fails when Q comes out bounded, which is what a check that dropped
// every parameter carrying a generate block prefix would produce.
TEST(DollarConstantElaboration,
     DollarParameterOfAGenerateBlockStillReachesThatBlocksParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam P = $;\n"
      "      localparam Q = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_q = false;
  for (auto& p : mod->params) {
    if (p.name != "Q") continue;
    found_q = true;
    EXPECT_TRUE(p.is_unbounded)
        << "block 'a' localparam P should reach block 'a' localparam Q";
  }
  EXPECT_TRUE(found_q);
}

// §6.20.7 (printed page 131) lets `$` be assigned to a value parameter of a
// simple bit vector type, and §8.25 gives a class's parameter port list the
// module rules. Each case fails on a registration that folds a class value
// parameter as an integer and reports the value when that fold fails, which is
// what rejected `class C #(int N = $)` while `parameter int i = $;` in a
// module was accepted.
TEST(DollarConstantElaboration, DollarClassParamDefaultIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = $);\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DollarConstantElaboration, DollarClassBodyLocalparamIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  localparam int N = $;\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

// An override assigns the parameter as a default does, so `$` is as legal
// there. §23.10.2's constant-expression rule is what reported it.
TEST(DollarConstantElaboration, DollarClassParamOverrideIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = 4);\n"
             "endclass\n"
             "module t;\n"
             "  C #($) c;\n"
             "  class D extends C #($);\n"
             "  endclass\n"
             "endmodule\n"));
}

// §6.20.7 lets a parameter holding `$` stand wherever `$` may be written as a
// literal, and an override is such a place, in a declaration and in an extends
// clause alike. The parameter's value is not in the scope the override is
// folded over, which is what reported `C #(P)` as not a constant expression.
TEST(DollarConstantElaboration, OverrideNamingADollarParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(int N = 4);\n"
             "endclass\n"
             "module t;\n"
             "  parameter int P = $;\n"
             "  C #(P) d;\n"
             "  class D extends C #(P);\n"
             "  endclass\n"
             "endmodule\n"));
}

// Each parameter of `params`, a line and a name, is reported as holding `$`
// though its type is no simple bit vector type.
template <size_t N>
void ExpectDollarTypeReported(
    const ElabFixture& f,
    const std::pair<uint32_t, std::string_view> (&params)[N]) {
  for (const auto& [line, name] : params) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'$' may be assigned only to a parameter of a simple bit "
                    "vector type, and parameter '{}' is not one",
                    name),
        line, "6.20.7"));
  }
}

// §6.20.7 lets `$` be assigned to a value parameter of a simple bit vector
// type, which §6.11.1 makes every integer type of Table 6-8 and a bit, logic or
// reg vector of one packed dimension, written directly or through a typedef. An
// untyped parameter takes its type from its value and is one too.
TEST(DollarConstantElaboration,
     DollarAssignedToEachSimpleBitVectorTypeIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef bit [7:0] octet_t;\n"
             "  parameter P0 = $;\n"
             "  parameter signed [3:0] P1 = $;\n"
             "  parameter logic [7:0] P2 = $;\n"
             "  parameter reg P3 = $;\n"
             "  parameter bit [3:0] P4 = $;\n"
             "  parameter byte P5 = $;\n"
             "  parameter shortint P6 = $;\n"
             "  parameter int P7 = $;\n"
             "  parameter longint P8 = $;\n"
             "  parameter integer P9 = $;\n"
             "  parameter time P10 = $;\n"
             "  parameter octet_t P11 = $;\n"
             "endmodule\n"));
}

// Every other parameter type refuses `$`: a non-integral type, an enumeration,
// a packed structure, a second packed dimension (written on the parameter or
// added to a typedef's), and an unpacked dimension, written on the parameter or
// carried by a typedef. A class name is no bit vector either.
TEST(DollarConstantElaboration,
     DollarAssignedToAnotherParameterTypeIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  typedef struct packed {bit a;} s_t;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef int i_t;\n"
      "  typedef bit a_t [2];\n"
      "  class C;\n"
      "  endclass\n"
      "  parameter real R = $;\n"
      "  parameter string S = $;\n"
      "  parameter e_t E = $;\n"
      "  parameter s_t T = $;\n"
      "  parameter bit [1:0][3:0] M = $;\n"
      "  parameter nib_t [1:0] N = $;\n"
      "  parameter i_t [1:0] I = $;\n"
      "  parameter int U [2] = $;\n"
      "  parameter a_t D = $;\n"
      "  parameter C H = $;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {9, "R"},  {10, "S"}, {11, "E"}, {12, "T"}, {13, "M"},
      {14, "N"}, {15, "I"}, {16, "U"}, {17, "D"}, {18, "H"}};
  ExpectDollarTypeReported(f, kParams);
}

// A parameter port is held to the same rule, and so is a parameter assigned a
// parameter whose value is `$`, since that assigns it `$` too (§6.20.7 gives
// `parameter P=Q;` as legal only where `$` itself would be).
TEST(DollarConstantElaboration,
     DollarPortOrDollarParameterOfAnotherTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter real R = $,\n"
      "           parameter int A [2] = $,\n"
      "           parameter W = $);\n"
      "  parameter real Q = W;\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kParams[] = {
      {1, "R"}, {2, "A"}, {4, "Q"}};
  ExpectDollarTypeReported(f, kParams);
}

// A type name the tables cannot resolve leaves nothing to judge, so the type
// is taken as a simple bit vector type and `$` is not reported against it; a
// class name resolving to no typedef is no bit vector all the same. A
// parameter with no declared type at all is judged by nothing either.
TEST(DollarConstantElaboration, UnresolvedOrAbsentTypeIsNotJudged) {
  const TypedefMap kTypedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>> kDims;
  const std::unordered_set<std::string_view> kClasses = {"C"};
  const TypeShapeTables kTables{kTypedefs, kDims, kClasses};
  DataType missing;
  missing.kind = DataTypeKind::kNamed;
  missing.type_name = "missing_t";
  EXPECT_TRUE(IsSimpleBitVectorType(missing, kTables));
  DataType handle;
  handle.kind = DataTypeKind::kNamed;
  handle.type_name = "C";
  EXPECT_FALSE(IsSimpleBitVectorType(handle, kTables));
  ElabFixture f;
  ValidateUnboundedParamType({"W", nullptr, false, {}}, kTables, f.diag);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.20.7 bars a parameter holding `$` from every queue context: a queue's
// bound, a dimension that would make a queue of it, and an index or a slice of
// a queue, in a module, a procedural block or a function alike. A dynamic,
// fixed or bounded dimension is no such context, nor is an index of a queue
// written with a bounded parameter, an index of an element of a queue of
// queues written with one, the compilation unit's `P` that `$unit::P` names,
// an index of an array that is no queue, or the bound of a value range.
TEST(DollarConstantElaboration, DollarParameterInAQueueContextIsRejected) {
  ElabFixture f;
  Elaborate(
      "parameter P = 1;\n"
      "module m;\n"
      "  parameter P = $;\n"
      "  parameter N = 2;\n"
      "  int q[$];\n"
      "  int b[$:P];\n"
      "  int c[P];\n"
      "  int d[];\n"
      "  int e[N];\n"
      "  int g[4];\n"
      "  int qq[$][$];\n"
      "  function automatic int f();\n"
      "    return q[P];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int lq[$:P];\n"
      "    q[P] = 1;\n"
      "    q = q[0:P-1];\n"
      "    q[$unit::P] = 1;\n"
      "    qq[0][N] = 1;\n"
      "    b[N] = 1;\n"
      "    g[N] = 1;\n"
      "    if (N inside {[0:P]}) g[0] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6U, 7U, 13U, 16U, 17U, 18U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameter 'P' holds '$', which a queue context "
                              "does not permit",
                              line, "6.20.7"));
  }
  for (uint32_t line : {19U, 20U, 21U, 22U, 23U}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), "holds '$'", line, "6.20.7"));
  }
}

// §6.20.7 lists the contexts `$` may be written in, and an ordinary operand is
// none of them: not a variable's or a net's initializer, a continuous or a
// procedural assignment's value, an operand of an operator, a condition or a
// function's return value. A queue select, with operators applied to `$` or
// without, a value range's bound and a call's arguments are left alone.
TEST(DollarConstantElaboration, DollarAsAnOrdinaryOperandIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  int x, y, q[$];\n"
      "  wire [7:0] w;\n"
      "  wire [7:0] v = $;\n"
      "  int z = $;\n"
      "  assign w = $;\n"
      "  function automatic int f();\n"
      "    return $;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = $;\n"
      "    y = $ + 1;\n"
      "    if (x == $) y = 0;\n"
      "    x = q[$];\n"
      "    y = q[$-1];\n"
      "    x = int'(y inside {[0:$]});\n"
      "    y = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "'$' may stand only in a queue's dimension or select, a value range's "
      "bound";
  for (uint32_t line : {4U, 5U, 6U, 8U, 11U, 12U, 13U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"));
  }
  for (uint32_t line : {14U, 15U, 16U, 17U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"));
  }
}

}  // namespace

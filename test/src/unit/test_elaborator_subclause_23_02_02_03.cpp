
#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

namespace {

TEST(PortKindDataTypeDirection, OmittedDirectionElaboratesToInout) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(wire x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(design->top_modules[0]->ports[0].width, 1u);
}

TEST(PortKindDataTypeDirection, OmittedTypeElaboratesAsLogicWidth1) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 1u);
}

TEST(PortKindDataTypeDirection, InheritedPortElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic [7:0] x, y);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  auto& py = design->top_modules[0]->ports[1];
  EXPECT_EQ(py.direction, Direction::kInput);
  EXPECT_EQ(py.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(py.width, 8u);
}

TEST(PortKindDataTypeDirection, OutputExplicitIntegerElaboratesWidth32) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output integer x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kInteger);
  EXPECT_EQ(port.width, 32u);
}

TEST(PortKindDataTypeDirection, SignedImplicitTypeElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output signed [5:0] x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 6u);
  EXPECT_TRUE(port.is_signed);
}

TEST(PortKindDataTypeDirection, ExplicitPortTakesExpressionDataType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input integer p_a, .p_b(s_b), p_c);\n"
      "  logic [5:0] s_b;\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  // §23.2.2.3: the explicitly named port p_b takes the self-determined data
  // type of its connection expression s_b, a 6-bit value declared in the body.
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].width, 6u);
}

TEST(PortKindDataTypeDirection, VarFirstPortDefaultedToInoutIsRejected) {
  // §23.2.2.3 (LRM example mh4): a first port declared only with var omits the
  // direction, which defaults to inout. An inout port may not carry a variable
  // data type, so applying the default-direction rule surfaces the error the
  // LRM documents for mh4. The rejection is observable only after elaboration.
  // The report is the §23.3.3.2 rule against a variable data type on an inout
  // port, emitted by DiagnosePortTypeConstraints in
  // src/elaborator/elaborator_module_ports.cpp once §23.2.2.3's default
  // direction has made this port an inout.
  ElabFixture f;
  ElaborateSrc("module m(var x); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable data type is not permitted on inout port "
                            "'x'",
                            1, "23.3.3.2"));
}

TEST(PortKindDataTypeDirection, FirstPortExplicitTypeElaboratesAsInoutNet) {
  // §23.2.2.3: an explicit data type on the first port with no direction
  // keyword still resolves to an inout port (direction default) that is a net
  // (inout port kind default), carrying the explicit type's width through
  // elaboration.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(integer x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.type_kind, DataTypeKind::kInteger);
  EXPECT_FALSE(port.is_var);
  EXPECT_EQ(port.width, 32u);
}

TEST(PortKindDataTypeDirection, InputOmittedKindElaboratesAsNet) {
  // §23.2.2.3: for an input port with the port kind omitted, the kind defaults
  // to a net; the elaborated port therefore is not a variable.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->ports[0].is_var);
}

TEST(PortKindDataTypeDirection, OutputImplicitTypeElaboratesAsNet) {
  // §23.2.2.3: an output port whose data type is left implicit (only a packed
  // range here) defaults its port kind to a net, so is_var is false.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_FALSE(port.is_var);
}

TEST(PortKindDataTypeDirection, OutputExplicitTypeElaboratesAsVariable) {
  // §23.2.2.3: an output port declared with an explicit data type defaults its
  // port kind to variable, so the elaborated port reports is_var.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output logic x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_TRUE(port.is_var);
}

TEST(PortKindDataTypeDirection, RefPortElaboratesAsVariable) {
  // §23.2.2.3: a ref port is always a variable, independent of its data type.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(ref [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_TRUE(port.is_var);
}

// §23.2.2.3 makes an input or inout with no port kind a net, and §6.7.1 gives
// a net only a 4-state integral type or an unpacked aggregate of such types,
// so `input string s`, `input real r` and `inout event e` each declare an
// illegal net and are reported at their own line, where `input var string v`
// declares a variable and is not. Only integral and aggregate types were
// judged, and none of the three was reported.
TEST(PortKindDataTypeDirection, ANetPortOfATypeNoNetCanHaveIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input string s,\n"
      "         input real r,\n"
      "         inout event e,\n"
      "         input var string v);\n"
      "endmodule\n",
      f, "m");
  for (uint32_t line : {1u, 2u, 3u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "net data type must be 4-state", line, "6.7.1"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "net data type must be 4-state", 4, "6.7.1"));
}

}  // namespace

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, BinaryWildcardEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryWildcardNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardEqOnClassHandles) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  C a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardNeqOnClassHandles) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  C a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardEqClassHandleWithNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  C a;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardNeqClassHandleWithNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  C a;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardEqOnInterfaceClassHandles) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  interface class IC;\n"
      "  endclass\n"
      "  IC a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardNeqOnInterfaceClassHandles) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  interface class IC;\n"
      "  endclass\n"
      "  IC a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardEqOnChandle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, WildcardNeqOnChandle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.6 states "The wildcard equality operator is equivalent to the logical
// equality operator if its operands are class handles, interface class handles,
// chandles or the literal null", so ==? on class handles is held to the rule
// §11.4.5 states for the logical equality operator: one operand shall be
// assignment compatible with the other. Handles of unrelated class types are
// not, so the comparison is rejected and the report names §11.4.5.
TEST(OperatorElaboration, WildcardEqIncompatibleClassHandlesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  class D;\n"
      "  endclass\n"
      "  C a;\n"
      "  D b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible", 9, "11.4.5"));
}

// Wildcard inequality is the other operator §11.4.6 makes equivalent to its
// logical counterpart, so it is rejected under §11.4.5 for the same reason.
TEST(OperatorElaboration, WildcardNeqIncompatibleClassHandlesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  class D;\n"
      "  endclass\n"
      "  C a;\n"
      "  D b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible", 9, "11.4.5"));
}

}  // namespace

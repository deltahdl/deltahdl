#include "fixture_elaborator.h"

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

// ==? is equivalent to == on class handles.
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

// !=? is equivalent to != on class handles.
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

// ==? with null on class handle.
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

// !=? with null on class handle.
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

// ==? on chandle operands.
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

// !=? on chandle operands.
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

}  // namespace

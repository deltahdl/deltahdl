#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModportExpressionElaboration, SamePortIdInDifferentModports) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "  modport B(output .P(r[7:4]));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, DuplicatePortIdInSameModportErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input .P(a), input .P(b));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration, ConstantPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(output .P(2));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration, ConstantPortExpressionWithInoutDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(inout .P(2));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration, ConstantPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  modport mp(input .P(2));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, HierarchicalAccessThroughModportSelectsBoundExpression) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "endinterface\n"
             "module child(I i);\n"
             "endmodule\n"
             "module top;\n"
             "  I inst();\n"
             "  child u(inst.A);\n"
             "endmodule\n"));
}

}  // namespace

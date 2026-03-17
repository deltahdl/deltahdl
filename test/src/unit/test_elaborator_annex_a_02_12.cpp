#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LetDeclElaboration, BasicLetDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclNoArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let val = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithDefaultsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let inc(x, step = 1) = x + step;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclUntypedArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let pass(untyped a) = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclTypedArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let mul(logic [15:0] x, logic [15:0] y) = x * y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, MultipleLetDeclsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "  let mul(a, b) = a * b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  let op(x, y) = x & y;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(LetDeclElaboration, LetDeclInInterfaceElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc;\n"
      "  let valid(req, ack) = req & ack;\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithComplexBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclInBlockItemElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  initial begin\n"
      "    let local_add(a, b) = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LetDeclElaboration, LetDeclWithAttributeElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  let f((* mark *) logic x) = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
